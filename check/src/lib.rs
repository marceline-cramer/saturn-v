// Copyright (C) 2025 Marceline Cramer
// SPDX-License-Identifier: AGPL-3.0-or-later
//
// Saturn V is free software: you can redistribute it and/or modify it under
// the terms of the GNU Affero General Public License as published by the Free
// Software Foundation, either version 3 of the License, or (at your option) any
// later version.
//
// Saturn V is distributed in the hope that it will be useful, but WITHOUT ANY
// WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
// FOR A PARTICULAR PURPOSE. See the GNU Affero General Public License for
// more details.
//
// You should have received a copy of the GNU Affero General Public License
// along with Saturn V. If not, see <https://www.gnu.org/licenses/>.

use saturn_v_ir::{BinaryOpKind, Expr, QueryTerm, Type, UnaryOpKind, Value};
use z3::{
    ast::{self, Ast},
    Context, FuncDecl, SortKind,
};

pub fn expr_to_z3<'a>(
    ctx: &'a Context,
    variables: &[(Type, ast::Dynamic<'a>)],
    relations: &[FuncDecl<'a>],
    expr: &Expr,
) -> Result<(Type, ast::Dynamic<'a>), Error> {
    match expr {
        Expr::Variable(idx) => variables
            .get(*idx as usize)
            .cloned()
            .ok_or(Error::InvalidVariableIndex(*idx)),
        Expr::Value(val) => Ok(value_to_z3(ctx, val)),
        Expr::Load { relation, query } => {
            let relation = relations
                .get(*relation as usize)
                .ok_or(Error::InvalidRelationIndex(*relation))?;

            let mut terms = Vec::with_capacity(query.len());
            for term in query.iter() {
                terms.push(match term {
                    QueryTerm::Variable(idx) => variables
                        .get(*idx as usize)
                        .cloned()
                        .ok_or(Error::InvalidVariableIndex(*idx))?,
                    QueryTerm::Value(val) => value_to_z3(ctx, val),
                });
            }

            let args: Vec<_> = terms.iter().map(|(_ty, term)| term as _).collect();
            Ok((Type::Boolean, relation.apply(args.as_slice())))
        }
        Expr::UnaryOp { op, term } => {
            let (ty, term) = expr_to_z3(ctx, variables, relations, term)?;

            use Type::*;
            use UnaryOpKind::*;
            Ok(match (*op, ty) {
                (Not, Boolean) => (Boolean, term.as_bool().unwrap().not().into()),
                (Negate, Integer) => (Integer, term.as_int().unwrap().unary_minus().into()),
                (Negate, Real) => (Integer, term.as_float().unwrap().unary_neg().into()),
                (op, ty) => return Err(Error::InvalidUnaryOp { op, ty }),
            })
        }
        Expr::BinaryOp { op, lhs, rhs } => {
            let (lhs_ty, lhs) = expr_to_z3(ctx, variables, relations, lhs)?;
            let (rhs_ty, rhs) = expr_to_z3(ctx, variables, relations, rhs)?;

            use BinaryOpKind::*;
            use Type::*;
            let result = match (*op, lhs_ty, rhs_ty) {
                // equality
                (Eq, lhs_ty, rhs_ty) if lhs_ty == rhs_ty => {
                    Some((Boolean, ast::Dynamic::from(lhs._eq(&rhs))))
                }

                // integer arithmetic
                (_, Integer, Integer) => {
                    let lhs = lhs.as_int().unwrap();
                    let rhs = rhs.as_int().unwrap();
                    let result = match *op {
                        Add => Some(lhs + rhs),
                        Mul => Some(lhs * rhs),
                        Div => Some(lhs / rhs),
                        Lt => return Ok((Boolean, lhs.lt(&rhs).into())),
                        Le => return Ok((Boolean, lhs.le(&rhs).into())),
                        _ => None,
                    };

                    result.map(|result| (Integer, ast::Dynamic::from(result)))
                }

                // real arithmetic
                (_, Real, Real) => {
                    let rounding = ast::Float::round_towards_zero(ctx);
                    let lhs = lhs.as_float().unwrap();
                    let rhs = rhs.as_float().unwrap();
                    let result = match *op {
                        Add => Some(rounding.add(&lhs, &rhs)),
                        Mul => Some(rounding.mul(&lhs, &rhs)),
                        Div => Some(rounding.div(&lhs, &rhs)),
                        Lt => return Ok((Boolean, lhs.lt(&rhs).into())),
                        Le => return Ok((Boolean, lhs.le(&rhs).into())),
                        _ => None,
                    };

                    result.map(|result| (Real, ast::Dynamic::from(result)))
                }

                // string arithmetic
                (_, String, String) => {
                    let lhs = lhs.as_string().unwrap();
                    let rhs = rhs.as_string().unwrap();
                    let result = match *op {
                        Concat => Some(ast::String::concat(ctx, &[&lhs, &rhs])),
                        _ => None,
                    };

                    result.map(|result| (String, ast::Dynamic::from(result)))
                }

                // boolean logic
                (_, Boolean, Boolean) => {
                    let lhs = lhs.as_bool().unwrap();
                    let rhs = rhs.as_bool().unwrap();
                    let result = match *op {
                        And => Some(ast::Bool::and(ctx, &[&lhs, &rhs])),
                        Or => Some(ast::Bool::or(ctx, &[&lhs, &rhs])),
                        _ => None,
                    };

                    result.map(|result| (Boolean, ast::Dynamic::from(result)))
                }

                _ => None,
            };

            result.ok_or(Error::InvalidBinaryOp {
                op: *op,
                lhs: lhs_ty,
                rhs: rhs_ty,
            })
        }
    }
}

pub fn value_to_z3<'a>(ctx: &'a Context, val: &Value) -> (Type, ast::Dynamic<'a>) {
    use Value::*;
    match val {
        Boolean(val) => (Type::Boolean, ast::Bool::from_bool(ctx, *val).into()),
        Integer(val) => (Type::Integer, ast::Int::from_i64(ctx, *val).into()),
        Real(val) => (Type::Real, ast::Float::from_f64(ctx, **val).into()),
        Symbol(val) => (
            Type::Symbol,
            ast::String::from_str(ctx, val).unwrap().into(),
        ),
        String(val) => (
            Type::String,
            ast::String::from_str(ctx, val).unwrap().into(),
        ),
    }
}

pub enum Error {
    InvalidVariableIndex(u32),
    InvalidRelationIndex(u32),
    UnexpectedSort(SortKind),
    InvalidUnaryOp {
        op: UnaryOpKind,
        ty: Type,
    },
    InvalidBinaryOp {
        op: BinaryOpKind,
        lhs: Type,
        rhs: Type,
    },
}
