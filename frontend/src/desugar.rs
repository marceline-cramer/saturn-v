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

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use indexmap::IndexSet;
use salsa::Database;

use saturn_v_ir as ir;

use crate::{
    infer::{TypeKey, TypeTable, TypedRuleBody},
    parse::{file_relation, BinaryOpKind, Expr, ExprKind, RelationDefinition, UnaryOpKind},
    toplevel::File,
    types::PrimitiveType,
};

pub fn desugar_rule_body<'db>(
    db: &'db dyn Database,
    needed_vars: HashSet<u32>,
    rule_body: TypedRuleBody<'db>,
) -> ir::RuleBody<RelationDefinition<'db>> {
    // look up the abstract rule body
    let inner = rule_body.inner(db);

    // create the desugarer
    let mut desugarer = Desugarer::new(db, inner.ast(db).file(db), rule_body.table(db));

    // desugar each of the clauses in turn
    let mut clauses = Vec::with_capacity(inner.clauses(db).len());
    for clause in inner.clauses(db).iter() {
        let exprs = desugarer.desugar_expr(*clause);
        assert_eq!(exprs.len(), 1, "desugared clause does not have length 1");
        clauses.push(exprs[0].clone());
    }

    // finalize the rule body
    desugarer.to_rule_body(needed_vars, clauses)
}

/// A structure used to track the mutable state used in desugaring a rule body.
pub struct Desugarer<'db> {
    /// The reference to the database being used.
    db: &'db dyn Database,

    /// The file that desugaring is being done in. Used to resolve relation names.
    file: File,

    /// The complete type table.
    table: TypeTable<'db>,

    /// A growable list of lowered variables.
    lowered_vars: Vec<PrimitiveType>,

    /// Maps each type key in the table to the first index of their lowered,
    /// flattened variables and the number of variables.
    typed_vars: HashMap<TypeKey<'db>, (u32, usize)>,

    /// An index set of all loaded relations.
    relations: IndexSet<RelationDefinition<'db>>,

    /// A backlog of equality clauses for binding relation variables to expressions.
    relation_bindings: Vec<(u32, ir::Expr)>,
}

impl<'db> Desugarer<'db> {
    /// Creates a new desugarer.
    pub fn new(db: &'db dyn Database, file: File, table: TypeTable<'db>) -> Self {
        Self {
            db,
            file,
            table,
            lowered_vars: vec![],
            typed_vars: HashMap::new(),
            relations: IndexSet::new(),
            relation_bindings: vec![],
        }
    }

    /// Creates an IR rule body out of given clauses and this desugarer's relation bindings.
    pub fn to_rule_body(
        &self,
        needed_vars: HashSet<u32>,
        mut clauses: Vec<ir::Expr>,
    ) -> ir::RuleBody<RelationDefinition<'db>> {
        // add each of the relation bindings as clauses
        clauses.extend(
            self.relation_bindings
                .iter()
                .map(|(idx, expr)| ir::Expr::BinaryOp {
                    op: ir::BinaryOpKind::Eq,
                    lhs: Arc::new(ir::Expr::Variable(*idx)),
                    rhs: Arc::new(expr.clone()),
                }),
        );

        // reduce clauses into a single conjunctive filter expression
        let test = clauses
            .into_iter()
            .reduce(|lhs, rhs| ir::Expr::BinaryOp {
                op: ir::BinaryOpKind::And,
                lhs: Arc::new(lhs),
                rhs: Arc::new(rhs),
            })
            .unwrap_or(ir::Expr::Value(ir::Value::Boolean(true)));

        // desugared expressions are just filters with sinks.
        // transforming this into a proper relational program is the job of lowering
        let instructions = ir::Instruction::Sink {
            vars: needed_vars,
            rest: Box::new(ir::Instruction::Filter {
                test,
                rest: Box::new(ir::Instruction::Noop),
            }),
        };

        // collect all variables
        let vars = self.lowered_vars.iter().copied().map(Into::into).collect();

        // collect all loaded relations
        let loaded = self.relations.iter().copied().collect();

        // create the rule
        ir::RuleBody {
            vars,
            loaded,
            instructions,
        }
    }

    /// Desugars an expression, returning its flattened list of sub-expressions.
    pub fn desugar_expr(&mut self, expr: Expr<'db>) -> Vec<ir::Expr> {
        use ExprKind::*;
        match expr.kind(self.db) {
            // tuples simply concatenate their desugared elements
            Tuple(els) => els.iter().flat_map(|el| self.desugar_expr(*el)).collect(),
            // wrap value literals directly in an expression
            Value(val) => vec![ir::Expr::Value(val.clone())],
            // pass variables to the dedicated method
            // wow, it's a method, huh? am I doing OOP again? mind-boggling.
            Variable(name) => self.desugar_variable(name),
            // desugar atoms in a dedicated method
            Atom { head, body } => {
                let body = self.desugar_expr(body);
                self.desugar_atom(head.inner, body)
            }
            // desugar unary operators in a dedicated method
            UnaryOp { op, term } => {
                let term = self.desugar_expr(term);
                self.desugar_unary_op(op.inner, term)
            }
            // desugar binary operators in a dedicated method
            BinaryOp { op, lhs, rhs } => {
                let lhs = self.desugar_expr(lhs);
                let rhs = self.desugar_expr(rhs);
                self.desugar_binary_op(op.inner, lhs, rhs)
            }
        }
    }

    /// Flattens a high-level, typed variable into lowered variables.
    ///
    /// Panics if the variable name is not in the type table.
    pub fn desugar_variable(&mut self, name: String) -> DesugaredExpr {
        // create the type key
        let key = TypeKey::Variable(name.clone());

        // initialize this variable's lowered storage if it hasn't already been
        let (start, len) = self.typed_vars.entry(key.clone()).or_insert_with(|| {
            // lookup the flattened type
            let ty = self
                .table
                .flatten(&key.into())
                .unwrap_or_else(|| panic!("failed to flatten variable {name:?}"));

            // extend the variable arrays with the flattened types
            let idx = self.lowered_vars.len();
            let len = ty.len();
            self.lowered_vars.extend(ty);
            (idx as u32, len)
        });

        // map flattened types into variable lookups
        (0..*len)
            .map(|idx| ir::Expr::Variable(*start + idx as u32))
            .collect()
    }

    /// Desugars an atom expression.
    pub fn desugar_atom(&mut self, head: String, body: DesugaredExpr) -> DesugaredExpr {
        // lookup the flattened type of the relation itself
        let ty = self
            .table
            .flatten(&TypeKey::Relation(head.clone()).into())
            .expect("failed to flatten relation type");

        // sanity-check that the body and types match
        // not a debug assertion because bugs that would be caught by this check
        // would otherwise be nearly impossible to track down
        assert_eq!(body.len(), ty.len(), "flattened atom lengths don't match");

        // create a list of query terms
        let mut query = Vec::with_capacity(body.len());
        for (body, ty) in body.into_iter().zip(ty) {
            use ir::Expr::*;
            query.push(match body {
                // if the body's term is a variable, use it directly
                Variable(idx) => ir::QueryTerm::Variable(idx),
                // if the body's term is a value, use it directly
                Value(val) => ir::QueryTerm::Value(val),
                // for all other expressions, create a fresh binding variable
                expr => {
                    let idx = self.lowered_vars.len() as u32;
                    self.lowered_vars.push(ty);
                    self.relation_bindings.push((idx, expr));
                    ir::QueryTerm::Variable(idx)
                }
            });
        }

        // look up the index of the loaded relation
        let (relation, _old) = self.relations.insert_full(
            file_relation(self.db, self.file, head).expect("failed to find relation definition"),
        );

        // create the final relation evaluation
        vec![ir::Expr::Load {
            relation: relation as u32,
            query,
        }]
    }

    /// Desugars a binary operation.
    pub fn desugar_binary_op(
        &mut self,
        op: BinaryOpKind,
        lhs: DesugaredExpr,
        rhs: DesugaredExpr,
    ) -> DesugaredExpr {
        // sanity-check that lengths of sides match
        assert_eq!(lhs.len(), rhs.len(), "binary operand lengths do not match");

        // translate high-level binary operator kinds into IR
        use ir::BinaryOpKind as IR;
        use BinaryOpKind::*;
        let (op, (lhs, rhs)) = match (op, (lhs, rhs)) {
            // swap around high-level operators that have redundant IR
            (Gt, (lhs, rhs)) => (IR::Lt, (rhs, lhs)),
            (Ge, (lhs, rhs)) => (IR::Le, (rhs, lhs)),
            // the does-not-equal operator is the negation of equality
            (Ne, (lhs, rhs)) => {
                let inner = self.desugar_binary_op(BinaryOpKind::Eq, lhs, rhs);
                return self.desugar_unary_op(UnaryOpKind::Not, inner);
            }
            // subtraction is implementing using addition, negating the rhs
            (Sub, (lhs, rhs)) => {
                let rhs = self.desugar_unary_op(UnaryOpKind::Negate, rhs);
                (IR::Add, (lhs, rhs))
            }
            // all other operators can be kept as-is
            (Add, terms) => (IR::Add, terms),
            (Mul, terms) => (IR::Mul, terms),
            (Div, terms) => (IR::Div, terms),
            (Concat, terms) => (IR::Concat, terms),
            (And, terms) => (IR::And, terms),
            (Or, terms) => (IR::Or, terms),
            (Eq, terms) => (IR::Eq, terms),
            (Lt, terms) => (IR::Lt, terms),
            (Le, terms) => (IR::Le, terms),
        };

        // implement each logical operation on the inner terms
        let terms = lhs
            .into_iter()
            .zip(rhs)
            .map(|(lhs, rhs)| ir::Expr::BinaryOp {
                op,
                lhs: Arc::new(lhs),
                rhs: Arc::new(rhs),
            });

        // in the special case that this is a logical operation, collapse all
        // terms into a single conjunction of Boolean operations
        if op.category() == ir::BinaryOpCategory::Logical {
            // unwrap is okay because no desugaring base cases return empty tuples
            return vec![terms
                .reduce(|lhs, rhs| ir::Expr::BinaryOp {
                    op: IR::And,
                    lhs: Arc::new(lhs),
                    rhs: Arc::new(rhs),
                })
                .unwrap()];
        }

        // otherwise, return terms as they are
        terms.collect()
    }

    /// Desugars a unary operation.
    pub fn desugar_unary_op(&mut self, op: UnaryOpKind, term: DesugaredExpr) -> DesugaredExpr {
        // unary operations just pass through their operators
        // this should only ever work on single flattened expressions
        // but... in the case it shouldn't later, it's not this code's problem
        term.into_iter()
            .map(|term| ir::Expr::UnaryOp {
                op: op.into(),
                term: Arc::new(term),
            })
            .collect()
    }
}

/// A flattened, desugared expression, representing each element in a tuple.
pub type DesugaredExpr = Vec<ir::Expr>;
