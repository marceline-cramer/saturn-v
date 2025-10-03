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
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use indexmap::IndexSet;
use salsa::{Database, Update};

use saturn_v_ir::{self as ir, QueryTerm};

use crate::{
    diagnostic::{AccumulateDiagnostic, BasicDiagnostic, DiagnosticKind},
    infer::{TypeKey, TypeTable, TypedRuleBody},
    parse::{BinaryOpKind, Expr, ExprKind, Pattern, RelationDefinition, UnaryOpKind},
    resolve::file_relation,
    toplevel::{AstNode, File},
    types::{PrimitiveType, WithAst},
};

#[salsa::tracked]
pub fn desugar_rule_body<'db>(
    db: &'db dyn Database,
    rule_body: TypedRuleBody<'db>,
) -> Desugarer<'db> {
    // look up the abstract rule body
    let inner = rule_body.inner(db);

    // create the desugarer
    let mut desugarer = Desugarer::new(inner.ast(db).file(db), rule_body.table(db).clone());

    // desugar each of the clauses in turn
    for clause in inner.clauses(db).iter() {
        desugarer.add_clause(db, *clause);
    }

    // return the completed desugarer
    desugarer
}

/// A structure used to track the mutable state used in desugaring a rule body.
#[derive(Clone, PartialEq, Eq, Update)]
pub struct Desugarer<'db> {
    /// The file that desugaring is being done in. Used to resolve relation names.
    file: File,

    /// The complete type table.
    table: TypeTable<'db>,

    /// A growable list of lowered variables.
    lowered_vars: Vec<PrimitiveType>,

    /// Maps each type key in the table to the first index of their lowered,
    /// flattened variables and the number of variables.
    typed_vars: BTreeMap<TypeKey<'db>, (u32, usize)>,

    /// An index set of all loaded relations.
    relations: IndexSet<RelationDefinition<'db>>,

    /// Clauses that have been added to this desugarer.
    clauses: DesugaredExpr,
}

impl<'db> Desugarer<'db> {
    /// Creates a new desugarer.
    pub fn new(file: File, table: TypeTable<'db>) -> Self {
        Self {
            file,
            table,
            lowered_vars: Vec::new(),
            typed_vars: BTreeMap::new(),
            relations: IndexSet::new(),
            clauses: Vec::new(),
        }
    }

    /// Desugars a pattern into a set of query terms and needed variables.
    pub fn desugar_pattern(
        &mut self,
        db: &'db dyn Database,
        pattern: &Pattern,
        query: &mut Vec<QueryTerm>,
        needed: &mut BTreeSet<u32>,
    ) {
        match pattern {
            Pattern::Tuple(els) => els
                .iter()
                .for_each(|el| self.desugar_pattern(db, el.as_ref(), query, needed)),
            Pattern::Variable(name) => {
                let vars = self.allocate_variable(db, name);
                needed.extend(vars.iter().copied());
                query.extend(vars.into_iter().map(QueryTerm::Variable));
            }
            Pattern::Value(val) => query.push(QueryTerm::Value(val.clone())),
        }
    }

    /// Creates an IR rule body out of given clauses and this desugarer's relation bindings.
    pub fn to_rule_body(
        &self,
        needed_vars: BTreeSet<u32>,
    ) -> ir::RuleBody<RelationDefinition<'db>> {
        // reduce clauses into a single conjunctive filter expression
        let test = self
            .clauses
            .clone()
            .into_iter()
            .map(|expr| expr.inner)
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

    /// Adds an expression as a clause.
    pub fn add_clause(&mut self, db: &'db dyn Database, expr: Expr<'db>) {
        let exprs = self.desugar_expr(db, expr);
        assert_eq!(exprs.len(), 1, "desugared clause does not have length 1");
        self.clauses.push(exprs[0].clone());
    }

    /// Desugars an expression, returning its flattened list of sub-expressions.
    pub fn desugar_expr(&mut self, db: &'db dyn Database, expr: Expr<'db>) -> DesugaredExpr {
        use ExprKind::*;
        match expr.kind(db) {
            // tuples simply concatenate their desugared elements
            Tuple(els) => els
                .iter()
                .flat_map(|el| self.desugar_expr(db, *el))
                .collect(),
            // wrap value literals directly in an expression
            Value(val) => vec![expr.ast(db).with(ir::Expr::Value(val.clone()))],
            // pass variables to the dedicated method
            // wow, it's a method, huh? am I doing OOP again? mind-boggling.
            Variable(name) => self.desugar_variable(db, expr.ast(db).with(name)),
            // desugar atoms in a dedicated method
            Atom { head, body } => {
                let body = self.desugar_expr(db, body);
                vec![expr.ast(db).with(self.desugar_atom(db, head, body))]
            }
            // desugar unary operators in a dedicated method
            UnaryOp { op, term } => {
                let term = self.desugar_expr(db, term);
                self.desugar_unary_op(db, op.inner, term)
            }
            // desugar binary operators in a dedicated method
            BinaryOp { op, lhs, rhs } => {
                let lhs = self.desugar_expr(db, lhs);
                let rhs = self.desugar_expr(db, rhs);
                self.desugar_binary_op(db, expr.ast(db), op.inner, lhs, rhs)
            }
        }
    }

    /// Flattens a high-level, typed variable into lowered variables.
    ///
    /// Panics if the variable name is not in the type table.
    pub fn desugar_variable(
        &mut self,
        db: &'db dyn Database,
        name: WithAst<String>,
    ) -> DesugaredExpr {
        self.allocate_variable(db, name.as_str())
            .into_iter()
            .map(ir::Expr::Variable)
            .map(|var| name.with(var))
            .collect()
    }

    /// Flattens a high-level, typed variable into a list of indices of lowered varaibles.
    ///
    /// Panics if the variable name is not in the type table.
    pub fn allocate_variable(&mut self, _db: &'db dyn Database, name: &str) -> Vec<u32> {
        // create the type key
        let key = TypeKey::Variable(name.to_string());

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

        // map flattened types into variable indices
        (0..*len).map(|idx| *start + idx as u32).collect()
    }

    /// Desugars an atom expression.
    pub fn desugar_atom(
        &mut self,
        db: &'db dyn Database,
        head: WithAst<String>,
        body: DesugaredExpr,
    ) -> ir::Expr {
        // lookup the flattened type of the relation itself
        let ty = self
            .table
            .flatten(&TypeKey::Relation(head.as_ref().clone()).into())
            .expect("failed to flatten relation type");

        // sanity-check that the body and types match
        // not a debug assertion because bugs that would be caught by this check
        // would otherwise be nearly impossible to track down
        assert_eq!(body.len(), ty.len(), "flattened atom lengths don't match");

        // create a list of query terms
        let mut query = Vec::with_capacity(body.len());
        for (body, ty) in body.into_iter().zip(ty) {
            use ir::Expr::*;
            query.push(match body.as_ref().clone() {
                // if the body's term is a variable, use it directly
                Variable(idx) => ir::QueryTerm::Variable(idx),
                // if the body's term is a value, use it directly
                Value(val) => ir::QueryTerm::Value(val),
                // for all other expressions, create a fresh binding variable
                _ => {
                    let idx = self.lowered_vars.len() as u32;
                    self.lowered_vars.push(ty);
                    self.bind_relation(db, idx, body);
                    ir::QueryTerm::Variable(idx)
                }
            });
        }

        // look up the index of the loaded relation
        let (relation, _old) = self.relations.insert_full(
            file_relation(db, self.file, head).expect("failed to find relation definition"),
        );

        // create the final relation evaluation
        ir::Expr::Load {
            relation: relation as u32,
            query,
        }
    }

    /// Helper function to bind a fresh relation variable to an expression.
    fn bind_relation(&mut self, db: &dyn Database, var: u32, expr: WithAst<ir::Expr>) {
        WarnExpressionsInQueries { ast: expr.ast }.accumulate(db);

        self.clauses.push(expr.map(|expr| ir::Expr::BinaryOp {
            op: ir::BinaryOpKind::Eq,
            lhs: Arc::new(ir::Expr::Variable(var)),
            rhs: Arc::new(expr),
        }))
    }

    /// Desugars a binary operation.
    pub fn desugar_binary_op(
        &mut self,
        db: &'db dyn Database,
        ast: AstNode,
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
                let inner = self.desugar_binary_op(db, ast, BinaryOpKind::Eq, lhs, rhs);
                return self.desugar_unary_op(db, UnaryOpKind::Not, inner);
            }
            // subtraction is implementing using addition, negating the rhs
            (Sub, (lhs, rhs)) => {
                let rhs = self.desugar_unary_op(db, UnaryOpKind::Negate, rhs);
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
                lhs: Arc::new(lhs.inner),
                rhs: Arc::new(rhs.inner),
            });

        // in the special case that this is a logical operation, collapse all
        // terms into a single conjunction of Boolean operations
        match op.category() {
            ir::BinaryOpCategory::Logical | ir::BinaryOpCategory::Comparison => {
                // unwrap is okay because no desugaring base cases return empty tuples
                vec![terms
                    .reduce(|lhs, rhs| ir::Expr::BinaryOp {
                        op: IR::And,
                        lhs: Arc::new(lhs),
                        rhs: Arc::new(rhs),
                    })
                    .map(|term| ast.with(term))
                    .unwrap()]
            }
            // otherwise, return terms as they are
            _ => terms.map(|term| ast.with(term)).collect(),
        }
    }

    /// Desugars a unary operation.
    pub fn desugar_unary_op(
        &mut self,
        _db: &'db dyn Database,
        op: UnaryOpKind,
        term: DesugaredExpr,
    ) -> DesugaredExpr {
        // unary operations just pass through their operators
        // this should only ever work on single flattened expressions
        // but... in the case it shouldn't later, it's not this code's problem
        term.into_iter()
            .map(|term| {
                term.map(|term| ir::Expr::UnaryOp {
                    op: op.into(),
                    term: Arc::new(term),
                })
            })
            .collect()
    }
}

/// A flattened, desugared expression, representing each element in a tuple.
pub type DesugaredExpr = Vec<WithAst<ir::Expr>>;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct WarnExpressionsInQueries {
    ast: AstNode,
}

impl BasicDiagnostic for WarnExpressionsInQueries {
    fn range(&self) -> std::ops::Range<AstNode> {
        self.ast..self.ast
    }

    fn message(&self) -> String {
        "Kerolox does not support assigning variables in query expressions".to_string()
    }

    fn kind(&self) -> DiagnosticKind {
        DiagnosticKind::Warning
    }

    fn is_fatal(&self) -> bool {
        false
    }
}
