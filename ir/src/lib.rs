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
    hash::Hash,
    sync::Arc,
};

use indexmap::IndexSet;
use ordered_float::OrderedFloat;
use pretty::RcDoc;
use serde::{Deserialize, Serialize};
use strum::{EnumDiscriminants, EnumString};

pub mod sexp;
pub mod validate;

#[derive(Clone, Debug, Default)]
pub struct Program<R> {
    pub relations: HashMap<R, Relation<R>>,
    pub constraints: Vec<Constraint<R>>,
}

impl<R: Clone + Hash + Eq> Program<R> {
    /// Easy shorthand to add a relation to this program.
    pub fn insert_relation(&mut self, relation: Relation<R>) {
        self.relations.insert(relation.store.clone(), relation);
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
pub struct Constraint<R> {
    /// The desugared instructions in this constraint.
    pub instructions: Instruction,

    /// The variables to group this constraint over.
    pub head: Vec<u32>,

    /// The lookups for custom relation types loaded by the filter.
    pub loaded: Vec<R>,

    /// The type of each variable.
    pub vars: Vec<Type>,

    /// What weight this constraint has.
    pub weight: ConstraintWeight,

    /// The kind of constraint that this is.
    pub kind: ConstraintKind,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
pub enum ConstraintWeight {
    Hard,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
pub enum ConstraintKind {
    /// For every group, at least one element must be true.
    Any,

    /// Exactly one element in a group must be true.
    One,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Relation<R> {
    /// The relation's type.
    pub ty: Vec<Type>,

    /// The custom relation data that this relation stores to.
    pub store: R,

    /// Each rule that stores to this relation.
    pub rules: Vec<Rule<R>>,

    /// A list of facts initially stored by this relation.
    pub facts: Vec<Vec<Value>>,

    /// The kind of relation this is.
    pub kind: RelationKind,

    /// Whether or not this relation should be outputted.
    pub is_output: bool,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
pub enum RelationKind {
    /// Generates tuples without any logical overhead.
    Basic,

    /// May be dependent on a decision relation but is not a decision itself.
    Conditional,

    /// Is a decision: all tuples may be arbitrarily removed to meet constraints.
    Decision,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Rule<R> {
    /// The desugared instructions for this rule.
    pub instructions: Instruction,

    /// Maps from the variables in the filter to query terms to store in the
    /// relation this rule is for.
    pub head: Vec<QueryTerm>,

    /// The lookups for custom relation types loaded by the instructions.
    pub loaded: Vec<R>,

    /// The type of each variable.
    pub vars: Vec<Type>,
}

#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize, EnumDiscriminants)]
#[strum_discriminants(name(InstructionKind))]
#[strum_discriminants(derive(Hash, Deserialize, Serialize))]
pub enum Instruction {
    Noop,
    Sink(HashSet<u32>, Box<Self>),
    Filter(Expr, Box<Self>),
    FromQuery(u32, Vec<QueryTerm>),
    Let(u32, Expr, Box<Self>),
    Merge(Box<Self>, Box<Self>),
    Join(Box<Self>, Box<Self>),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
pub enum Expr {
    Variable(u32),
    Value(Value),
    Load {
        relation: u32,
        query: Vec<QueryTerm>,
    },
    UnaryOp {
        op: UnaryOpKind,
        term: Arc<Expr>,
    },
    BinaryOp {
        op: BinaryOpKind,
        lhs: Arc<Expr>,
        rhs: Arc<Expr>,
    },
}

impl Expr {
    pub fn map_variables(self, map: &IndexSet<u32>) -> Self {
        use Expr::*;
        match self {
            Variable(idx) => Variable(map.get_index_of(&idx).unwrap() as u32),
            UnaryOp { op, term } => UnaryOp {
                op,
                term: (*term).clone().map_variables(map).into(),
            },
            BinaryOp { op, lhs, rhs } => BinaryOp {
                op,
                lhs: (*lhs).clone().map_variables(map).into(),
                rhs: (*rhs).clone().map_variables(map).into(),
            },
            other => other,
        }
    }
}

/// Redundant operations (Sub, Neq, Gt, Ge) are not included. Use unary ops to
/// evaluate those.
#[derive(
    Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, EnumString, Deserialize, Serialize,
)]
pub enum BinaryOpKind {
    Add,
    Mul,
    Div,
    Concat,
    And,
    Or,
    Eq,
    Lt,
    Le,
}

impl BinaryOpKind {
    pub fn category(&self) -> BinaryOpCategory {
        use BinaryOpCategory::*;
        use BinaryOpKind::*;
        match self {
            Add | Mul | Div => Arithmetic,
            Concat => String,
            And | Or => Logical,
            Eq | Lt | Le => Comparison,
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum BinaryOpCategory {
    Arithmetic,
    String,
    Logical,
    Comparison,
}

#[derive(
    Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, EnumString, Deserialize, Serialize,
)]
pub enum UnaryOpKind {
    Not,
    Negate,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
pub enum QueryTerm {
    Variable(u32),
    Value(Value),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
pub enum Value {
    Boolean(bool),
    Integer(i64),
    Real(OrderedFloat<f64>),
    Symbol(String),
    String(String),
}

impl Value {
    pub fn ty(&self) -> Type {
        use Value::*;
        match self {
            Boolean(_) => Type::Boolean,
            Integer(_) => Type::Integer,
            Real(_) => Type::Real,
            Symbol(_) => Type::Symbol,
            String(_) => Type::String,
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Deserialize, Serialize)]
pub enum Type {
    Boolean,
    Integer,
    Real,
    Symbol,
    String,
}

#[cfg(test)]
pub mod tests {
    use super::*;

    use sexp::Sexp;

    // TODO: move this into sexp module
    #[test]
    fn basic_pretty_print() {
        let expr = Expr::BinaryOp {
            op: BinaryOpKind::Eq,
            lhs: Arc::new(Expr::Variable(0)),
            rhs: Arc::new(Expr::BinaryOp {
                op: BinaryOpKind::Add,
                lhs: Arc::new(Expr::Variable(1)),
                rhs: Arc::new(Expr::Value(Value::Integer(1))),
            }),
        };

        let mut out = String::new();
        expr.to_doc().render_fmt(40, &mut out).unwrap();
        println!("{out}");
    }
}
