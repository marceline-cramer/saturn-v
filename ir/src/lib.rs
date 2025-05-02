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

#[cfg(feature = "fuzz")]
use arbitrary::Arbitrary;

pub mod sexp;
pub mod validate;

#[derive(Clone, Debug, Default)]
#[cfg_attr(feature = "fuzz", derive(Arbitrary))]
#[cfg_attr(
    feature = "fuzz",
    arbitrary(bound = "R: Arbitrary<'arbitrary> + Eq + Hash")
)]
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
#[cfg_attr(feature = "fuzz", derive(Arbitrary))]
#[cfg_attr(
    feature = "fuzz",
    arbitrary(bound = "R: Arbitrary<'arbitrary> + Eq + Hash")
)]
pub struct Constraint<R> {
    /// What weight this constraint has.
    pub weight: ConstraintWeight,

    /// The kind of constraint that this is.
    pub kind: ConstraintKind,

    /// The type of each variable.
    pub vars: Vec<Type>,

    /// The variables to group this constraint over.
    pub head: Vec<u32>,

    /// The lookups for custom relation types loaded by the filter.
    pub loaded: Vec<R>,

    /// The desugared instructions in this constraint.
    pub instructions: Instruction,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
#[cfg_attr(feature = "fuzz", derive(Arbitrary))]
pub enum ConstraintWeight {
    Hard,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
#[cfg_attr(feature = "fuzz", derive(Arbitrary))]
pub enum ConstraintKind {
    /// Constrain the cardinality of elements per group.
    Cardinality {
        /// The kind of cardinality constraint.
        kind: CardinalityConstraintKind,

        /// The threshold of the cardinality constraint.
        threshold: u16,
    },
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
#[cfg_attr(feature = "fuzz", derive(Arbitrary))]
pub enum CardinalityConstraintKind {
    /// The cardinality must be at least the threshold.
    AtLeast,

    /// The cardinality must be at most the threshold.
    AtMost,

    /// The cardinality must be exactly threshold.
    Only,
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "fuzz", derive(Arbitrary))]
pub struct Relation<R> {
    /// The relation's type.
    pub ty: Vec<Type>,

    /// The custom relation data that this relation stores to.
    pub store: R,

    /// The kind of relation this is.
    pub kind: RelationKind,

    /// Whether or not this relation should be outputted.
    pub is_output: bool,

    /// A list of facts initially stored by this relation.
    pub facts: Vec<Vec<Value>>,

    /// Each rule that stores to this relation.
    pub rules: Vec<Rule<R>>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
#[cfg_attr(feature = "fuzz", derive(Arbitrary))]
pub enum RelationKind {
    /// Generates tuples without any logical overhead.
    Basic,

    /// May be dependent on a decision relation but is not a decision itself.
    Conditional,

    /// Is a decision: all tuples may be arbitrarily removed to meet constraints.
    Decision,
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "fuzz", derive(Arbitrary))]
pub struct Rule<R> {
    /// Maps from the variables in the filter to query terms to store in the
    /// relation this rule is for.
    pub head: Vec<QueryTerm>,

    /// The type of each variable.
    pub vars: Vec<Type>,

    /// The lookups for custom relation types loaded by the instructions.
    pub loaded: Vec<R>,

    /// The desugared instructions for this rule.
    pub instructions: Instruction,
}

/// A recursive, branching instruction representation that evaluates to some
/// set of assigned variables.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize, EnumDiscriminants)]
#[strum_discriminants(name(InstructionKind))]
#[strum_discriminants(derive(Hash, Deserialize, Serialize))]
#[cfg_attr(feature = "fuzz", derive(Arbitrary))]
pub enum Instruction {
    /// An instruction that does nothing and creates no variables.
    ///
    /// Invalid and only used to easily terminate instructions.
    Noop,

    /// Declares a variable sink: a set of variables that have not been emitted
    /// by the rest of the instructions.
    Sink { vars: HashSet<u32>, rest: Box<Self> },

    /// Filters tuples depending on the result of a test expression.
    Filter {
        /// The expression to test the filter against.
        ///
        /// Must evaluate to a Boolean.
        test: Expr,

        /// The rest of the instructions.
        rest: Box<Self>,
    },

    /// Leaf instruction that initializes variables using query terms.
    FromQuery {
        /// The index of the relation to load from. The relations corresponding
        /// to each index can be found in structs that own instructions.
        relation: u32,

        /// The terms of the query. The number and types of terms must match the
        /// corresponding type of the query.
        terms: Vec<QueryTerm>,
    },

    /// Assigns the result of an expression to a variable.
    Let {
        /// The index of the variable to assign to.
        var: u32,

        /// The expression to evaluate that assigns a value to the variable.
        ///
        /// All used variables must of course be available in the rest of the
        /// instructions and the type must match the declared type of the variable.
        expr: Expr,

        /// The rest of the instructions.
        rest: Box<Self>,
    },

    /// Merges two instruction branches.
    ///
    /// The set of variable assignments emitted by each branch MUST match.
    Merge {
        /// The left-hand branch of instructions to merge.
        lhs: Box<Self>,

        /// The right-hand branch of instructions to merge.
        rhs: Box<Self>,
    },

    /// Relationally joins two instruction branches.
    ///
    /// For every subset of variables present in one branch, this instruction
    /// emits the union of the shared values for that shared subset as well as
    /// all pairings of values unique to each branch.
    Join {
        /// The left-hand branch of instructions to join.
        lhs: Box<Self>,

        /// The right-hand branch of instructions to join.
        rhs: Box<Self>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
#[cfg_attr(feature = "fuzz", derive(Arbitrary))]
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
#[cfg_attr(feature = "fuzz", derive(Arbitrary))]
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
#[cfg_attr(feature = "fuzz", derive(Arbitrary))]
pub enum UnaryOpKind {
    Not,
    Negate,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
#[cfg_attr(feature = "fuzz", derive(Arbitrary))]
pub enum QueryTerm {
    Variable(u32),
    Value(Value),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
#[cfg_attr(feature = "fuzz", derive(Arbitrary))]
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
#[cfg_attr(feature = "fuzz", derive(Arbitrary))]
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
