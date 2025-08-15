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
    fmt::Display,
    hash::Hash,
    sync::Arc,
};

use ordered_float::OrderedFloat;
use pretty::RcDoc;
use serde::{Deserialize, Serialize};
use strum::{EnumDiscriminants, EnumString};

#[cfg(feature = "fuzz")]
use arbitrary::Arbitrary;

pub mod sexp;
pub mod validate;

#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[cfg_attr(feature = "fuzz", derive(Arbitrary))]
#[cfg_attr(
    feature = "fuzz",
    arbitrary(bound = "R: Arbitrary<'arbitrary> + Eq + Hash")
)]
pub struct Program<R: Eq + Hash> {
    pub relations: HashMap<R, Relation<R>>,
    pub constraints: Vec<Constraint<R>>,
}

impl<R: Eq + Hash> Default for Program<R> {
    fn default() -> Self {
        Self {
            relations: HashMap::new(),
            constraints: Vec::new(),
        }
    }
}

impl<R: Clone + Hash + Eq> Program<R> {
    /// Easy shorthand to add a relation to this program.
    pub fn insert_relation(&mut self, relation: Relation<R>) {
        self.relations.insert(relation.store.clone(), relation);
    }

    /// Merges another program into this one.
    pub fn merge(mut self, other: Self) -> Self {
        // constraints simply get added
        self.constraints.extend(other.constraints);

        // relations need to be tree-merged
        use std::collections::hash_map::Entry;
        for (key, relation) in other.relations {
            match self.relations.entry(key) {
                Entry::Occupied(mut entry) => {
                    // move relation contents into this one
                    // TODO: assert that properties of the relations match
                    let old = entry.get_mut();
                    old.rules.extend(relation.rules);
                    old.facts.extend(relation.facts);
                }
                Entry::Vacant(entry) => {
                    // simply add the new relation
                    entry.insert(relation);
                }
            }
        }

        // return the mutated self
        self
    }

    /// Translates all of the relation values in this program into another type.
    pub fn map_relations<O: Hash + Eq>(self, mut cb: impl FnMut(R) -> O) -> Program<O> {
        // map relations
        let relations = self
            .relations
            .into_iter()
            .map(|(key, relation)| {
                let key = cb(key);

                let rules = relation
                    .rules
                    .into_iter()
                    .map(|rule| Rule {
                        head: rule.head,
                        body: rule.body.map_relations(&mut cb),
                    })
                    .collect();

                let relation = Relation {
                    ty: relation.ty,
                    kind: relation.kind,
                    io: relation.io,
                    facts: relation.facts,
                    store: cb(relation.store),
                    rules,
                };

                (key, relation)
            })
            .collect();

        // map constraints
        let constraints = self
            .constraints
            .into_iter()
            .map(|constraint| Constraint {
                weight: constraint.weight,
                kind: constraint.kind,
                head: constraint.head,
                body: constraint.body.map_relations(&mut cb),
            })
            .collect();

        // return mapped items
        Program {
            relations,
            constraints,
        }
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

    /// The variables to group this constraint over.
    pub head: Vec<u32>,

    /// This constraint's [RuleBody].
    pub body: RuleBody<R>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
#[cfg_attr(feature = "fuzz", derive(Arbitrary))]
pub enum ConstraintWeight {
    Hard,
    Soft(u32),
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

#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[cfg_attr(feature = "fuzz", derive(Arbitrary))]
pub struct Relation<R> {
    /// The relation's type.
    pub ty: StructuredType,

    /// The custom relation data that this relation stores to.
    pub store: R,

    /// The kind of relation this is.
    pub kind: RelationKind,

    /// The IO of this relation.
    pub io: RelationIO,

    /// A list of facts initially stored by this relation.
    pub facts: Vec<Vec<Value>>,

    /// Each rule that stores to this relation.
    pub rules: Vec<Rule<R>>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
#[cfg_attr(feature = "fuzz", derive(Arbitrary))]
pub enum RelationIO {
    /// This relation does not interact with IO at all.
    None,

    /// This relation is an input relation.
    Input,

    /// This relation is an output relation.
    Output,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
#[cfg_attr(feature = "fuzz", derive(Arbitrary))]
pub enum StructuredType {
    Tuple(Vec<StructuredType>),
    Primitive(Type),
}

impl StructuredType {
    /// Flattens the structured type into a list of primitives.
    pub fn flatten(&self) -> Vec<Type> {
        use StructuredType::*;
        match self {
            Tuple(els) => els.iter().flat_map(Self::flatten).collect(),
            Primitive(ty) => vec![*ty],
        }
    }
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

#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[cfg_attr(feature = "fuzz", derive(Arbitrary))]
pub struct Rule<R> {
    /// Maps from the variables in the filter to query terms to store in the
    /// relation this rule is for.
    pub head: Vec<QueryTerm>,

    /// The rule's body.
    pub body: RuleBody<R>,
}

#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[cfg_attr(feature = "fuzz", derive(Arbitrary))]
pub struct RuleBody<R> {
    /// The type of each variable.
    pub vars: Vec<Type>,

    /// The lookups for custom relation types loaded by the instructions.
    pub loaded: Vec<R>,

    /// The desugared instructions for this rule.
    pub instructions: Instruction,
}

impl<R> RuleBody<R> {
    /// Translates all of the relation values in this rule into another type.
    pub fn map_relations<O: Hash + Eq>(self, cb: impl FnMut(R) -> O) -> RuleBody<O> {
        RuleBody {
            vars: self.vars,
            instructions: self.instructions,
            loaded: self.loaded.into_iter().map(cb).collect(),
        }
    }
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

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Value::*;
        match self {
            Boolean(true) => write!(f, "True"),
            Boolean(false) => write!(f, "False"),
            Integer(val) => write!(f, "{val}"),
            Real(val) => write!(f, "{val}"),
            Symbol(name) => write!(f, "{name}"),
            String(val) => write!(f, "\"{val:?}\""),
        }
    }
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

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
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
