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

use std::sync::Arc;

use saturn_v_ir::{ConstraintKind, ConstraintWeight, Expr, QueryTerm, RelationKind, Value};
use serde::{Deserialize, Serialize};

use crate::utils::Key;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
pub struct Fact {
    pub relation: Key<Relation>,
    pub values: FixedValues,
}

impl Fact {
    pub fn relation_pair(self) -> (Key<Relation>, Self) {
        (self.relation, self)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
pub enum Gate {
    And { lhs: Condition, rhs: Condition },
    Or { terms: Vec<Condition> },
    Decision { terms: Vec<Condition> },
}

/// Constrains a group of constraint conditions.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
pub struct ConstraintGroup {
    pub terms: Vec<Condition>,
    pub weight: ConstraintWeight,
    pub kind: ConstraintKind,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
pub struct Tuple {
    pub values: Values,
    pub condition: Option<Condition>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
pub enum Condition {
    Gate(Key<Gate>),
    Fact(Key<Fact>),
}

pub type IndexList = Arc<[usize]>;

/// The terms of a query.
///
/// Terms can either be constrained by a value or bound to variables.
pub type Query = Arc<[Option<Value>]>;

/// The head of a relation store operation.
pub type StoreHead = Arc<[QueryTerm]>;

/// The head of a load operation.
pub type LoadHead = (Key<Relation>, LoadMask, FixedValues);

/// The type of a "load mask": a selection of which columns of a relation to join by in load operations.
///
/// A `true` represents a variable binding and a `false` represents a static value.
pub type LoadMask = bitvec::boxed::BitBox;

/// Everyday, mutable value storage in a node, typically in [Tuple].
pub type Values = Vec<Value>;

/// Immutable value storage. Lower overhead to arrange.
pub type FixedValues = Arc<[Value]>;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
pub enum Node {
    /// Joins two nodes together.
    Join {
        /// The left-hand node to join. Leftover terms come first.
        lhs: Key<Node>,

        /// The right-hand node to join. Leftover terms come after left-hand terms.
        rhs: Key<Node>,

        /// The number of terms starting from the front of each node to join.
        num: usize,
    },

    /// Merges two nodes together.
    Merge {
        /// The left-hand node to merge.
        lhs: Key<Node>,

        /// The right-hand node to merge.
        rhs: Key<Node>,
    },

    /// Projects (rearranges) a node's terms.
    ///
    /// Can also drop variables.
    Project {
        /// The node to project.
        src: Key<Node>,

        /// A list of indices for which terms of the original node this projection loads.
        map: IndexList,
    },

    /// Evaluates a test expression on the input tuples and keeps the ones that pass.
    Filter {
        /// The node to pull input tuples from.
        src: Key<Node>,

        /// The expression to execute.
        expr: Expr,
    },

    /// Evaluates an expression to push a new element to input tuples.
    Push {
        /// The node to pull input tuples from.
        src: Key<Node>,

        /// The expression to execute.
        expr: Expr,
    },

    /// Loads node contents from a relation.
    LoadRelation {
        /// The key of the relation to load.
        relation: Key<Relation>,

        /// A query to constrain the loading by.
        query: Query,
    },

    /// Stores a node's contents into a relation.
    StoreRelation {
        /// The node to load terms from.
        src: Key<Node>,

        /// The relation to store into.
        dst: Key<Relation>,

        /// The map from destination variables or values to relation elements.
        head: StoreHead,
    },

    /// Stores a node's contents as a constraint.
    Constraint {
        /// The node to load terms from.
        src: Key<Node>,

        /// The indices of the variables that the head is made up of.
        head: IndexList,

        /// The constraint's weight.
        weight: ConstraintWeight,

        /// The kind of constraint.
        kind: ConstraintKind,
    },
}

impl Node {
    pub fn join_lhs(self) -> Option<(Key<Node>, usize)> {
        match self {
            Node::Join { lhs, num, .. } => Some((lhs, num)),
            _ => None,
        }
    }

    pub fn join_rhs(self) -> Option<(Key<Node>, usize)> {
        match self {
            Node::Join { rhs, num, .. } => Some((rhs, num)),
            _ => None,
        }
    }

    pub fn merge_lhs(self) -> Option<Key<Node>> {
        match self {
            Node::Merge { lhs, .. } => Some(lhs),
            _ => None,
        }
    }

    pub fn merge_rhs(self) -> Option<Key<Node>> {
        match self {
            Node::Merge { rhs, .. } => Some(rhs),
            _ => None,
        }
    }

    pub fn project(self) -> Option<(Key<Node>, IndexList)> {
        match self {
            Node::Project { src, map } => Some((src, map)),
            _ => None,
        }
    }

    pub fn filter(self) -> Option<(Key<Node>, Expr)> {
        match self {
            Node::Filter { src, expr } => Some((src, expr)),
            _ => None,
        }
    }

    pub fn push(self) -> Option<(Key<Node>, Expr)> {
        match self {
            Node::Push { src, expr } => Some((src, expr)),
            _ => None,
        }
    }

    pub fn load_mask(self) -> Option<(Key<Relation>, LoadMask)> {
        match self {
            Node::LoadRelation { relation, query } => {
                Some((relation, query.iter().map(Option::is_none).collect()))
            }
            _ => None,
        }
    }

    pub fn load_head(self) -> Option<LoadHead> {
        match self {
            Node::LoadRelation { relation, query } => Some((
                relation,
                query.iter().map(Option::is_none).collect(),
                query.iter().flatten().cloned().collect(),
            )),
            _ => None,
        }
    }

    pub fn store_relation(self) -> Option<(Key<Node>, (Key<Relation>, StoreHead))> {
        match self {
            Node::StoreRelation { src, dst, head } => Some((src, (dst, head))),
            _ => None,
        }
    }

    pub fn constraint_src(self) -> Option<(Key<Node>, IndexList)> {
        match self {
            Node::Constraint { src, head, .. } => Some((src, head)),
            _ => None,
        }
    }

    pub fn constraint_type(self) -> Option<(ConstraintWeight, ConstraintKind)> {
        match self {
            Node::Constraint { weight, kind, .. } => Some((weight, kind)),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
pub struct Relation {
    /// Used to differentiate otherwise identically-defined relations.
    pub discriminant: u64,

    /// The kind of relation this is.
    pub kind: RelationKind,

    /// If this relation is an output.
    pub is_output: bool,

    /// The formatting segments to display this relation.
    pub formatting: Arc<[String]>,
}
