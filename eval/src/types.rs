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

use saturn_v_ir::{
    ConstraintKind, ConstraintWeight, Expr, QueryTerm, RelationIO, RelationKind, StructuredType,
    Value,
};
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
    pub values: FixedValues,
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
pub struct Node {
    /// The [NodeInput] that produces input tuples to this node.
    pub input: NodeInput,

    /// A series of expressions to push the results of to the stack.
    pub push: Arc<[Expr]>,

    /// The filter expressions to evaluate after all new variables are pushed.
    pub filter: Arc<[Expr]>,

    /// Projects tuple elements within this node to outgoing tuples.
    pub project: Option<IndexList>,

    /// An optional, non-node output to direct this node's tuples towards.
    pub output: Option<NodeOutput>,
}

impl Node {
    pub fn constraint_type(self) -> Option<(ConstraintWeight, ConstraintKind)> {
        match self.output {
            Some(NodeOutput::Constraint { weight, kind, .. }) => Some((weight, kind)),
            _ => None,
        }
    }

    pub fn stratum(&self) -> u16 {
        match self.input {
            NodeInput::Antijoin { stratum, .. } => stratum,
            _ => 0,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
pub enum NodeInput {
    /// Loads tuples from a single, unprocessed node source.
    Source {
        /// The node source to load from.
        src: NodeSource,
    },

    /// Joins two sources together.
    Join {
        /// The left-hand node to join. Leftover terms come first.
        lhs: NodeSource,

        /// The right-hand node to join. Leftover terms come after left-hand terms.
        rhs: NodeSource,

        /// The number of terms starting from the front of each node to join.
        num: usize,
    },

    /// Merges two sources together.
    Merge {
        /// The left-hand node to merge.
        lhs: NodeSource,

        /// The right-hand node to merge.
        rhs: NodeSource,
    },

    /// Loads tuples from a node source but antijoins from a total query.
    Antijoin {
        /// The node source to load from.
        src: NodeSource,

        /// The negation stratum blocking this antijoin operation.
        ///
        /// Antijoin cannot proceed until this negation stratum is reached.
        stratum: u16,

        /// The key of the relation to antijoin.
        relation: Key<Relation>,

        /// A fully-populated query to select tuples from the source relation.
        query: Query,
    },
}

impl NodeInput {
    pub fn sources(self) -> Vec<NodeSource> {
        match self {
            NodeInput::Source { src } => vec![src],
            NodeInput::Merge { lhs, rhs } => vec![lhs, rhs],
            _ => vec![],
        }
    }

    pub fn join_lhs(self) -> Option<(NodeSource, usize)> {
        match self {
            NodeInput::Join { lhs, num, .. } => Some((lhs, num)),
            _ => None,
        }
    }

    pub fn join_rhs(self) -> Option<(NodeSource, usize)> {
        match self {
            NodeInput::Join { rhs, num, .. } => Some((rhs, num)),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
pub enum NodeSource {
    /// Loads tuples for this node from another node.
    Node {
        /// The key of the node to load from.
        node: Key<Node>,
    },

    /// Loads tuples for this node from a relation query.
    Relation {
        /// The key of the relation to load.
        relation: Key<Relation>,

        /// A query to constrain the loading by.
        query: Query,
    },
}

impl NodeSource {
    pub fn node(self) -> Option<Key<Node>> {
        match self {
            NodeSource::Node { node } => Some(node),
            _ => None,
        }
    }

    pub fn relation_mask(self) -> Option<(Key<Relation>, LoadMask)> {
        match self {
            NodeSource::Relation { relation, query } => {
                Some((relation, query.iter().map(Option::is_none).collect()))
            }
            _ => None,
        }
    }

    pub fn relation_head(self) -> Option<LoadHead> {
        match self {
            NodeSource::Relation { relation, query } => Some((
                relation,
                query.iter().map(Option::is_none).collect(),
                query.iter().flatten().cloned().collect(),
            )),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
pub enum NodeOutput {
    /// Stores a node's output tuples into a relation.
    Relation {
        /// The relation to store into.
        dst: Key<Relation>,

        /// The map from destination variables or values to relation elements.
        head: StoreHead,

        /// The kind of relation this is storing to.
        kind: RelationKind,
    },

    /// Stores a node's output tuples as a constraint.
    Constraint {
        /// The indices of the variables that the head is made up of.
        head: IndexList,

        /// The constraint's weight.
        weight: ConstraintWeight,

        /// The kind of constraint.
        kind: ConstraintKind,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
pub struct Relation {
    /// The unique name of this relation.
    pub name: String,

    /// The high-level type of the elements of this relation.
    pub ty: StructuredType,

    /// The kind of relation this is.
    pub kind: RelationKind,

    /// The IO of this relation.
    pub io: RelationIO,
}

impl Relation {
    /// Helper function to test if this relation is an output.
    pub fn is_output(&self) -> bool {
        matches!(self.io, RelationIO::Output)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
pub enum ConditionalLink {
    /// The conditional is unconditionally true.
    Unconditional,

    /// The conditional is unbound by any conditions.
    Free,

    /// The condiitonal is linked to a condition.
    Link(Condition),
}
