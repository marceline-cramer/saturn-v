use saturn_v_ir::{ConstraintKind, Expr, Value};
use serde::{Deserialize, Serialize};
use smallvec::SmallVec;

use crate::utils::Key;

pub type Values = SmallVec<[Value; 2]>;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
pub struct Fact {
    pub relation: Key<Relation>,
    pub values: Values,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
pub enum Clause {
    And {
        lhs: Condition,
        rhs: Condition,
        out: Condition,
    },
    AndNot {
        lhs: Condition,
        /// Negated.
        rhs: Condition,
        out: Condition,
    },
    Implies {
        term: Condition,
        out: Condition,
    },
    Or {
        terms: Vec<Condition>,
        out: Condition,
    },
    Decision {
        terms: Vec<Condition>,
        out: Condition,
    },
}

impl Clause {
    pub fn into_conditions(self) -> Vec<Condition> {
        use Clause::*;
        match self {
            And { lhs, rhs, out } => vec![lhs, rhs, out],
            AndNot { lhs, rhs, out } => vec![lhs, rhs, out],
            Implies { term, out } => vec![term, out],
            Or { mut terms, out } => {
                terms.push(out);
                terms
            }
            Decision { mut terms, out } => {
                terms.push(out);
                terms
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
pub struct Tuple {
    pub values: Values,
    pub condition: Option<Condition>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
pub struct Condition {
    pub kind: ConditionKind,
    pub values: Values,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
pub enum ConditionKind {
    Node(Key<Node>),
    Relation(Key<Relation>),
}

pub type IndexList = SmallVec<[usize; 8]>;

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

    /// Projects (rearranges) a node's terms.
    ///
    /// Can also unload nodes.
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
        resource: Key<Relation>,
    },

    /// Stores a node's contents into a relation.
    StoreRelation {
        /// The node to load terms from.
        src: Key<Node>,

        /// The relation to store into.
        dst: Key<Relation>,

        /// The map from destination terms to source terms.
        map: IndexList,
    },

    /// Stores a node's contents as a constraint.
    Constraint {
        /// The node to load terms from.
        src: Key<Node>,

        /// The indices of the variables that the head is made up of.
        head: IndexList,

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

    pub fn project_src(self) -> Option<Key<Node>> {
        match self {
            Node::Project { src, .. } => Some(src),
            _ => None,
        }
    }

    pub fn project_map(self) -> Option<IndexList> {
        match self {
            Node::Project { map, .. } => Some(map),
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

    pub fn load_relation(self) -> Option<Key<Relation>> {
        match self {
            Node::LoadRelation { resource } => Some(resource),
            _ => None,
        }
    }

    pub fn store_relation(self) -> Option<(Key<Node>, (Key<Relation>, IndexList))> {
        match self {
            Node::StoreRelation { src, dst, map } => Some((src, (dst, map))),
            _ => None,
        }
    }

    pub fn constraint(self) -> Option<(Key<Node>, (IndexList, ConstraintKind))> {
        match self {
            Node::Constraint { src, unify, kind } => Some((src, (unify, kind))),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
pub struct Relation {
    /// Used to differentiate otherwise identically-defined relations.
    pub discriminant: u64,

    /// If this relation is a decision.
    pub is_decision: bool,

    /// If this relation is conditional.
    pub is_conditional: bool,

    /// If this relation is an output.
    pub is_output: bool,
}
