use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use indexmap::IndexSet;
use ordered_float::OrderedFloat;
use pretty::RcDoc;
use serde::{Deserialize, Serialize};
use strum::EnumString;

pub mod sexp;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InstructionKind {
    Noop,
    Sink(HashSet<i64>, Box<Self>),
    Filter(Expr, Box<Self>),
    FromQuery(i64, Vec<QueryTerm>),
    Let(i64, Expr, Box<Self>),
    Merge(Box<Self>, Box<Self>),
    Join(Box<Self>, Box<Self>),
}

pub struct Program<R> {
    pub constraints: Vec<Constraint<R>>,
    pub relations: HashMap<R, Relation<R>>,
}

pub struct Constraint<R> {
    /// The desugared body of this rule.
    pub filter: Expr,

    /// The variables to group this constraint over.
    pub head: Vec<usize>,

    /// The lookups for custom relation types loaded by the filter.
    pub loaded: Vec<R>,

    /// The kind of constraint that this is.
    pub kind: ConstraintKind,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
pub enum ConstraintKind {
    // TODO
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Relation<R> {
    /// The relation's type.
    pub ty: Vec<Type>,

    /// The custom relation data that this relation stores to.
    pub store: R,

    /// Each rule that stores to this relation.
    pub rules: Vec<Rule<R>>,

    /// Whether or not this relation is a decision.
    pub is_decision: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Rule<R> {
    /// The desugared body of this rule.
    pub filter: Expr,

    /// Maps from the variables in the filter to query terms to store in the
    /// relation this rule is for.
    pub head: Vec<QueryTerm>,

    /// The lookups for custom relation types loaded by the filter.
    pub loaded: Vec<R>,

    /// The type of each variable.
    pub vars: Vec<Type>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
pub enum Expr {
    Variable(usize),
    Value(Value),
    Load {
        relation: usize,
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
    pub fn map_variables(self, map: &IndexSet<usize>) -> Self {
        use Expr::*;
        match self {
            Variable(idx) => Variable(map.get_index_of(&idx).unwrap()),
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

#[derive(
    Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, EnumString, Deserialize, Serialize,
)]
pub enum UnaryOpKind {
    Not,
    Negate,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
pub enum QueryTerm {
    Variable(usize),
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
