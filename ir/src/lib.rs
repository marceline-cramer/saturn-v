use std::collections::HashMap;

use ordered_float::OrderedFloat;
use pretty::RcDoc;

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

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ConstraintKind {
    // TODO
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Relation<R> {
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
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Expr {
    Variable(usize),
    Value(Value),
    Load {
        relation: usize,
        query: Vec<QueryTerm>,
    },
    UnaryOp {
        op: UnaryOpKind,
        term: Box<Expr>,
    },
    BinaryOp {
        op: BinaryOpKind,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
}

impl Expr {
    pub fn to_doc(&self) -> RcDoc<()> {
        use Expr::*;
        match self {
            Variable(idx) => RcDoc::text("(")
                .append("Variable")
                .append(RcDoc::space())
                .append(idx.to_string())
                .append(")"),
            Value(val) => RcDoc::text("(")
                .append("Value")
                .append(RcDoc::space())
                .append(val.to_doc())
                .append(")"),
            Load { relation, query } => RcDoc::text("(")
                .append("Load")
                .append(RcDoc::space())
                .append(relation.to_string())
                .append(
                    RcDoc::intersperse(query.iter().map(|q| q.to_doc()), RcDoc::line())
                        .nest(4)
                        .group(),
                )
                .append(")"),
            UnaryOp { op, term } => RcDoc::text("(")
                .append("UnaryOp")
                .append(RcDoc::space())
                .append(op.to_doc())
                .append(RcDoc::line().append(term.to_doc()).nest(4).group())
                .append(")"),
            BinaryOp { op, lhs, rhs } => RcDoc::text("(")
                .append("BinaryOp")
                .append(RcDoc::space())
                .append(op.to_doc())
                .append(
                    RcDoc::line()
                        .append(lhs.to_doc())
                        .append(RcDoc::line())
                        .append(rhs.to_doc())
                        .nest(4)
                        .group(),
                )
                .append(")"),
        }
    }
}

/// Redundant operations (Sub, Neq, Gt, Ge) are not included. Use unary ops to
/// evaluate those.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
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
    pub fn to_doc(&self) -> RcDoc<()> {
        use BinaryOpKind::*;
        let kind = match self {
            Add => "Add",
            Mul => "Mul",
            Div => "Div",
            Concat => "Concat",
            And => "And",
            Or => "Or",
            Eq => "Eq",
            Lt => "Lt",
            Le => "Le",
        };

        RcDoc::text("(").append(kind).append(")")
    }
}
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum UnaryOpKind {
    Not,
    Negate,
}

impl UnaryOpKind {
    pub fn to_doc(&self) -> RcDoc<()> {
        use UnaryOpKind::*;
        let kind = match self {
            Not => "Not",
            Negate => "Negate",
        };

        RcDoc::text("(").append(kind).append(")")
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum QueryTerm {
    Variable(usize),
    Value(Value),
}

impl QueryTerm {
    pub fn to_doc(&self) -> RcDoc<()> {
        use QueryTerm::*;
        let (kind, val) = match self {
            Variable(idx) => ("QueryVariable", RcDoc::text(idx.to_string())),
            Value(val) => ("QueryValue", val.to_doc()),
        };

        RcDoc::text("(")
            .append(kind)
            .append(RcDoc::space())
            .append(val)
            .append(")")
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Value {
    Boolean(bool),
    Integer(i64),
    Real(OrderedFloat<f64>),
    Symbol(String),
    String(String),
}

impl Value {
    pub fn to_doc(&self) -> RcDoc<()> {
        use Value::*;
        let (kind, val) = match self {
            Boolean(val) => ("Boolean", val.to_string()),
            Integer(val) => ("Integer", val.to_string()),
            Real(val) => ("Real", val.to_string()),
            Symbol(val) => ("Symbol", format!("{val:?}")),
            String(val) => ("String", format!("{val:?}")),
        };

        RcDoc::text("(")
            .append(kind)
            .append(RcDoc::space())
            .append(val)
            .append(")")
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;

    #[test]
    fn basic_pretty_print() {
        let expr = Expr::BinaryOp {
            op: BinaryOpKind::Eq,
            lhs: Box::new(Expr::Variable(0)),
            rhs: Box::new(Expr::BinaryOp {
                op: BinaryOpKind::Add,
                lhs: Box::new(Expr::Variable(1)),
                rhs: Box::new(Expr::Value(Value::Integer(1))),
            }),
        };

        let mut out = Vec::new();
        expr.to_doc().render(40, &mut out).unwrap();
        let out = String::from_utf8(out).unwrap();
        println!("{out}");
    }
}
