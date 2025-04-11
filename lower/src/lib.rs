use std::collections::HashSet;

use egglog::EGraph;
use indexmap::IndexSet;
use pretty::RcDoc;
use saturn_v_ir::{sexp::Sexp, Instruction, Rule};

pub type RelationTable<R> = IndexSet<R>;

pub const FORMAT_WIDTH: usize = 80;

pub static EGGLOG_LOWER_SRC: &str = include_str!("lower.egg");

/// Initilizes an e-graph loaded with the lowering code.
pub fn init_lower_egraph() -> EGraph {
    // TODO: memoize this despite egraph not being sync
    let mut graph = EGraph::default();
    graph
        .parse_and_run_program(None, EGGLOG_LOWER_SRC)
        .expect("failed to load check.egg");
    graph
}

/// Defines the egglog representation to check a rule.
pub fn extract_rule<R>(name: &str, rule: &Rule<R>) -> String {
    let instr = Instruction::Sink(
        HashSet::from_iter(0..(rule.vars.len() as i64)),
        Box::new(Instruction::Filter(
            rule.filter.clone(),
            Box::new(Instruction::Noop),
        )),
    );

    let assignment = RcDoc::text("(")
        .append("let")
        .append(RcDoc::space())
        .append(name.to_string())
        .append(RcDoc::line())
        .append(instr.to_doc())
        .append(")")
        .group();

    let run = RcDoc::text("(run 1000000)")
        .append(RcDoc::hardline())
        .append(format!("(query-extract {name})"));

    let mut out = String::new();

    assignment
        .append(RcDoc::hardline())
        .append(run)
        .render_fmt(FORMAT_WIDTH, &mut out)
        .unwrap();

    out
}

#[cfg(test)]
pub mod tests {
    use std::sync::Arc;

    use super::*;

    use chumsky::prelude::*;
    use saturn_v_ir::{sexp::Token, *};

    fn test_rule(rule: Rule<()>) -> Instruction {
        let name = "test_rule";
        let extract = extract_rule(name, &rule);
        println!("{extract}");
        let mut egg = init_lower_egraph();
        let msgs = egg.parse_and_run_program(None, &extract).unwrap();

        let output = &msgs[0];

        let tokens = Token::lexer()
            .parse(output.as_str())
            .expect("failed to lex");

        let stream = chumsky::Stream::from_iter(
            tokens.len()..tokens.len(),
            tokens
                .iter()
                .cloned()
                .enumerate()
                .map(|(idx, tok)| (tok, idx..idx)),
        );

        Instruction::parser()
            .parse(stream)
            .expect("failed to parse")
    }

    #[test]
    fn basic_pretty_print() {
        let filter = Expr::BinaryOp {
            op: BinaryOpKind::And,
            lhs: Arc::new(Expr::Load {
                relation: 0,
                query: vec![QueryTerm::Variable(1)],
            }),
            rhs: Arc::new(Expr::BinaryOp {
                op: BinaryOpKind::Eq,
                lhs: Arc::new(Expr::Variable(0)),
                rhs: Arc::new(Expr::BinaryOp {
                    op: BinaryOpKind::Add,
                    lhs: Arc::new(Expr::Variable(1)),
                    rhs: Arc::new(Expr::Value(Value::Integer(1))),
                }),
            }),
        };

        let rule = Rule::<()> {
            filter,
            head: vec![QueryTerm::Variable(0)],
            loaded: vec![()],
            vars: vec![Type::Integer, Type::Integer],
        };

        eprintln!("{:#?}", test_rule(rule));
    }

    #[test]
    fn relational_or() {
        let filter = Expr::BinaryOp {
            op: BinaryOpKind::Or,
            lhs: Arc::new(Expr::Load {
                relation: 0,
                query: vec![QueryTerm::Variable(0)],
            }),
            rhs: Arc::new(Expr::Load {
                relation: 1,
                query: vec![QueryTerm::Variable(0)],
            }),
        };

        let rule = Rule::<()> {
            filter,
            head: vec![QueryTerm::Variable(0)],
            loaded: vec![(), ()],
            vars: vec![Type::Integer],
        };

        eprintln!("{:#?}", test_rule(rule));
    }
}
