use egglog::EGraph;
use indexmap::IndexSet;
use pretty::RcDoc;
use saturn_v_ir::Rule;

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

/// Defines the egglog representation of a rule's filter.
pub fn define_rule<R>(name: &str, rule: &Rule<R>) -> String {
    let filter = RcDoc::text("(")
        .append("let")
        .append(RcDoc::space())
        .append(format!("{name}_filter"))
        .append(RcDoc::line().append(rule.filter.to_doc()).nest(4).group())
        .append(")");

    let mut out = String::new();
    filter.render_fmt(FORMAT_WIDTH, &mut out).unwrap();
    out
}

pub fn extract_rule<R>(name: &str, rule: &Rule<R>) -> String {
    let vars = rule
        .vars
        .iter()
        .enumerate()
        .map(|(idx, _ty)| idx.to_string());

    let vars = RcDoc::<()>::text("(")
        .append("set-of")
        .append(
            RcDoc::line()
                .append(RcDoc::intersperse(vars, RcDoc::line()))
                .nest(4)
                .group(),
        )
        .append(")");

    let filter = RcDoc::text("(")
        .append("Filter")
        .append(RcDoc::space())
        .append(format!("{name}_filter"))
        .append(RcDoc::space())
        .append("(Noop)")
        .append(")");

    let sink = RcDoc::text("(")
        .append("Sink")
        .append(RcDoc::space())
        .append(vars)
        .append(RcDoc::space())
        .append(filter)
        .append(")");

    let assignment = RcDoc::text("(")
        .append("let")
        .append(RcDoc::space())
        .append(name)
        .append(RcDoc::space())
        .append(sink)
        .append(")");

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
    use super::*;

    use chumsky::prelude::*;
    use saturn_v_ir::{sexp::Token, *};

    fn test_rule(rule: Rule<()>) -> InstructionKind {
        let name = "test_rule";
        let definition = define_rule(name, &rule);
        let extract = extract_rule(name, &rule);
        println!("{definition}");
        println!("{extract}");

        let full = format!("{definition}{extract}");
        let mut egg = init_lower_egraph();
        let msgs = egg.parse_and_run_program(None, &full).unwrap();

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

        InstructionKind::parser()
            .parse(stream)
            .expect("failed to parse")
    }

    #[test]
    fn basic_pretty_print() {
        let filter = Expr::BinaryOp {
            op: BinaryOpKind::And,
            lhs: Box::new(Expr::Load {
                relation: 0,
                query: vec![QueryTerm::Variable(1)],
            }),
            rhs: Box::new(Expr::BinaryOp {
                op: BinaryOpKind::Eq,
                lhs: Box::new(Expr::Variable(0)),
                rhs: Box::new(Expr::BinaryOp {
                    op: BinaryOpKind::Add,
                    lhs: Box::new(Expr::Variable(1)),
                    rhs: Box::new(Expr::Value(Value::Integer(1))),
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
            lhs: Box::new(Expr::Load {
                relation: 0,
                query: vec![QueryTerm::Variable(0)],
            }),
            rhs: Box::new(Expr::Load {
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
