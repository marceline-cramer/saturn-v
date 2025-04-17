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

use std::collections::HashSet;

use egglog::EGraph;
use indexmap::IndexSet;
use saturn_v_ir::{
    sexp::{self, Doc, Sexp},
    Instruction, Rule,
};

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

/// Defines the egglog representation to lower a rule.
pub fn extract_rule<R>(name: &str, rule: &Rule<R>) -> String {
    let instr = Instruction::Sink(
        HashSet::from_iter(0..(rule.vars.len() as i64)),
        Box::new(rule.instructions.clone()),
    );

    let assignment = sexp::doc_indent(
        sexp::doc_pair("let", Doc::text(name.to_string())),
        instr.to_doc(),
    );

    let run = Doc::text("(run 1000000)")
        .append(Doc::hardline())
        .append(format!("(query-extract {name})"));

    let mut out = String::new();

    assignment
        .append(Doc::hardline())
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

    fn filter_to_instructions(filter: Expr) -> Instruction {
        Instruction::Sink(
            filter
                .variable_deps()
                .iter()
                .map(|idx| *idx as i64)
                .collect(),
            Box::new(Instruction::Filter(filter, Box::new(Instruction::Noop))),
        )
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
            instructions: filter_to_instructions(filter),
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
            instructions: filter_to_instructions(filter),
            head: vec![QueryTerm::Variable(0)],
            loaded: vec![(), ()],
            vars: vec![Type::Integer],
        };

        eprintln!("{:#?}", test_rule(rule));
    }
}
