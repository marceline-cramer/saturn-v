// Copyright (C) 2025-2026 Marceline Cramer
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

use chumsky::prelude::*;
use egglog::EGraph;
use indexmap::IndexSet;
use saturn_v_ir::{
    sexp::{self, Doc, Sexp, Token},
    Instruction, RuleBody,
};
use thread_local::ThreadLocal;
use tracing::{debug, trace};

pub type RelationTable<R> = IndexSet<R>;

pub const FORMAT_WIDTH: usize = 80;

pub static EGGLOG_LOWER_SRC: &str = include_str!("lower.egg");

/// Initilizes an e-graph loaded with the lowering code.
pub fn init_lower_egraph() -> EGraph {
    static BASE_EGRAPH: ThreadLocal<EGraph> = ThreadLocal::new();

    BASE_EGRAPH
        .get_or(|| {
            let mut graph = EGraph::default();
            graph
                .parse_and_run_program(None, EGGLOG_LOWER_SRC)
                .expect("failed to load check.egg");
            graph
        })
        .clone()
}

/// Defines the egglog representation to lower a rule body.
pub fn extract_rule_body<R>(name: &str, rule: &RuleBody<R>) -> String {
    let assignment = sexp::doc_indent(
        sexp::doc_pair("let", Doc::text(name.to_string())),
        rule.instructions.to_doc(),
    );

    let run = Doc::text("(run 1000000)")
        .append(Doc::hardline())
        .append(format!("(extract {name})"));

    let mut out = String::new();

    assignment
        .append(Doc::hardline())
        .append(run)
        .render_fmt(FORMAT_WIDTH, &mut out)
        .unwrap();

    trace!("extracting rule body: {out}");

    out
}

/// Actually runs the computation to lower a rule body.
pub fn lower_rule_body<R>(rule: RuleBody<R>) -> RuleBody<R> {
    let name = "test_rule";
    let extract = extract_rule_body(name, &rule);

    let start = std::time::Instant::now();
    let mut egg = init_lower_egraph();
    let msgs = egg.parse_and_run_program(None, &extract).unwrap();
    debug!("lowered rule body in {:?}", start.elapsed());

    for (idx, msg) in msgs.iter().enumerate() {
        trace!("egglog output #{idx}: {msg}");
    }

    // first message is empty, second is result
    let output = msgs[1].to_string();

    // lexing should never fail
    let tokens = Token::lexer()
        .parse(&output)
        .into_result()
        .expect("failed to lex");

    let stream = chumsky::input::IterInput::new(
        tokens
            .clone()
            .into_iter()
            .enumerate()
            .map(|(idx, tok)| (tok, (idx..idx).into())),
        (tokens.len()..tokens.len()).into(),
    );

    // parsing egglog output should never fail
    let instructions = Instruction::parser()
        .parse(stream)
        .into_result()
        .expect("failed to parse");

    // return lowered body
    RuleBody {
        instructions,
        ..rule
    }
}

#[cfg(test)]
pub mod tests {
    use std::sync::Arc;

    use super::*;

    use saturn_v_ir::*;

    fn filter_to_instructions(test: Expr) -> Instruction {
        Instruction::Sink {
            vars: test.variable_deps(),
            rest: Box::new(Instruction::Filter {
                test,
                rest: Box::new(Instruction::Noop),
            }),
        }
    }

    /// Recursively collects every `Filter.test` expression in an instruction tree.
    fn collect_filter_tests(instr: &Instruction) -> Vec<Expr> {
        fn go(instr: &Instruction, out: &mut Vec<Expr>) {
            match instr {
                Instruction::Noop | Instruction::FromQuery { .. } => {}
                Instruction::Sink { rest, .. } => go(rest, out),
                Instruction::Filter { test, rest } => {
                    out.push(test.clone());
                    go(rest, out);
                }
                Instruction::Let { rest, .. } => go(rest, out),
                Instruction::Antijoin { rest, .. } => go(rest, out),
                Instruction::Merge { lhs, rhs } | Instruction::Join { lhs, rhs } => {
                    go(lhs, out);
                    go(rhs, out);
                }
            }
        }

        let mut out = Vec::new();
        go(instr, &mut out);
        out
    }

    /// Flattens a nested `Or` expression tree into its non-`Or` leaves.
    fn collect_or_leaves(expr: &Expr, out: &mut Vec<Expr>) {
        match expr {
            Expr::BinaryOp {
                op: BinaryOpKind::Or,
                lhs,
                rhs,
            } => {
                collect_or_leaves(lhs, out);
                collect_or_leaves(rhs, out);
            }
            other => out.push(other.clone()),
        }
    }

    /// Converts a list of expressions into a set for order-insensitive comparison.
    fn expr_set(exprs: impl IntoIterator<Item = Expr>) -> std::collections::HashSet<Expr> {
        exprs.into_iter().collect()
    }

    /// Lowers a single filter expression and returns the lowered instruction tree.
    fn lower_filter_expr(expr: Expr) -> Instruction {
        let rule = RuleBody::<()> {
            instructions: filter_to_instructions(expr),
            loaded: vec![],
            vars: vec![],
        };

        lower_rule_body(rule).instructions
    }

    /// Asserts `actual` and `expected` contain the same expressions (ignoring order).
    fn assert_filter_tests_equal(actual: &[Expr], expected: &[Expr]) {
        let actual_set = expr_set(actual.to_vec());
        let expected_set = expr_set(expected.to_vec());
        assert_eq!(actual_set, expected_set);
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

        let rule = RuleBody::<()> {
            instructions: filter_to_instructions(filter),
            loaded: vec![()],
            vars: vec![Type::Integer, Type::Integer],
        };

        eprintln!("{:#?}", lower_rule_body(rule));
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

        let rule = RuleBody::<()> {
            instructions: filter_to_instructions(filter),
            loaded: vec![(), ()],
            vars: vec![Type::Integer],
        };

        eprintln!("{:#?}", lower_rule_body(rule));
    }

    #[test]
    fn and_children_right_nested_sets() {
        let a = Arc::new(Expr::Value(Value::Integer(1)));
        let b = Arc::new(Expr::Value(Value::Integer(2)));
        let c = Arc::new(Expr::Value(Value::Integer(3)));

        // a AND (b AND c)
        let expr = Expr::BinaryOp {
            op: BinaryOpKind::And,
            lhs: a.clone(),
            rhs: Arc::new(Expr::BinaryOp {
                op: BinaryOpKind::And,
                lhs: b.clone(),
                rhs: c.clone(),
            }),
        };

        let lowered = lower_filter_expr(expr);
        let tests = collect_filter_tests(&lowered);
        assert_filter_tests_equal(
            &tests,
            &[
                Expr::Value(Value::Integer(1)),
                Expr::Value(Value::Integer(2)),
                Expr::Value(Value::Integer(3)),
            ],
        );
    }

    #[test]
    fn and_children_left_nested_sets() {
        let a = Arc::new(Expr::Value(Value::Integer(1)));
        let b = Arc::new(Expr::Value(Value::Integer(2)));
        let c = Arc::new(Expr::Value(Value::Integer(3)));

        // (a AND b) AND c
        let expr = Expr::BinaryOp {
            op: BinaryOpKind::And,
            lhs: Arc::new(Expr::BinaryOp {
                op: BinaryOpKind::And,
                lhs: a.clone(),
                rhs: b.clone(),
            }),
            rhs: c.clone(),
        };

        let lowered = lower_filter_expr(expr);
        let tests = collect_filter_tests(&lowered);
        assert_filter_tests_equal(
            &tests,
            &[
                Expr::Value(Value::Integer(1)),
                Expr::Value(Value::Integer(2)),
                Expr::Value(Value::Integer(3)),
            ],
        );
    }

    #[test]
    fn and_children_mixed_order_sets() {
        let a = Arc::new(Expr::Value(Value::Integer(1)));
        let b = Arc::new(Expr::Value(Value::Integer(2)));
        let c = Arc::new(Expr::Value(Value::Integer(3)));

        // a AND (c AND b)
        let expr = Expr::BinaryOp {
            op: BinaryOpKind::And,
            lhs: a.clone(),
            rhs: Arc::new(Expr::BinaryOp {
                op: BinaryOpKind::And,
                lhs: c.clone(),
                rhs: b.clone(),
            }),
        };

        let lowered = lower_filter_expr(expr);
        let tests = collect_filter_tests(&lowered);
        assert_filter_tests_equal(
            &tests,
            &[
                Expr::Value(Value::Integer(1)),
                Expr::Value(Value::Integer(2)),
                Expr::Value(Value::Integer(3)),
            ],
        );
    }

    #[test]
    fn or_children_sets_consistent() {
        // Build a right-nested OR and ensure the lowered instructions include all children
        let expr = Expr::BinaryOp {
            op: BinaryOpKind::Or,
            lhs: Arc::new(Expr::Value(Value::Integer(10))),
            rhs: Arc::new(Expr::BinaryOp {
                op: BinaryOpKind::Or,
                lhs: Arc::new(Expr::Value(Value::Integer(20))),
                rhs: Arc::new(Expr::Value(Value::Integer(30))),
            }),
        };

        let rule = RuleBody::<()> {
            instructions: filter_to_instructions(expr),
            loaded: vec![],
            vars: vec![],
        };

        let lowered = lower_rule_body(rule).instructions;

        let tests = collect_filter_tests(&lowered);
        let mut leaves = Vec::new();
        for test in &tests {
            collect_or_leaves(test, &mut leaves);
        }

        assert_filter_tests_equal(
            &leaves,
            &[
                Expr::Value(Value::Integer(10)),
                Expr::Value(Value::Integer(20)),
                Expr::Value(Value::Integer(30)),
            ],
        );
    }
}
