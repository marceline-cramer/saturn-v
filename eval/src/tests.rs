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
    self as ir, BinaryOpKind, CardinalityConstraintKind, Constraint, ConstraintKind,
    ConstraintWeight, Expr, Instruction, Program, QueryTerm, RelationKind, Rule, Type, Value,
};

use crate::{dataflow::DataflowRouters, load::Loader, solve::Solver, utils::run_pumps};

async fn run(loader: Loader<String>) {
    let config = timely::Config::thread();
    let routers = DataflowRouters::default();

    let workers = timely::execute(config, {
        let handle = tokio::runtime::Handle::current();
        let routers = routers.clone();
        move |worker| {
            let (input, output) = crate::dataflow::backend(worker, &routers);
            run_pumps(worker, handle.clone(), input, output);
        }
    })
    .expect("failed to start dataflows");

    std::thread::spawn(move || drop(workers));

    let mut facts = routers.facts_in.into_source();
    for fact in loader.facts {
        facts.insert(fact);
    }

    let mut relations = routers.relations_in.into_source();
    for relation in loader.relations.values() {
        relations.insert(relation.clone());
    }

    let mut nodes = routers.nodes_in.into_source();
    for node in loader.nodes {
        nodes.insert(node);
    }

    nodes.flush();

    facts.forget();
    relations.forget();
    nodes.forget();

    let (output_tx, output_rx) = flume::unbounded();

    let mut solver = Solver::new(
        routers.conditions_out.into_sink(),
        routers.clauses_out.into_sink(),
        routers.outputs_out.into_sink(),
        output_tx,
    );

    assert_eq!(solver.step().await, Some(()), "failed to step solver");
    assert_eq!(solver.solve(), Some(true), "unsat or unknown");
    solver.update_outputs();

    let mut batch = Vec::new();
    while let Ok(crate::utils::Update::Push(output, true)) = output_rx.recv() {
        batch.push(output);
    }

    eprintln!("outputs: {batch:#?}");
}

#[tokio::test]
async fn test_pick_one() {
    let mut program = Program::default();

    program.insert_relation(ir::Relation {
        ty: vec![Type::Integer],
        store: "Choice".to_string(),
        facts: (1..=10).map(|idx| vec![Value::Integer(idx)]).collect(),
        kind: RelationKind::Decision,
        is_output: true,
        rules: vec![],
    });

    program.constraints.push(Constraint {
        head: vec![],
        loaded: vec!["Choice".to_string()],
        vars: vec![Type::Integer],
        weight: ConstraintWeight::Hard,
        kind: ConstraintKind::Cardinality {
            kind: CardinalityConstraintKind::Only,
            threshold: 1,
        },
        instructions: Instruction::FromQuery {
            relation: 0,
            terms: vec![QueryTerm::Variable(0)],
        },
    });

    let loader = Loader::load_program(&program);
    run(loader).await;
}

#[tokio::test]
async fn test_pick_pairs() {
    let mut program = Program::default();

    program.insert_relation(ir::Relation {
        ty: vec![Type::Integer],
        store: "Base".to_string(),
        facts: vec![vec![Value::Integer(0)]],
        kind: RelationKind::Basic,
        is_output: false,
        rules: vec![Rule {
            vars: vec![Type::Integer, Type::Integer],
            head: vec![QueryTerm::Variable(0)],
            loaded: vec!["Base".to_string()],
            instructions: Instruction::Let {
                var: 0,
                expr: Expr::BinaryOp {
                    op: saturn_v_ir::BinaryOpKind::Add,
                    lhs: Arc::new(Expr::Variable(1)),
                    rhs: Arc::new(Expr::Value(Value::Integer(1))),
                },
                rest: Box::new(Instruction::Filter {
                    test: Expr::BinaryOp {
                        op: BinaryOpKind::Lt,
                        lhs: Arc::new(Expr::Variable(1)),
                        rhs: Arc::new(Expr::Value(Value::Integer(100))),
                    },
                    rest: Box::new(Instruction::FromQuery {
                        relation: 0,
                        terms: vec![QueryTerm::Variable(1)],
                    }),
                }),
            },
        }],
    });

    program.insert_relation(ir::Relation {
        ty: vec![Type::Integer, Type::Integer],
        store: "Pair".to_string(),
        facts: vec![],
        kind: RelationKind::Decision,
        is_output: true,
        rules: vec![Rule {
            vars: vec![Type::Integer, Type::Integer],
            head: vec![QueryTerm::Variable(0), QueryTerm::Variable(1)],
            loaded: vec!["Base".to_string()],
            instructions: Instruction::Filter {
                test: Expr::BinaryOp {
                    op: BinaryOpKind::Lt,
                    lhs: Arc::new(Expr::Variable(0)),
                    rhs: Arc::new(Expr::Variable(1)),
                },
                rest: Box::new(Instruction::Join {
                    lhs: Box::new(Instruction::FromQuery {
                        relation: 0,
                        terms: vec![QueryTerm::Variable(0)],
                    }),
                    rhs: Box::new(Instruction::FromQuery {
                        relation: 0,
                        terms: vec![QueryTerm::Variable(1)],
                    }),
                }),
            },
        }],
    });

    program.constraints.push(Constraint {
        head: vec![0],
        loaded: vec!["Pair".to_string()],
        vars: vec![Type::Integer, Type::Integer, Type::Integer],
        weight: ConstraintWeight::Hard,
        kind: saturn_v_ir::ConstraintKind::Cardinality {
            kind: CardinalityConstraintKind::Only,
            threshold: 1,
        },
        instructions: Instruction::Let {
            var: 0,
            expr: Expr::BinaryOp {
                op: BinaryOpKind::Div,
                lhs: Arc::new(Expr::Variable(1)),
                rhs: Arc::new(Expr::Value(Value::Integer(10))),
            },
            rest: Box::new(Instruction::FromQuery {
                relation: 0,
                terms: vec![QueryTerm::Variable(1), QueryTerm::Variable(2)],
            }),
        },
    });

    let loader = Loader::load_program(&program);
    run(loader).await;
}
