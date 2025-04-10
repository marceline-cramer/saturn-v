use std::sync::Arc;

use saturn_v_ir::{BinaryOpKind, Expr, InstructionKind, QueryTerm, Value};

use crate::{
    dataflow::DataflowRouters,
    load::Loader,
    solve::Solver,
    types::{Fact, Relation},
    utils::{run_pumps, Key},
};

async fn run(loader: Loader) {
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
    for fact in loader.relations {
        relations.insert(fact);
    }

    let mut nodes = routers.nodes_in.into_source();
    for fact in loader.nodes {
        nodes.insert(fact);
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

    assert_eq!(solver.step().await, Some(true), "unsat or timeout");
    solver.update_outputs();

    let mut batch = Vec::new();
    while let Ok(crate::utils::Update::Push(output, true)) = output_rx.recv() {
        batch.push(output);
    }

    eprintln!("outputs: {batch:#?}");
}

#[tokio::test]
async fn test_basic() {
    let relations = vec![
        Relation {
            discriminant: 0,
            is_decision: false,
            is_conditional: false,
            is_output: false,
        },
        Relation {
            discriminant: 1,
            is_decision: true,
            is_conditional: false,
            is_output: true,
        },
    ];

    let relation_keys: Vec<_> = relations.iter().map(Key::new).collect();

    let mut loader = Loader::new(relations);

    loader.add_fact(Fact {
        relation: relation_keys[0],
        values: vec![Value::Integer(1)].into(),
    });

    loader.store_relation(
        0,
        vec![QueryTerm::Variable(0)],
        &InstructionKind::Let(
            0,
            Expr::BinaryOp {
                op: saturn_v_ir::BinaryOpKind::Add,
                lhs: Arc::new(Expr::Variable(1)),
                rhs: Arc::new(Expr::Value(Value::Integer(1))),
            },
            Box::new(InstructionKind::Filter(
                Expr::BinaryOp {
                    op: BinaryOpKind::Lt,
                    lhs: Arc::new(Expr::Variable(1)),
                    rhs: Arc::new(Expr::Value(Value::Integer(100))),
                },
                Box::new(InstructionKind::FromQuery(0, vec![QueryTerm::Variable(1)])),
            )),
        ),
    );

    loader.store_relation(
        1,
        vec![QueryTerm::Variable(0), QueryTerm::Variable(1)],
        &InstructionKind::Filter(
            Expr::BinaryOp {
                op: BinaryOpKind::Lt,
                lhs: Arc::new(Expr::Variable(0)),
                rhs: Arc::new(Expr::Variable(1)),
            },
            Box::new(InstructionKind::Join(
                Box::new(InstructionKind::FromQuery(0, vec![QueryTerm::Variable(0)])),
                Box::new(InstructionKind::FromQuery(0, vec![QueryTerm::Variable(1)])),
            )),
        ),
    );

    run(loader).await;
}
