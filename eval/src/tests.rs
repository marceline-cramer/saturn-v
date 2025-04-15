use std::sync::Arc;

use saturn_v_ir::{
    self as ir, BinaryOpKind, Constraint, ConstraintKind, ConstraintWeight, Expr, Instruction,
    Program, QueryTerm, RelationKind, Rule, Type, Value,
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

    assert_eq!(solver.step().await, Some(true), "unsat or timeout");
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
        kind: ConstraintKind::One,
        instructions: Instruction::FromQuery(0, vec![QueryTerm::Variable(0)]),
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
            instructions: Instruction::Let(
                0,
                Expr::BinaryOp {
                    op: saturn_v_ir::BinaryOpKind::Add,
                    lhs: Arc::new(Expr::Variable(1)),
                    rhs: Arc::new(Expr::Value(Value::Integer(1))),
                },
                Box::new(Instruction::Filter(
                    Expr::BinaryOp {
                        op: BinaryOpKind::Lt,
                        lhs: Arc::new(Expr::Variable(1)),
                        rhs: Arc::new(Expr::Value(Value::Integer(100))),
                    },
                    Box::new(Instruction::FromQuery(0, vec![QueryTerm::Variable(1)])),
                )),
            ),
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
            instructions: Instruction::Filter(
                Expr::BinaryOp {
                    op: BinaryOpKind::Lt,
                    lhs: Arc::new(Expr::Variable(0)),
                    rhs: Arc::new(Expr::Variable(1)),
                },
                Box::new(Instruction::Join(
                    Box::new(Instruction::FromQuery(0, vec![QueryTerm::Variable(0)])),
                    Box::new(Instruction::FromQuery(0, vec![QueryTerm::Variable(1)])),
                )),
            ),
        }],
    });

    program.constraints.push(Constraint {
        head: vec![0],
        loaded: vec!["Pair".to_string()],
        vars: vec![Type::Integer, Type::Integer, Type::Integer],
        weight: ConstraintWeight::Hard,
        kind: saturn_v_ir::ConstraintKind::One,
        instructions: Instruction::Let(
            0,
            Expr::BinaryOp {
                op: BinaryOpKind::Div,
                lhs: Arc::new(Expr::Variable(1)),
                rhs: Arc::new(Expr::Value(Value::Integer(10))),
            },
            Box::new(Instruction::FromQuery(
                0,
                vec![QueryTerm::Variable(1), QueryTerm::Variable(2)],
            )),
        ),
    });

    let loader = Loader::load_program(&program);
    run(loader).await;
}
