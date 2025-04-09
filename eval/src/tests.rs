use std::sync::Arc;

use saturn_v_ir::{Expr, InstructionKind, QueryTerm, Value};

use crate::{
    dataflow::DataflowRouters,
    load::Loader,
    types::{Fact, Relation},
    utils::{run_pumps, Key, OutputSink},
};

fn relations(num: u64) -> Vec<Relation> {
    (0..num)
        .map(|idx| Relation {
            discriminant: idx,
            is_decision: false,
            is_conditional: false,
            is_output: false,
        })
        .collect()
}

fn relation_key(idx: u64) -> Key<Relation> {
    Key::new(&Relation {
        discriminant: idx,
        is_decision: false,
        is_conditional: false,
        is_output: false,
    })
}

fn run(loader: Loader) -> OutputSink<Fact> {
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

    routers.facts_out.into_sink()
}

#[tokio::test]
async fn test_basic() {
    let mut loader = Loader::new(relations(2));

    for i in 1..=100 {
        loader.add_fact(Fact {
            relation: relation_key(0),
            values: vec![Value::Integer(i)].into(),
        });
    }

    loader.store_relation(
        1,
        vec![QueryTerm::Variable(0)],
        &InstructionKind::Let(
            0,
            Expr::BinaryOp {
                op: saturn_v_ir::BinaryOpKind::Mul,
                lhs: Arc::new(Expr::Variable(1)),
                rhs: Arc::new(Expr::Variable(1)),
            },
            Box::new(InstructionKind::FromQuery(0, vec![QueryTerm::Variable(1)])),
        ),
    );

    let mut facts_rx = run(loader);
    eprintln!(
        "batch of output facts: {:#?}",
        facts_rx.next_batch().await.unwrap()
    );
}
