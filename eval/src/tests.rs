use std::sync::Arc;

use saturn_v_ir::{Expr, InstructionKind, QueryTerm, Value};

use crate::{
    load::Loader,
    types::{Fact, Relation},
    utils::{run_pumps, InputRouter, Key, OutputRouter, OutputSink},
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

    let relations_in = InputRouter::default();
    let facts_in = InputRouter::default();
    let nodes_in = InputRouter::default();
    let variables_out = OutputRouter::default();
    let clauses_out = OutputRouter::default();
    let facts_out = OutputRouter::default();

    let workers = timely::execute(config, {
        let handle = tokio::runtime::Handle::current();
        let relations_in = relations_in.clone();
        let facts_in = facts_in.clone();
        let nodes_in = nodes_in.clone();
        let facts_out = facts_out.clone();
        move |worker| {
            let (input, output) = crate::dataflow::backend(
                worker,
                &relations_in,
                &facts_in,
                &nodes_in,
                &variables_out,
                &clauses_out,
                &facts_out,
            );

            run_pumps(worker, handle.clone(), input, output);
        }
    })
    .expect("failed to start dataflows");

    std::thread::spawn(move || drop(workers));

    let mut facts = facts_in.into_source();
    for fact in loader.facts {
        facts.insert(fact);
    }

    let mut relations = relations_in.into_source();
    for fact in loader.relations {
        relations.insert(fact);
    }

    let mut nodes = nodes_in.into_source();
    for fact in loader.nodes {
        nodes.insert(fact);
    }

    nodes.flush();

    facts.forget();
    relations.forget();
    nodes.forget();

    facts_out.into_sink()
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
