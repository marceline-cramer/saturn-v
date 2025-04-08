use differential_dataflow::operators::{iterate::Variable, Join, Reduce, Threshold};
use timely::{communication::Allocator, dataflow::Scope, order::Product, worker::Worker};

use crate::{
    types::{Clause, Condition, ConditionKind, Fact, IndexList, Node, Relation, Tuple, Values},
    utils::*,
};

pub fn backend(
    worker: &mut Worker<Allocator>,
    relations_in: &InputRouter<Relation>,
    facts_in: &InputRouter<Fact>,
    nodes_in: &InputRouter<Node>,
    variables_out: &OutputRouter<Condition>,
    clauses_out: &OutputRouter<Clause>,
    facts_out: &OutputRouter<Fact>,
) -> (impl PumpInput, impl PumpOutput) {
    worker.dataflow(|scope| {
        // enter inputs into context
        let mut relations_in = relations_in.add_sink();
        let mut facts_in = facts_in.add_sink();
        let mut nodes_in = nodes_in.add_sink();

        let relations = relations_in.to_collection(scope).map(Key::pair);

        let facts = facts_in
            .to_collection(scope)
            .map(|fact| (fact.relation, fact));

        let nodes = nodes_in.to_collection(scope).map(Key::pair);

        let inputs = relations_in.and(facts_in).and(nodes_in);

        // generate the semantics
        let (facts, clauses, implies) = scope.iterative::<u32, _, _>(|scope| {
            // enter inputs into iterative scope
            let relations = relations.enter(scope);
            let facts = facts.enter(scope);
            let nodes = nodes.enter(scope);

            // initialize iterative variables and state
            let step = Product::new(Default::default(), 1);
            let facts = Variable::new_from(facts, step);
            let tuples = Variable::new(scope, step);
            let clauses = Variable::new(scope, step);
            let implies = Variable::new(scope, step);

            // extract left and right sides of join operation
            let join_lhs = nodes
                .flat_map(map_value(Node::join_lhs))
                .map(|(dst, (src, num))| (src, (dst, num)))
                .join(&tuples)
                .map(value)
                .map(join_slice);

            let join_rhs = nodes
                .flat_map(map_value(Node::join_rhs))
                .map(|(dst, (src, num))| (src, (dst, num)))
                .join(&tuples)
                .map(value)
                .map(join_slice);

            // select and merge sides of join source nodes
            let joined = join_lhs.join(&join_rhs).map(join);

            // extract the new tuples and clauses from a join
            let join = joined.map(key);
            let join_clauses = joined.flat_map(value);

            // project operation
            let project_src = nodes.flat_map(map_value(Node::project_src)).map(swap);
            let project_map = nodes.flat_map(map_value(Node::project_map));

            // join together project targets and rearrange values
            let project = project_src
                .join(&tuples)
                .map(value)
                .join(&project_map)
                .map(project);

            // load relation operation
            let load = nodes
                .flat_map(map_value(Node::load_relation))
                .map(swap)
                .join(&facts)
                .join(&relations)
                .map(value)
                .map(load);

            // combine all operations into new tuples
            let new_tuples = join.concat(&project).concat(&load).distinct();
            tuples.set_concat(&new_tuples);

            // store new tuples to corresponding relations
            let stored = nodes
                .map(value)
                .flat_map(Node::store_relation)
                .join(&new_tuples)
                .map(value)
                .map(store)
                .distinct();

            // the keys of stored contain new tuples
            let store = stored.map(key);
            let new_implies = stored.flat_map(value);

            // return outputs of all extended collections
            (
                facts.set_concat(&store).leave().map(value),
                clauses.set_concat(&join_clauses).leave(),
                implies.set_concat(&new_implies).leave(),
            )
        });

        // make a map from implies to their relations
        let implies = implies.map(|(fact, condition)| (fact.relation, (fact, condition)));

        // for a decision to be true, one of their dependents must also be true
        let decisions = implies
            .semijoin(&relations.filter(|(_key, rel)| rel.is_decision).map(key))
            .map(value)
            .reduce(decision)
            .map(value);

        // conditional relations are collective ORs of their dependent conditions
        let conditional = implies
            .semijoin(&relations.filter(|(_key, rel)| rel.is_conditional).map(key))
            .map(value)
            .reduce(conditional)
            .map(value);

        // extend clauses
        let clauses = clauses.concatenate([decisions, conditional]).distinct();

        // track instances of all condition variables
        let variables = clauses.flat_map(Clause::into_conditions).distinct();

        // return inputs and outputs
        let outputs = variables_out
            .add_source(&variables)
            .and(clauses_out.add_source(&clauses))
            .and(facts_out.add_source(&facts));

        (inputs, outputs)
    })
}

pub fn join_slice(
    ((dst, num), mut tuple): ((Key<Node>, usize), Tuple),
) -> ((Key<Node>, Values), Tuple) {
    let prefix = tuple.values[..num].into();
    tuple.values = tuple.values[num..].into();
    ((dst, prefix), tuple)
}

pub fn join(
    ((dst, prefix), (lhs, rhs)): ((Key<Node>, Values), (Tuple, Tuple)),
) -> ((Key<Node>, Tuple), Option<Clause>) {
    let values: Values = prefix
        .iter()
        .chain(lhs.values.iter())
        .chain(rhs.values.iter())
        .cloned()
        .collect();

    let (condition, clause) = match (lhs.condition, rhs.condition) {
        (None, None) => (None, None),
        (Some(lhs), None) => (Some(lhs), None),
        (None, Some(rhs)) => (Some(rhs), None),
        (Some(lhs), Some(rhs)) => {
            let out = Condition {
                kind: ConditionKind::Node(dst),
                values: values.clone(),
            };

            let clause = Clause::And {
                lhs,
                rhs,
                out: out.clone(),
            };

            (Some(out), Some(clause))
        }
    };

    let tuple = Tuple { values, condition };
    ((dst, tuple), clause)
}

pub fn project((dst, (tuple, map)): (Key<Node>, (Tuple, IndexList))) -> (Key<Node>, Tuple) {
    let condition = tuple.condition;
    let values = map.iter().map(|idx| tuple.values[*idx].clone()).collect();
    (dst, Tuple { values, condition })
}

pub fn load(((node, fact), relation): ((Key<Node>, Fact), Relation)) -> (Key<Node>, Tuple) {
    let values = fact.values;

    let condition = if relation.is_conditional || relation.is_decision {
        Some(Condition {
            kind: ConditionKind::Relation(fact.relation),
            values: values.clone(),
        })
    } else {
        None
    };

    (node, Tuple { values, condition })
}

pub fn store(
    ((relation, map), tuple): ((Key<Relation>, IndexList), Tuple),
) -> ((Key<Relation>, Fact), Option<(Fact, Condition)>) {
    let values = map.iter().map(|idx| tuple.values[*idx].clone()).collect();
    let fact = Fact { relation, values };
    let implies = tuple.condition.map(|cond| (fact.clone(), cond));
    ((relation, fact), implies)
}

pub fn decision(fact: &Fact, input: &[(&Condition, Diff)], output: &mut Vec<(Clause, Diff)>) {
    let clause = Clause::Decision {
        terms: input
            .iter()
            .map(|(cond, _diff)| cond.clone().clone())
            .collect(),
        out: Condition {
            kind: ConditionKind::Relation(fact.relation),
            values: fact.values.clone(),
        },
    };

    output.push((clause, 1));
}

pub fn conditional(fact: &Fact, input: &[(&Condition, Diff)], output: &mut Vec<(Clause, Diff)>) {
    let clause = Clause::Or {
        terms: input
            .iter()
            .map(|(cond, _diff)| cond.clone().clone())
            .collect(),
        out: Condition {
            kind: ConditionKind::Relation(fact.relation),
            values: fact.values.clone(),
        },
    };

    output.push((clause, 1));
}
