use std::fmt::Debug;

use differential_dataflow::operators::{iterate::Variable, Join, Reduce, Threshold};
use saturn_v_ir::*;
use timely::{communication::Allocator, dataflow::Scope, order::Product, worker::Worker};

use crate::{
    types::{
        Clause, Condition, ConditionKind, Fact, IndexList, Node, Relation, StoreHead, Tuple, Values,
    },
    utils::*,
};

pub fn backend(
    worker: &mut Worker<Allocator>,
    routers: &DataflowRouters,
) -> (impl PumpInput, impl PumpOutput) {
    worker.dataflow(|scope| {
        // enter inputs into context
        let mut relations_in = routers.relations_in.add_sink();
        let mut facts_in = routers.facts_in.add_sink();
        let mut nodes_in = routers.nodes_in.add_sink();

        let relations = relations_in.to_collection(scope).map(Key::pair);

        let facts = facts_in
            .to_collection(scope)
            .map(|fact| (fact.relation, fact));

        let nodes = nodes_in.to_collection(scope).map(Key::pair);

        let inputs = relations_in.and(facts_in).and(nodes_in);

        // generate the semantics
        let (tuples, facts, clauses, implies) = scope.iterative::<u32, _, _>(|scope| {
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

            // extract left and right sides of merge operation
            let merge_lhs = nodes
                .flat_map(map_value(Node::merge_lhs))
                .map(swap)
                .join(&tuples)
                .map(value);

            let merge_rhs = nodes
                .flat_map(map_value(Node::merge_rhs))
                .map(swap)
                .join(&tuples)
                .map(value);

            // merge sides
            let merge = merge_lhs.concat(&merge_rhs);

            // project operation
            let project_src = nodes.flat_map(map_value(Node::project_src)).map(swap);
            let project_map = nodes.flat_map(map_value(Node::project_map));

            // join together project targets and rearrange values
            let project = project_src
                .join(&tuples)
                .map(value)
                .join(&project_map)
                .map(project);

            // filter nodes
            let filter = nodes
                .flat_map(map_value(Node::filter))
                .map(|(dst, (src, expr))| (src, (dst, expr)))
                .join(&tuples)
                .map(value)
                .filter(filter)
                .map(|((dst, _expr), tuple)| (dst, tuple));

            // push nodes
            let push = nodes
                .flat_map(map_value(Node::push))
                .map(|(dst, (src, expr))| (src, (dst, expr)))
                .join(&tuples)
                .map(value)
                .map(push);

            // load relation operation
            let load = nodes
                .flat_map(map_value(Node::load_relation))
                .map(swap)
                .map(|((rel, _query), node)| (rel, node)) // TODO: hack
                .inspect(inspect("load input"))
                .join(&facts)
                .join(&relations)
                .map(value)
                .map(load);

            // combine all operations into new tuples
            let new_tuples = join
                .concat(&merge)
                .concat(&project)
                .concat(&filter)
                .concat(&push)
                .concat(&load)
                .distinct()
                .inspect(inspect("stored"));

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
                tuples
                    .set_concat(&new_tuples)
                    .inspect(inspect("tuples"))
                    .leave(),
                facts.set_concat(&store).inspect(inspect("facts")).leave(),
                clauses
                    .set_concat(&join_clauses)
                    .inspect(inspect("clauses"))
                    .leave(),
                implies
                    .set_concat(&new_implies)
                    .inspect(inspect("implies"))
                    .leave(),
            )
        });

        // make a map from implies to their relations
        let implies = implies.map(|(fact, condition)| (fact.relation, (fact, condition)));

        // for a decision to be true, one of their dependents must also be true
        let decisions = implies
            .semijoin(
                &relations
                    .filter(|(_key, rel)| rel.kind == RelationKind::Decision)
                    .map(key),
            )
            .map(value);

        // conditional relations are collective ORs of their dependent conditions
        let conditional = implies
            .semijoin(
                &relations
                    .filter(|(_key, rel)| rel.kind == RelationKind::Conditional)
                    .map(key),
            )
            .map(value);

        // filter output facts from all facts
        let outputs = facts
            .semijoin(&relations.filter(|(_key, rel)| rel.is_output).map(key))
            .map(value)
            .distinct();

        // collect constraint groups into clauses
        let constraint_type = nodes.flat_map(map_value(Node::constraint_type));

        let constraints = nodes
            .flat_map(map_value(Node::constraint_src))
            .map(|(dst, (src, map))| (src, (dst, map)))
            .join_map(&tuples, constraint_map)
            .reduce(constraint_reduce)
            .map(|((dst, _head), group)| (dst, group))
            .join_map(&constraint_type, constraint_clause);

        // extend clauses
        let clauses = clauses
            .concat(&decisions.reduce(decision_clause).map(value))
            .concat(&conditional.reduce(conditional_clause).map(value))
            .concat(&constraints)
            .distinct();

        // track instances of all condition variables
        let conditions = clauses
            .flat_map(Clause::into_conditions)
            .concat(
                &decisions
                    .concat(&conditional)
                    .map(key)
                    .concat(&outputs)
                    .map(Into::into),
            )
            .distinct();

        // return inputs and outputs
        let outputs = routers
            .conditions_out
            .add_source(&conditions)
            .and(routers.clauses_out.add_source(&clauses))
            .and(routers.outputs_out.add_source(&outputs));

        (inputs, outputs)
    })
}

#[derive(Clone, Default)]
pub struct DataflowRouters {
    pub relations_in: InputRouter<Relation>,
    pub facts_in: InputRouter<Fact>,
    pub nodes_in: InputRouter<Node>,
    pub conditions_out: OutputRouter<Condition>,
    pub clauses_out: OutputRouter<Clause>,
    pub outputs_out: OutputRouter<Fact>,
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

    let condition = match relation.kind {
        RelationKind::Conditional | RelationKind::Decision => Some(Condition {
            kind: ConditionKind::Relation(fact.relation),
            values: values.clone(),
        }),
        RelationKind::Basic => None,
    };

    (node, Tuple { values, condition })
}

pub fn store(
    ((relation, head), tuple): ((Key<Relation>, StoreHead), Tuple),
) -> ((Key<Relation>, Fact), Option<(Fact, Condition)>) {
    let values = head
        .into_iter()
        .map(|term| match term {
            QueryTerm::Value(val) => val,
            QueryTerm::Variable(idx) => tuple.values[idx].clone(),
        })
        .collect();

    let fact = Fact { relation, values };
    let implies = tuple.condition.map(|cond| (fact.clone(), cond));
    ((relation, fact), implies)
}

pub fn decision_clause(
    fact: &Fact,
    input: &[(&Condition, Diff)],
    output: &mut Vec<(Clause, Diff)>,
) {
    let clause = Clause::Decision {
        terms: input
            .iter()
            .cloned()
            .map(|(cond, _diff)| cond.clone())
            .collect(),
        out: Condition {
            kind: ConditionKind::Relation(fact.relation),
            values: fact.values.clone(),
        },
    };

    output.push((clause, 1));
}

pub fn conditional_clause(
    fact: &Fact,
    input: &[(&Condition, Diff)],
    output: &mut Vec<(Clause, Diff)>,
) {
    let clause = Clause::Or {
        terms: input
            .iter()
            .cloned()
            .map(|(cond, _diff)| cond.clone())
            .collect(),
        out: Condition {
            kind: ConditionKind::Relation(fact.relation),
            values: fact.values.clone(),
        },
    };

    output.push((clause, 1));
}

pub fn inspect<T: Debug, D: Debug>(name: &str) -> impl for<'a> Fn(&'a (T, D, Diff)) {
    let name = name.to_string();
    move |update| {
        // eprintln!("{name}: {update:?}");
    }
}

pub fn filter(((_dst, expr), tuple): &((Key<Node>, Expr), Tuple)) -> bool {
    match eval_expr(&tuple.values, expr) {
        Value::Boolean(test) => test,
        other => panic!("unexpected filter value: {other:?}"),
    }
}

pub fn push(((dst, expr), mut tuple): ((Key<Node>, Expr), Tuple)) -> (Key<Node>, Tuple) {
    tuple.values.push(eval_expr(&tuple.values, &expr));
    (dst, tuple)
}

pub fn eval_expr(vals: &Values, expr: &Expr) -> Value {
    match expr {
        Expr::Variable(idx) => vals.get(*idx).expect("invalid variable index").clone(),
        Expr::Value(val) => val.clone(),
        Expr::Load { .. } => unreachable!("eval expressions cannot load relations"),
        Expr::UnaryOp { op, term } => match (op, eval_expr(vals, term)) {
            (UnaryOpKind::Not, Value::Boolean(val)) => Value::Boolean(!val),
            (UnaryOpKind::Negate, Value::Integer(val)) => Value::Integer(-val),
            (UnaryOpKind::Negate, Value::Real(val)) => Value::Real(-val),
            other => panic!("invalid unary op: {other:?}"),
        },
        Expr::BinaryOp { op, lhs, rhs } => match (op, eval_expr(vals, lhs), eval_expr(vals, rhs)) {
            // integer arithmetic
            (BinaryOpKind::Add, Value::Integer(lhs), Value::Integer(rhs)) => {
                Value::Integer(lhs + rhs)
            }
            (BinaryOpKind::Mul, Value::Integer(lhs), Value::Integer(rhs)) => {
                Value::Integer(lhs * rhs)
            }
            (BinaryOpKind::Div, Value::Integer(lhs), Value::Integer(rhs)) => {
                Value::Integer(lhs / rhs)
            }

            // real arithmetic
            (BinaryOpKind::Add, Value::Real(lhs), Value::Real(rhs)) => Value::Real(lhs + rhs),
            (BinaryOpKind::Mul, Value::Real(lhs), Value::Real(rhs)) => Value::Real(lhs * rhs),
            (BinaryOpKind::Div, Value::Real(lhs), Value::Real(rhs)) => Value::Real(lhs / rhs),

            // string operators
            (BinaryOpKind::Concat, Value::String(mut lhs), Value::String(rhs)) => {
                lhs.push_str(&rhs);
                Value::String(lhs)
            }

            // logical operators
            (BinaryOpKind::And, Value::Boolean(lhs), Value::Boolean(rhs)) => {
                Value::Boolean(lhs && rhs)
            }
            (BinaryOpKind::Or, Value::Boolean(lhs), Value::Boolean(rhs)) => {
                Value::Boolean(lhs || rhs)
            }

            // comparisons
            (BinaryOpKind::Eq, lhs, rhs) if lhs.ty() == rhs.ty() => Value::Boolean(lhs == rhs),
            (BinaryOpKind::Lt, lhs, rhs) if lhs.ty() == rhs.ty() => Value::Boolean(lhs < rhs),
            (BinaryOpKind::Le, lhs, rhs) if lhs.ty() == rhs.ty() => Value::Boolean(lhs <= rhs),

            // everything else is invalid
            other => panic!("invalid binary op: {other:?}"),
        },
    }
}

pub fn constraint_map(
    _src: &Key<Node>,
    (dst, map): &(Key<Node>, IndexList),
    tuple: &Tuple,
) -> ((Key<Node>, Values), Option<Condition>) {
    let key = map.iter().map(|idx| tuple.values[*idx].clone()).collect();
    ((*dst, key), tuple.condition.clone())
}

pub fn constraint_reduce(
    _key: &(Key<Node>, Values),
    input: &[(&Option<Condition>, Diff)],
    output: &mut Vec<(Vec<Condition>, Diff)>,
) {
    let mut terms = Vec::new();

    for (cond, _diff) in input {
        if let Some(cond) = cond.clone() {
            terms.push(cond.clone());
        }
    }

    if !terms.is_empty() {
        output.push((terms, 1));
    }
}

pub fn constraint_clause(
    _dst: &Key<Node>,
    terms: &Vec<Condition>,
    (weight, kind): &(ConstraintWeight, ConstraintKind),
) -> Clause {
    Clause::ConstraintGroup {
        terms: terms.clone(),
        weight: weight.clone(),
        kind: kind.clone(),
    }
}
