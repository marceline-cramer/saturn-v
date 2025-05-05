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

use std::fmt::Debug;

use differential_dataflow::operators::{
    arrange::ArrangeByKey, iterate::Variable, Join, JoinCore, Reduce, Threshold,
};
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
        let facts = facts_in.to_collection(scope).map(Fact::relation_pair);
        let nodes = nodes_in.to_collection(scope).map(Key::pair);

        // generate the semantics
        let (facts, clauses, implies, conditions) = scope.iterative::<u32, _, _>(|scope| {
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

            // arrange tuples for all fetch operations
            let tuples_arranged = tuples.arrange_by_key();

            // extract left and right sides of join operation
            let join_lhs = nodes
                .flat_map(map_value(Node::join_lhs))
                .map_in_place(|(dst, (src, _num))| std::mem::swap(dst, src))
                .join_core(&tuples_arranged, |_, dst, tup| [join_slice(dst, tup)]);

            let join_rhs = nodes
                .flat_map(map_value(Node::join_rhs))
                .map_in_place(|(dst, (src, _num))| std::mem::swap(dst, src))
                .join_core(&tuples_arranged, |_, dst, tup| [join_slice(dst, tup)]);

            // select and merge sides of join source nodes
            let joined = join_lhs.join_map(&join_rhs, join);

            // extract the new tuples and clauses from a join
            let join = joined.map(key);
            let join_rhs = joined.flat_map(value);
            let join_clauses = join_rhs.map(key);
            let join_cond = join_rhs.map(value);

            // extract left and right sides of merge operation
            let merge_lhs = nodes
                .flat_map(map_value(Node::merge_lhs))
                .map_in_place(swap_in_place)
                .join_core(&tuples_arranged, |_, dst, tup| [(*dst, tup.clone())]);

            let merge_rhs = nodes
                .flat_map(map_value(Node::merge_rhs))
                .map_in_place(swap_in_place)
                .join_core(&tuples_arranged, |_, dst, tup| [(*dst, tup.clone())]);

            // merge sides
            let merge = merge_lhs.concat(&merge_rhs);

            // project operation
            let project = nodes
                .flat_map(map_value(Node::project))
                .map_in_place(|(dst, (src, _))| std::mem::swap(dst, src))
                .join_core(&tuples_arranged, |_, dst, tup| [project(dst, tup)]);

            // filter nodes
            let filter = nodes
                .flat_map(map_value(Node::filter))
                .map_in_place(|(dst, (src, _))| std::mem::swap(dst, src))
                .join_core(&tuples_arranged, |_, dst, tup| filter(dst, tup));

            // push nodes
            let push = nodes
                .flat_map(map_value(Node::push))
                .map_in_place(|(dst, (src, _))| std::mem::swap(dst, src))
                .join_core(&tuples_arranged, |_, rhs, val| [push(rhs, val)]);

            // load relation operation
            let load = nodes
                .flat_map(map_value(Node::load_relation))
                .map(|(node, (rel, _query))| (rel, node)) // TODO: hack
                .inspect(inspect("load input"))
                .join(&facts)
                .join(&relations)
                .map(value)
                .map(load);

            let load_cond = load.flat_map(value);
            let load = load.map(key);

            // store tuples to corresponding relations
            let stored = nodes
                .map(value)
                .flat_map(Node::store_relation)
                .join_core(&tuples_arranged, |_, dst, val| [store(dst, val)])
                .distinct();

            // collect constraint groups into clauses
            let constraint_type = nodes.flat_map(map_value(Node::constraint_type));

            let constraints = nodes
                .flat_map(map_value(Node::constraint_src))
                .map_in_place(|(dst, (src, _))| std::mem::swap(dst, src))
                .join_core(&tuples_arranged, |_, dst, tup| [constraint_map(dst, tup)])
                .reduce(constraint_reduce)
                .map(|((dst, _head), group)| (dst, group))
                .join_map(&constraint_type, constraint_clause);

            // combine all operations into new tuples
            tuples
                .set_concat(&join.concatenate([merge, project, filter, push, load]))
                .inspect(inspect("tuples"));

            // the keys of stored contain new tuples
            let store = stored.map(key).map(Fact::relation_pair);
            let new_implies = stored.flat_map(value);

            // all new clauses
            let new_clauses = join_clauses
                .concat(&constraints)
                .inspect(inspect("clauses"));

            // all new conditions
            let conditions = join_cond.concat(&load_cond);

            // return outputs of all extended collections
            (
                facts.set_concat(&store).inspect(inspect("facts")).leave(),
                clauses.set_concat(&new_clauses).leave(),
                implies
                    .set_concat(&new_implies)
                    .inspect(inspect("implies"))
                    .leave(),
                conditions.leave(),
            )
        });

        // make a map from implies to their relations
        let implies = implies
            .map(|(fact, condition)| (fact.relation, (fact, condition)))
            .arrange_by_key();

        // for a decision to be true, one of their dependents must also be true
        let decisions = implies
            .semijoin(
                &relations
                    .filter(|(_key, rel)| rel.kind == RelationKind::Decision)
                    .map(key),
            )
            .map(value)
            .reduce(decision_clause)
            .map(value);

        // conditional relations are collective ORs of their dependent conditions
        let conditional = implies
            .semijoin(
                &relations
                    .filter(|(_key, rel)| rel.kind == RelationKind::Conditional)
                    .map(key),
            )
            .map(value)
            .reduce(conditional_clause)
            .map(value);

        // filter output facts from all facts
        let outputs = facts
            .semijoin(&relations.filter(|(_key, rel)| rel.is_output).map(key))
            .map(value);

        // extend clauses
        let clauses = clauses
            .concatenate([decisions.map(key), conditional.map(key)])
            .inspect(inspect("clause"));

        // track instances of all new condition variables
        let conditions = conditions
            .concatenate([decisions.map(value), conditional.map(value)])
            .map(|cond| Key::new(&cond));

        // return inputs and outputs
        (
            relations_in.and(facts_in).and(nodes_in),
            routers
                .conditions_out
                .add_source(&conditions)
                .and(routers.clauses_out.add_source(&clauses))
                .and(routers.outputs_out.add_source(&outputs)),
        )
    })
}

#[derive(Clone, Default)]
pub struct DataflowRouters {
    pub relations_in: InputRouter<Relation>,
    pub facts_in: InputRouter<Fact>,
    pub nodes_in: InputRouter<Node>,
    pub conditions_out: OutputRouter<Key<Condition>>,
    pub clauses_out: OutputRouter<Clause>,
    pub outputs_out: OutputRouter<Fact>,
}

pub fn join_slice((dst, num): &(Key<Node>, usize), tuple: &Tuple) -> ((Key<Node>, Values), Tuple) {
    let num = *num;
    let prefix = tuple.values[..num].into();
    (
        (*dst, prefix),
        Tuple {
            values: tuple.values[num..].into(),
            condition: tuple.condition,
        },
    )
}

pub fn join(
    (dst, prefix): &(Key<Node>, Values),
    lhs: &Tuple,
    rhs: &Tuple,
) -> ((Key<Node>, Tuple), Option<(Clause, Condition)>) {
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
            let (out_key, out) = Key::pair(Condition {
                kind: ConditionKind::Node(*dst),
                values: values.clone().into(),
            });

            let clause = Clause::And {
                out: out_key,
                lhs,
                rhs,
            };

            (Some(out_key), Some((clause, out)))
        }
    };

    let tuple = Tuple { values, condition };
    ((*dst, tuple), clause)
}

pub fn project((dst, map): &(Key<Node>, IndexList), tuple: &Tuple) -> (Key<Node>, Tuple) {
    let condition = tuple.condition;
    let values = map.iter().map(|idx| tuple.values[*idx].clone()).collect();
    (*dst, Tuple { values, condition })
}

pub fn load(
    ((node, fact), relation): ((Key<Node>, Fact), Relation),
) -> ((Key<Node>, Tuple), Option<Condition>) {
    let condition_data = match relation.kind {
        RelationKind::Conditional | RelationKind::Decision => Some(Condition {
            kind: ConditionKind::Relation(fact.relation),
            values: fact.values.clone(),
        }),
        RelationKind::Basic => None,
    };

    let values = fact.values.to_vec();
    let condition = condition_data.as_ref().map(Key::new);
    ((node, Tuple { values, condition }), condition_data)
}

pub fn store(
    (relation, head): &(Key<Relation>, StoreHead),
    tuple: &Tuple,
) -> (Fact, Option<(Fact, Key<Condition>)>) {
    let values = head
        .iter()
        .map(|term| match term {
            QueryTerm::Value(val) => val.clone(),
            QueryTerm::Variable(idx) => tuple.values[*idx as usize].clone(),
        })
        .collect();

    let relation = *relation;
    let fact = Fact { relation, values };
    let implies = tuple.condition.map(|cond| (fact.clone(), cond));
    (fact, implies)
}

pub fn decision_clause(
    fact: &Fact,
    input: &[(&Key<Condition>, Diff)],
    output: &mut Vec<((Clause, Condition), Diff)>,
) {
    let (key, cond) = Key::pair(Condition {
        kind: ConditionKind::Relation(fact.relation),
        values: fact.values.clone(),
    });

    let clause = Clause::Decision {
        terms: input.iter().cloned().map(|(cond, _diff)| *cond).collect(),
        out: key,
    };

    output.push(((clause, cond), 1));
}

pub fn conditional_clause(
    fact: &Fact,
    input: &[(&Key<Condition>, Diff)],
    output: &mut Vec<((Clause, Condition), Diff)>,
) {
    let (key, cond) = Key::pair(Condition {
        kind: ConditionKind::Relation(fact.relation),
        values: fact.values.clone(),
    });

    let clause = Clause::Or {
        terms: input.iter().cloned().map(|(cond, _diff)| *cond).collect(),
        out: key,
    };

    output.push(((clause, cond), 1));
}

#[allow(unused_variables)]
pub fn inspect<T: Debug, D: Debug>(name: &str) -> impl for<'a> Fn(&'a (T, D, Diff)) {
    let name = name.to_string();
    move |update| {
        // eprintln!("{name}: {update:?}");
    }
}

pub fn filter((dst, expr): &(Key<Node>, Expr), tuple: &Tuple) -> Option<(Key<Node>, Tuple)> {
    match eval_expr(&tuple.values, expr) {
        Value::Boolean(false) => None,
        Value::Boolean(true) => Some((*dst, tuple.clone())),
        other => panic!("unexpected filter value: {other:?}"),
    }
}

pub fn push((dst, expr): &(Key<Node>, Expr), tuple: &Tuple) -> (Key<Node>, Tuple) {
    let mut tuple = tuple.to_owned();
    tuple.values.push(eval_expr(&tuple.values, expr));
    (*dst, tuple)
}

pub fn eval_expr(vals: &Values, expr: &Expr) -> Value {
    match expr {
        Expr::Variable(idx) => vals
            .get(*idx as usize)
            .expect("invalid variable index")
            .clone(),
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
    (dst, map): &(Key<Node>, IndexList),
    tuple: &Tuple,
) -> ((Key<Node>, Values), Option<Key<Condition>>) {
    let key = map.iter().map(|idx| tuple.values[*idx].clone()).collect();
    ((*dst, key), tuple.condition)
}

pub fn constraint_reduce(
    _key: &(Key<Node>, Values),
    input: &[(&Option<Key<Condition>>, Diff)],
    output: &mut Vec<(Vec<Key<Condition>>, Diff)>,
) {
    let mut terms = Vec::new();

    for (cond, _diff) in input {
        if let Some(cond) = cond.as_ref().to_owned() {
            terms.push(cond.to_owned());
        }
    }

    if !terms.is_empty() {
        output.push((terms, 1));
    }
}

#[allow(clippy::ptr_arg)]
pub fn constraint_clause(
    _dst: &Key<Node>,
    terms: &Vec<Key<Condition>>,
    (weight, kind): &(ConstraintWeight, ConstraintKind),
) -> Clause {
    Clause::ConstraintGroup {
        terms: terms.clone(),
        weight: weight.clone(),
        kind: kind.clone(),
    }
}
