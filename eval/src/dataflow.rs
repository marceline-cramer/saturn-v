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
    arrange::ArrangeByKey, iterate::Variable, Join, JoinCore, Reduce,
};
use saturn_v_ir::*;
use timely::{communication::Allocator, dataflow::Scope, order::Product, worker::Worker};

use crate::{
    types::{
        Condition, ConstraintGroup, Fact, FixedValues, Gate, IndexList, LoadHead, LoadMask, Node,
        Relation, StoreHead, Tuple, Values,
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
        let (gates, implies, outputs, constraints) = scope.iterative::<u32, _, _>(|scope| {
            // enter inputs into iterative scope
            let relations = relations.enter(scope);
            let facts = facts.enter(scope);
            let nodes = nodes.enter(scope);

            // initialize iterative variables and state
            let step = Product::new(Default::default(), 1);
            let facts = Variable::new_from(facts, step);
            let tuples = Variable::new(scope, step);

            // arrange tuples for all fetch operations
            let tuples_arranged = tuples.arrange_by_key();

            // arrange facts
            let facts_arranged = facts.arrange_by_key();

            // arrange relations
            let relations_arranged = relations.arrange_by_key();

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

            // extract the new tuples and gates from a join
            let join = joined.map(key);
            let join_gates = joined.flat_map(value);

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

            // filter output facts from all facts
            let outputs = facts_arranged
                .semijoin(&relations.filter(|(_key, rel)| rel.is_output).map(key))
                .map(value)
                .inspect(inspect("output"));

            // arrange masked facts
            let load_mask = nodes
                .flat_map(map_value(Node::load_mask))
                .map(value)
                .join_core(&facts_arranged, load_mask);

            // join masked facts with load nodes to populate them
            let load = nodes
                .flat_map(map_value(Node::load_head))
                .map(|(dst, (rel, mask, vals))| (rel, (dst, mask, vals)))
                .join_core(&relations_arranged, |rel, (dst, mask, vals), relation| {
                    [((*rel, mask.clone(), vals.clone()), (*dst, relation.kind))]
                })
                .join_map(&load_mask, load);

            // store tuples to corresponding relations
            let stored = nodes
                .map(value)
                .flat_map(Node::store_relation)
                .map(|(src, (dst, head))| (dst, (src, head)))
                .join_core(&relations_arranged, |dst, (src, head), relation| {
                    Some((*src, (*dst, head.clone(), relation.kind)))
                })
                .join_core(&tuples_arranged, |_, dst, val| [store(dst, val)]);

            // the keys of stored contain facts to give to next iteration
            let store = stored.map(key).map(Fact::relation_pair);
            facts.set_concat(&store).inspect(inspect("facts"));

            // collect constraint groups
            let constraints = nodes
                .flat_map(map_value(Node::constraint_src))
                .map_in_place(|(dst, (src, _))| std::mem::swap(dst, src))
                .join_core(&tuples_arranged, |_, dst, tup| [constraint_map(dst, tup)]);

            // combine all operations into new tuples
            tuples
                .set_concat(&join.concatenate([merge, project, filter, push, load]))
                .inspect(inspect("tuple"));

            // return outputs of all extended collections
            (
                join_gates.leave(),
                stored.flat_map(value).leave(),
                outputs.leave(),
                constraints.leave(),
            )
        });

        let constraint_type = nodes.flat_map(map_value(Node::constraint_type));

        let constraints = constraints
            .reduce(constraint_reduce)
            .map(|((dst, _head), group)| (dst, group))
            .join_map(&constraint_type, constraint_clause)
            .inspect(inspect("constraint"));

        // conditional facts make gates out of their dependent conditions
        let conditional = implies
            .reduce(conditional_gate)
            .inspect(inspect("conditional"))
            .map(|((fact, _is_decision), gate)| (fact, gate));

        // extend gates with conditional gates
        let gates = conditional
            .flat_map(value)
            .concat(&gates)
            .inspect(inspect("gate"));

        // extract conditions from conditional gates
        let conditional = conditional
            .map(|(fact, gate)| (fact, gate.map(|gate| Condition::Gate(Key::new(&gate)))))
            .concat(&facts.map(|(_, fact)| (Key::new(&fact), None)));

        // return inputs and outputs
        (
            relations_in.and(facts_in).and(nodes_in),
            routers
                .gates_out
                .add_source(&gates)
                .and(routers.conditional_out.add_source(&conditional))
                .and(routers.constraints_out.add_source(&constraints))
                .and(routers.outputs_out.add_source(&outputs)),
        )
    })
}

#[derive(Clone, Default)]
pub struct DataflowRouters {
    pub relations_in: InputRouter<Relation>,
    pub facts_in: InputRouter<Fact>,
    pub nodes_in: InputRouter<Node>,
    pub conditional_out: OutputRouter<(Key<Fact>, Option<Condition>)>,
    pub gates_out: OutputRouter<Gate>,
    pub constraints_out: OutputRouter<ConstraintGroup>,
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
) -> ((Key<Node>, Tuple), Option<Gate>) {
    let values: Values = prefix
        .iter()
        .chain(lhs.values.iter())
        .chain(rhs.values.iter())
        .cloned()
        .collect();

    let (condition, gate) = match (lhs.condition, rhs.condition) {
        (None, None) => (None, None),
        (Some(lhs), None) => (Some(lhs), None),
        (None, Some(rhs)) => (Some(rhs), None),
        (Some(lhs), Some(rhs)) => {
            let (key, gate) = Key::pair(Gate::And { lhs, rhs });
            (Some(Condition::Gate(key)), Some(gate))
        }
    };

    let tuple = Tuple { values, condition };
    ((*dst, tuple), gate)
}

pub fn project((dst, map): &(Key<Node>, IndexList), tuple: &Tuple) -> (Key<Node>, Tuple) {
    let condition = tuple.condition;
    let values = map.iter().map(|idx| tuple.values[*idx].clone()).collect();
    (*dst, Tuple { values, condition })
}

pub fn load_mask(
    relation: &Key<Relation>,
    mask: &LoadMask,
    fact: &Fact,
) -> Option<(LoadHead, (Key<Fact>, FixedValues))> {
    let values = fact
        .values
        .iter()
        .enumerate()
        .map(|(idx, val)| (mask[idx], val));

    let head = values
        .clone()
        .filter(|(masked, _)| !*masked)
        .map(value)
        .cloned()
        .collect();

    let tail = values
        .filter(|(masked, _)| *masked)
        .map(value)
        .cloned()
        .collect();

    Some(((*relation, mask.clone(), head), (Key::new(fact), tail)))
}

pub fn load(
    _head: &LoadHead,
    (node, kind): &(Key<Node>, RelationKind),
    (fact, tail): &(Key<Fact>, FixedValues),
) -> (Key<Node>, Tuple) {
    let condition = match kind {
        RelationKind::Conditional | RelationKind::Decision => Some(Condition::Fact(*fact)),
        RelationKind::Basic => None,
    };

    let values = tail.to_vec();
    (*node, Tuple { values, condition })
}

pub fn store(
    (relation, head, kind): &(Key<Relation>, StoreHead, RelationKind),
    tuple: &Tuple,
) -> (Fact, Option<((Key<Fact>, bool), Option<Condition>)>) {
    let values = head
        .iter()
        .map(|term| match term {
            QueryTerm::Value(val) => val.clone(),
            QueryTerm::Variable(idx) => tuple.values[*idx as usize].clone(),
        })
        .collect();

    let relation = *relation;
    let fact = Fact { relation, values };

    let is_decision = match kind {
        RelationKind::Basic => None,
        RelationKind::Conditional => Some(false),
        RelationKind::Decision => Some(true),
    };

    let link = is_decision.map(|is_decision| ((Key::new(&fact), is_decision), tuple.condition));

    (fact, link)
}

pub fn conditional_gate(
    (_fact, is_decision): &(Key<Fact>, bool),
    input: &[(&Option<Condition>, Diff)],
    output: &mut Vec<(Option<Gate>, Diff)>,
) {
    let terms = if input.iter().any(|(cond, _diff)| cond.is_none()) {
        output.push((None, 1));
        return;
    } else {
        input
            .iter()
            .cloned()
            .map(|(cond, _diff)| cond.unwrap().to_owned())
            .collect()
    };

    let gate = if *is_decision {
        Gate::Decision { terms }
    } else {
        Gate::Or { terms }
    };

    output.push((Some(gate), 1));
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
) -> ((Key<Node>, Values), Option<Condition>) {
    let key = map.iter().map(|idx| tuple.values[*idx].clone()).collect();
    ((*dst, key), tuple.condition)
}

pub fn constraint_reduce(
    _key: &(Key<Node>, Values),
    input: &[(&Option<Condition>, Diff)],
    output: &mut Vec<(Vec<Condition>, Diff)>,
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
    terms: &Vec<Condition>,
    (weight, kind): &(ConstraintWeight, ConstraintKind),
) -> ConstraintGroup {
    ConstraintGroup {
        terms: terms.clone(),
        weight: weight.clone(),
        kind: kind.clone(),
    }
}
