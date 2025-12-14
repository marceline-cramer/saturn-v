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

use differential_dataflow::{
    lattice::Lattice,
    operators::{
        arrange::{ArrangeByKey, Arranged},
        iterate::Variable,
        Join, JoinCore, Reduce, Threshold,
    },
    trace::TraceReader,
    Collection, Data, ExchangeData,
};
use saturn_v_ir::*;
use serde::{Deserialize, Serialize};
use timely::{communication::Allocator, dataflow::Scope, order::Product, worker::Worker};
use tracing::{event, Level};

use crate::{
    types::{
        Condition, ConditionalLink, ConstraintGroup, Fact, FixedValues, Gate, LoadHead, LoadMask,
        Node, NodeInput, NodeOutput, NodeSource, Relation, Tuple, Values,
    },
    utils::*,
    DataflowRouters, InputEventKind,
};

pub fn backend(
    worker: &mut Worker<Allocator>,
    routers: &DataflowRouters,
) -> (impl PumpInput, impl PumpOutput) {
    worker.dataflow(|scope| {
        // enter input events into scope
        let mut events_in_sink = routers.events_in.add_sink();
        let events_in = events_in_sink.to_collection(scope);

        // enter all event kinds into context
        let relations = events_in.flat_map(InputEventKind::relation).map(Key::pair);

        let facts = events_in
            .flat_map(InputEventKind::fact)
            .map(Fact::relation_pair);

        let nodes = events_in.flat_map(InputEventKind::node).map(Key::pair);

        // generate the semantics
        let (gates, implies, outputs, constraints) = scope.iterative::<u16, _, _>(|scope| {
            // enter inputs into fixedpoint scope
            let relations = relations.enter(scope);
            let nodes = nodes.enter(scope);

            // initialize program variables and state
            let step = Product::new(0, 1);
            let outer_facts = Variable::new_from(facts.enter(scope), step);
            let outer_tuples = Variable::new(scope, step);

            // evaluate each stratum
            let stratum = scope.iterative::<u32, _, _>(|scope| {
                // initialize program variables and state
                let step = Product::new(Product::new(0, 0), 1);
                let facts = Variable::new_from(outer_facts.enter(scope), step);
                let tuples = Variable::new_from(outer_tuples.enter(scope), step);

                // enter inputs into stratum scope
                let relations = relations.enter(scope);
                let nodes = nodes.enter(scope);

                // arrange tuples for all fetch operations
                let tuples_arranged = tuples.arrange_by_key();

                // arrange facts
                let facts_arranged = facts.arrange_by_key();

                // arrange relations
                let relations_arranged = relations.arrange_by_key();

                // fetch node inputs
                let node_input = nodes.map(|(key, node)| (key, node.input));

                // extract sources of left sides of join operations
                let join_lhs = &node_input
                    .flat_map(map_value(NodeInput::join_lhs))
                    .map(|(dst, (src, num))| (src, (dst, num)));

                // extract sources of right sides of join operations
                let join_rhs = &node_input
                    .flat_map(map_value(NodeInput::join_rhs))
                    .map(|(dst, (src, num))| (src, (dst, num)));

                // extract unprocessed input sources
                let source = &node_input.flat_map(|(key, input)| {
                    input.sources().into_iter().map(move |src| (src, key))
                });

                // aggregate all sources to retrieve all load masks
                let load_mask = join_lhs
                    .concat(join_rhs)
                    .map(key)
                    .concat(&source.map(key))
                    .flat_map(NodeSource::relation_mask)
                    .join_core(&facts_arranged, load_mask)
                    .arrange_by_key();

                // load each source's tuples
                let join_lhs = load_source(
                    &tuples_arranged,
                    &load_mask,
                    &relations_arranged,
                    join_slice,
                    join_lhs,
                );

                let join_rhs = load_source(
                    &tuples_arranged,
                    &load_mask,
                    &relations_arranged,
                    join_slice,
                    join_rhs,
                );

                let source = load_source(
                    &tuples_arranged,
                    &load_mask,
                    &relations_arranged,
                    |node, tuple| (*node, tuple),
                    source,
                );

                // select and merge sides of join source nodes
                let joined = join_lhs.join_map(&join_rhs, join);

                // extract the new tuples and gates from a join
                let join = joined.map(key);
                let join_gates = joined.flat_map(value);

                // collect all node input tuples and do logic
                let node_results = join
                    .concat(&source)
                    .join_core(&nodes.arrange_by_key(), node_logic);

                // write node contents outputs to tuples
                let tuples = tuples
                    .set_concat(&node_results.flat_map(NodeResult::node))
                    .inspect(inspect("tuple"));

                // filter output facts from all facts
                let outputs = facts_arranged
                    .semijoin(&relations.filter(|(_key, rel)| rel.is_output()).map(key))
                    .map(value)
                    .inspect(inspect("output"));

                // store tuples to corresponding relations
                let stored = node_results.flat_map(NodeResult::store);

                // extract facts to give to next iteration
                // TODO: make a wrapper trait for distinct() on Arranged instead
                // of using distinct() here when facts get arranged next iteration
                let store = stored.map(key).distinct().map(Fact::relation_pair);
                let facts = facts.set_concat(&store).inspect(inspect("facts"));

                // collect implications to build conditional gates with
                let implies = stored.flat_map(|(fact, (kind, cond))| {
                    kind.map(|is_decision| ((Key::new(&fact), is_decision), cond))
                });

                // collect antijoins
                let antijoins = node_results.flat_map(NodeResult::antijoin);

                // collect constraint groups
                let constraints = node_results.flat_map(NodeResult::constraint);

                // return outputs of all extended collections
                (
                    facts.leave(),
                    tuples.leave(),
                    join_gates.leave(),
                    implies.leave(),
                    outputs.leave(),
                    antijoins.leave(),
                    constraints.leave(),
                )
            });

            // extract all results of one stratum
            let (stratum_facts, stratum_tuples, gates, implies, outputs, antijoins, constraints) =
                stratum;

            // antijoin against this stratum's facts
            let (antijoin_gates, antijoin_tuples) =
                antijoin(&antijoins, &stratum_facts, &relations);

            // add antijoined tuples to next stratum
            let next_tuples = stratum_tuples.concat(&antijoin_tuples);

            // pass stratum variables to next stratum
            outer_facts.set_concat(&stratum_facts.distinct());
            outer_tuples.set_concat(&next_tuples.distinct());

            // pass the collective results out of the main loop
            (
                gates.concat(&antijoin_gates).leave(),
                implies.leave(),
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

        // find base conditional facts to add to all outgoing conditionals
        let base_conditional = facts
            .join_core(&relations.arrange_by_key(), base_conditional)
            .inspect(inspect("base conditional"))
            .map(|fact| (fact, None));

        // conditional facts make gates out of their dependent conditions
        let conditional = implies
            .concat(&base_conditional)
            .reduce(conditional_gate)
            .inspect(inspect("conditional gate"));

        // extend gates with conditional gates
        let gates = conditional
            .flat_map(value)
            .concat(&gates)
            .inspect(inspect("gate"));

        // extract conditions from conditional gates
        let conditional = conditional.map(|((fact, is_decision), gate)| {
            match (is_decision, gate) {
                // unconditional decisions remain free
                (true, None) => (fact, ConditionalLink::Free),
                // unlinked non-decision conditions are unconditional
                (false, None) => (fact, ConditionalLink::Unconditional),
                // for either type of conditional, link gate
                (_, Some(gate)) => (
                    fact,
                    ConditionalLink::Link(Condition::Gate(Key::new(&gate))),
                ),
            }
        });

        // return inputs and outputs
        (
            events_in_sink,
            routers
                .gates_out
                .add_source(&gates)
                .and(routers.conditional_out.add_source(&conditional))
                .and(routers.constraints_out.add_source(&constraints))
                .and(routers.outputs_out.add_source(&outputs)),
        )
    })
}

pub fn load_source<G, T, O, TupleTr, LoadMaskTr, RelationTr>(
    tuples: &Arranged<G, TupleTr>,
    load_mask: &Arranged<G, LoadMaskTr>,
    relations: &Arranged<G, RelationTr>,
    map: fn(&T, Tuple) -> O,
    source: &Collection<G, (NodeSource, T), Diff>,
) -> Collection<G, O, Diff>
where
    G: Scope,
    G::Timestamp: Lattice,
    T: ExchangeData,
    O: Data,
    TupleTr: Clone
        + for<'a> TraceReader<
            Key<'a> = &'a Key<Node>,
            Val<'a> = &'a Tuple,
            Diff = Diff,
            Time = G::Timestamp,
        > + 'static,
    LoadMaskTr: Clone
        + for<'a> TraceReader<
            Key<'a> = &'a LoadHead,
            Val<'a> = &'a (Key<Fact>, FixedValues),
            Diff = Diff,
            Time = G::Timestamp,
        > + 'static,
    RelationTr: Clone
        + for<'a> TraceReader<
            Key<'a> = &'a Key<Relation>,
            Val<'a> = &'a Relation,
            Diff = Diff,
            Time = G::Timestamp,
        > + 'static,
{
    // load node source tuples
    let node = source
        .flat_map(|(src, key)| src.node().map(|node| (node, key)))
        .join_core(tuples, move |_node, key, tup| [map(key, tup.clone())]);

    // load relations
    let relation = source
        .flat_map(|(src, key)| {
            src.relation_head()
                .map(|(rel, mask, vals)| (rel, (key, mask, vals)))
        })
        .join_core(relations, |rel, (dst, mask, vals), relation| {
            [(
                (*rel, mask.clone(), vals.clone()),
                (dst.clone(), relation.kind),
            )]
        })
        .join_core(load_mask, move |_head, (src, kind), (fact, tail)| {
            [map(src, load(kind, fact, tail))]
        });

    // return both node source and relation source tuples
    node.concat(&relation)
}

pub fn join_slice((dst, num): &(Key<Node>, usize), tuple: Tuple) -> ((Key<Node>, Values), Tuple) {
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
    let values: FixedValues = prefix
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

pub fn load(kind: &RelationKind, fact: &Key<Fact>, tail: &FixedValues) -> Tuple {
    let condition = match kind {
        RelationKind::Conditional | RelationKind::Decision => Some(Condition::Fact(*fact)),
        RelationKind::Basic => None,
    };

    Tuple {
        values: tail.clone(),
        condition,
    }
}

pub fn base_conditional(
    _key: &Key<Relation>,
    fact: &Fact,
    rel: &Relation,
) -> Option<(Key<Fact>, bool)> {
    let is_decision = match rel.kind {
        RelationKind::Basic => return None,
        RelationKind::Conditional => false,
        RelationKind::Decision => true,
    };

    Some((Key::new(fact), is_decision))
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
pub fn inspect<T: Debug, D: Debug>(collection: &str) -> impl for<'a> Fn(&'a (T, D, Diff)) {
    let collection = collection.to_string();
    move |(data, time, diff)| {
        event!(Level::TRACE, collection, ?time, diff, message = ?data);
    }
}

pub fn node_logic(dst: &Key<Node>, tuple: &Tuple, node: &Node) -> Option<NodeResult> {
    let mut values: Vec<_> = tuple.values.iter().cloned().collect();
    values.reserve(node.push.len());

    for expr in node.push.iter() {
        values.push(eval_expr(&values, expr));
    }

    for expr in node.filter.iter() {
        match eval_expr(&values, expr) {
            Value::Boolean(false) => return None,
            Value::Boolean(true) => {}
            other => panic!("unexpected filter value: {other:?}"),
        }
    }

    if let Some(map) = node.project.as_ref() {
        values = map.iter().map(|idx| values[*idx].clone()).collect();
    }

    let kind = match &node.output {
        NodeOutput::Node => NodeResultKind::Node {
            dst: *dst,
            values: values.into(),
        },
        NodeOutput::Antijoin { relation, query } => {
            let refute = query
                .iter()
                .map(|term| match term {
                    QueryTerm::Variable(idx) => &values[*idx as usize],
                    QueryTerm::Value(val) => val,
                })
                .cloned()
                .collect();

            NodeResultKind::Antijoin {
                dst: *dst,
                values: values.into(),
                refute: Fact {
                    relation: *relation,
                    values: refute,
                },
            }
        }
        NodeOutput::Relation { dst, head, kind } => {
            let kind = match kind {
                RelationKind::Basic => None,
                RelationKind::Conditional => Some(false),
                RelationKind::Decision => Some(true),
            };

            let values = head
                .iter()
                .map(|term| match term {
                    QueryTerm::Value(val) => val.clone(),
                    QueryTerm::Variable(idx) => values[*idx as usize].clone(),
                })
                .collect();

            let fact = Fact {
                relation: *dst,
                values,
            };

            NodeResultKind::Store { fact, kind }
        }
        NodeOutput::Constraint { head, .. } => NodeResultKind::Constraint {
            dst: *dst,
            head: head.iter().map(|idx| values[*idx].clone()).collect(),
        },
    };

    Some(NodeResult {
        cond: tuple.condition,
        kind,
    })
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Deserialize, Serialize)]
pub struct NodeResult {
    pub cond: Option<Condition>,
    pub kind: NodeResultKind,
}

impl NodeResult {
    pub fn node(self) -> Option<(Key<Node>, Tuple)> {
        match self.kind {
            NodeResultKind::Node { dst, values } => {
                let condition = self.cond;
                let tuple = Tuple { values, condition };
                Some((dst, tuple))
            }
            _ => None,
        }
    }

    pub fn antijoin(self) -> Option<(Fact, (Key<Node>, Tuple))> {
        match self.kind {
            NodeResultKind::Antijoin {
                dst,
                values,
                refute,
            } => {
                let condition = self.cond;
                let tuple = Tuple { values, condition };
                Some((refute, (dst, tuple)))
            }
            _ => None,
        }
    }

    pub fn store(self) -> Option<(Fact, (Option<bool>, Option<Condition>))> {
        match self.kind {
            NodeResultKind::Store { fact, kind } => Some((fact, (kind, self.cond))),
            _ => None,
        }
    }

    pub fn constraint(self) -> Option<((Key<Node>, FixedValues), Option<Condition>)> {
        match self.kind {
            NodeResultKind::Constraint { dst, head } => Some(((dst, head), self.cond)),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Deserialize, Serialize)]
pub enum NodeResultKind {
    Node {
        dst: Key<Node>,
        values: FixedValues,
    },

    Antijoin {
        dst: Key<Node>,
        values: FixedValues,
        refute: Fact,
    },

    Store {
        fact: Fact,
        kind: Option<bool>,
    },

    Constraint {
        dst: Key<Node>,
        head: FixedValues,
    },
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

pub fn constraint_reduce(
    _key: &(Key<Node>, FixedValues),
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
        weight: *weight,
        kind: kind.clone(),
    }
}

pub fn antijoin<G>(
    antijoins: &Collection<G, (Fact, (Key<Node>, Tuple))>,
    facts: &Collection<G, (Key<Relation>, Fact)>,
    relations: &Collection<G, (Key<Relation>, Relation)>,
) -> (Collection<G, Gate>, Collection<G, (Key<Node>, Tuple)>)
where
    G: Scope<Timestamp: Lattice>,
{
    // arrange antijoins
    // TODO: make a wrapper trait for distinct() on Arranged instead
    // of using distinct() here when facts get arranged next iteration
    let antijoins = antijoins.distinct().arrange_by_key();

    // first, unconditionally permit all antijoins with absent facts
    let unconditional = antijoins.antijoin(&facts.map(value)).map(value);

    // filter out unconditional relations
    let relations = relations.filter(|(_key, rel)| !rel.kind.is_basic());

    // filter out unconditional facts
    let facts = facts
        .semijoin(&relations.map(key))
        .map(|(_key, fact)| (fact, ()));

    // conditionally join antijoins with conditional facts
    let conditional = antijoins
        .join(&facts)
        .map(|(fact, ((node, mut tuple), ()))| {
            // create key for the refuting fact
            let fact = Condition::NotFact(Key::new(&fact));

            // optionally construct gate if tuple is conditional
            if let Some(cond) = tuple.condition {
                let gate = Gate::And {
                    lhs: cond,
                    rhs: fact,
                };

                tuple.condition = Some(Condition::Gate(Key::new(&gate)));

                return ((node, tuple), Some(gate));
            }

            // otherwise, the tuple is negatively conditional on the fact
            tuple.condition = Some(fact);
            ((node, tuple), None)
        });

    // combine all permitted tuples
    let tuples = unconditional
        .concat(&conditional.map(key))
        .inspect(inspect("antijoin"));

    // return all new tuples and all new gates
    (conditional.flat_map(value), tuples)
}
