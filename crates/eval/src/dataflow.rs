// Copyright (C) 2025-2026 Marceline Cramer
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

use std::{fmt::Debug, hash::Hash, sync::Arc};

use dashmap::DashMap;
use derive_where::derive_where;
use differential_dataflow::{
    input::Input,
    lattice::Lattice,
    operators::{
        arrange::{ArrangeByKey, Arranged},
        iterate::Variable,
        Join, JoinCore, Reduce, Threshold,
    },
    trace::TraceReader,
    Data, ExchangeData, VecCollection,
};
use saturn_v_ir::*;
use saturn_v_solve::{Bool, BoolBinaryOp, BoolUnaryOp, DataflowModel};
use serde::{Deserialize, Serialize};
use timely::{
    communication::Allocator,
    dataflow::{scopes::Child, Scope, ScopeParent},
    order::Product,
    progress::timestamp::Refines,
    worker::Worker,
};
use tracing::{event, Level};

use crate::{
    types::{
        get_load_mask, Fact, FixedValues, LoadHead, LoadMask, Node, NodeInput, NodeOutput,
        NodeSource, Relation, Tuple, Values,
    },
    utils::*,
    DataflowRouters, InputEventKind,
};

pub fn backend<M: DataflowModel>(
    model: Arc<M>,
    worker: &mut Worker<Allocator>,
    routers: &DataflowRouters<M>,
) -> (impl PumpInput, impl PumpOutput) {
    worker.dataflow(|scope| {
        // enter input events into scope
        let mut events_in_sink = routers.events_in.add_sink();
        let events_in = events_in_sink.to_collection(scope);

        // build complete input
        let input = StratumInput {
            conditionals: ConditionalStore::new(model.clone()),
            facts: events_in.flat_map(InputEventKind::fact),
            relations: events_in.flat_map(InputEventKind::relation),
            nodes: events_in.flat_map(InputEventKind::node),
            tuples: scope.new_collection().1,
            model,
        };

        // evaluate to fixed-point
        let output = StratumOutput::evaluate_stratified(scope, &input);

        let node_constraint_type = input
            .nodes
            .map(Key::pair)
            .flat_map(map_value(Node::constraint_type))
            .arrange_by_key();

        let constraints = output
            .constraints
            .reduce(constraint_reduce)
            .map(|((dst, _head), group)| (dst, group))
            .arrange_by_key()
            .join_core(&node_constraint_type, constraint_clause)
            .inspect(inspect("constraint"));

        // filter out output facts
        let outputs = input
            .relations
            .filter(|rel| rel.io == RelationIO::Output)
            .map(|rel| (Key::new(&rel), rel.kind))
            .join_map(
                &output.facts.map(Fact::relation_pair),
                |_key, kind, fact| {
                    let cond = if kind.is_basic() {
                        model.from_const(true)
                    } else {
                        input.conditionals.get_conditional(Key::new(&fact))
                    };

                    (fact.clone(), cond)
                },
            );

        // return inputs and outputs
        (
            events_in_sink,
            routers
                .constraints_out
                .add_source(&constraints)
                .and(routers.outputs_out.add_source(&outputs)),
        )
    })
}

/// The inputs to the core per-stratum dataflow computation.
pub struct StratumInput<G: Scope, M: DataflowModel> {
    /// The [ConditionalStore] for all facts.
    pub conditionals: ConditionalStore<M>,

    /// The model that encodes new symbolic logic expressions.
    pub model: Arc<M>,

    /// All nodes in the dataflow at this stratum.
    pub nodes: VecCollection<G, Node>,

    /// All relations in the dataflow.
    pub relations: VecCollection<G, Relation>,

    /// All currently-known facts.
    pub facts: VecCollection<G, Fact>,

    /// The current collection of tuples in each node.
    pub tuples: VecCollection<G, (Key<Node>, Tuple<M>)>,
}

impl<M: DataflowModel, G: Scope + ScopeParent> StratumInput<G, M> {
    /// Enters this input into a child scope.
    pub fn enter<'a, T: Refines<G::Timestamp>>(
        &self,
        scope: &mut Child<'a, G, T>,
    ) -> StratumInput<Child<'a, G, T>, M> {
        StratumInput {
            conditionals: self.conditionals.clone(),
            model: self.model.clone(),
            nodes: self.nodes.enter(scope),
            relations: self.relations.enter(scope),
            facts: self.facts.enter(scope),
            tuples: self.tuples.enter(scope),
        }
    }
}

/// The results of the core dataflow computation, per-stratum.
pub struct StratumOutput<G: Scope, M: DataflowModel> {
    /// Unique facts added to the dataflow.
    pub facts: VecCollection<G, Fact>,

    /// Conditional fact implications.
    pub implies: VecCollection<G, (Key<Fact>, Bool<M>)>,

    /// New tuples computed in this stratum.
    pub tuples: VecCollection<G, (Key<Node>, Tuple<M>)>,

    /// New antijoin tuples: tuples who may be refuted by the presence of facts.
    pub antijoins: VecCollection<G, (Fact, (Key<Node>, Tuple<M>))>,

    /// Constraint groups and their entries.
    pub constraints: VecCollection<G, ((Key<Node>, FixedValues), Bool<M>)>,
}

impl<'a, G: Scope, M: DataflowModel, T: Refines<G::Timestamp>> StratumOutput<Child<'a, G, T>, M> {
    /// Leaves this child scope.
    pub fn leave(self) -> StratumOutput<G, M> {
        StratumOutput {
            facts: self.facts.leave(),
            implies: self.implies.leave(),
            tuples: self.tuples.leave(),
            antijoins: self.antijoins.leave(),
            constraints: self.constraints.leave(),
        }
    }
}

impl<G: Scope<Timestamp: Hash + Default + Lattice>, M: DataflowModel> StratumOutput<G, M> {
    /// Evaluates stratified input, using alternating fixedpoints per-stratum.
    pub fn evaluate_stratified(scope: &mut G, input: &StratumInput<G, M>) -> Self {
        scope.iterative::<u32, _, _>(move |scope| {
            // enter input into this scope
            let input = StratumInput {
                nodes: input.nodes.enter_at(scope, |node| node.stratum()),
                ..input.enter(scope)
            };

            // evaluate this stratum to positive fixed-point
            StratumOutput::evaluate_naf(scope, &input).leave()
        })
    }

    /// Evaluates to fixedpoint using alternating fixedpoints with negation as failure.
    pub fn evaluate_naf(scope: &mut G, input: &StratumInput<G, M>) -> Self {
        scope.iterative::<u32, _, _>(move |scope| {
            // enter input into this scope
            let mut input = input.enter(scope);

            // initialize feedback variable for tuples that pass NAF
            let step = Product::new(Default::default(), 1);
            let tuples = Variable::new_from(input.tuples, step.clone());

            // track each alternating fixedpoint's antijoins
            let antijoins = Variable::new(scope, step);

            // replace input with variables
            input.tuples = tuples.clone();

            // run this stratum to positive fixed-point
            let mut output = StratumOutput::evaluate_stratum(scope, &input);

            // arrange only this stratum's antijoins
            let antijoins = antijoins.set(&output.antijoins).distinct().arrange_by_key();

            // unconditionally permit all antijoins with absent facts
            let unconditional = antijoins.antijoin(&output.facts.distinct()).map(value);

            // extract conditional relation keys
            let conditional_relations = input
                .relations
                .filter(|rel| !rel.kind.is_basic())
                .map(|rel| Key::new(&rel));

            // extract conditional facts
            let conditional_facts = output
                .facts
                .map(Fact::relation_pair)
                .semijoin(&conditional_relations)
                .map(value);

            // conditionally antijoin with present facts
            let conditional = antijoins.semijoin(&conditional_facts).map({
                let model = input.model.clone();
                let cond_store = input.conditionals.clone();
                move |(fact, (node, mut tuple))| {
                    let fact_cond = cond_store.get_conditional(Key::new(&fact));

                    tuple.condition = model.binary_op(
                        BoolBinaryOp::And,
                        tuple.condition,
                        model.unary_op(BoolUnaryOp::Not, fact_cond),
                    );

                    (node, tuple)
                }
            });

            // collate all permitted tuples
            let antijoin_tuples = unconditional.concat(&conditional);

            // pass permitted tuples
            output.tuples = tuples.set_concat(&antijoin_tuples);

            // return outputs of all extended collections
            output.leave()
        })
    }

    /// Evaluates a single stratum to fixed-point using positive semi-naive evaluation.
    pub fn evaluate_stratum(scope: &mut G, input: &StratumInput<G, M>) -> Self {
        scope.iterative::<u32, _, _>(move |scope| {
            // enter input to this iteration
            let mut input = input.enter(scope);

            // init feed-forward inputs for each step
            let step = Product::new(Default::default(), 1);
            let facts = Variable::new_from(input.facts, step.clone());
            let tuples = Variable::new_from(input.tuples, step);

            // replace inputs with their variables
            input.facts = facts.clone();
            input.tuples = tuples.clone();

            // run the internal semi-naive evaluation
            let mut output = StratumOutput::evaluate_once(&input);

            // feed outputs back into stratum variables to fixed-point
            output.facts = facts.set_concat(&output.facts);
            output.tuples = tuples.set_concat(&output.tuples);

            // return outputs of all extended collections
            output.leave().inspect()
        })
    }

    /// Calculates a single iteration of positive semi-naive inference.
    pub fn evaluate_once(input: &StratumInput<G, M>) -> Self {
        // arrange all inputs
        let tuples_arranged = input.tuples.arrange_by_key();
        let facts_arranged = input.facts.map(Fact::relation_pair).arrange_by_key();
        let relations_arranged = input.relations.map(Key::pair).arrange_by_key();
        let nodes = input.nodes.map(Key::pair);
        let nodes_arranged = nodes.arrange_by_key();

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
        let source = &node_input
            .flat_map(|(key, input)| input.sources().into_iter().map(move |src| (src, key)));

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
            input.model.clone(),
            input.conditionals.clone(),
            &tuples_arranged,
            &load_mask,
            &relations_arranged,
            join_slice,
            join_lhs,
        );

        let join_rhs = load_source(
            input.model.clone(),
            input.conditionals.clone(),
            &tuples_arranged,
            &load_mask,
            &relations_arranged,
            join_slice,
            join_rhs,
        );

        let source = load_source(
            input.model.clone(),
            input.conditionals.clone(),
            &tuples_arranged,
            &load_mask,
            &relations_arranged,
            |node, tuple| (*node, tuple),
            source,
        );

        // select and merge sides of join source nodes
        let joined = join_lhs.join_map(&join_rhs, {
            let model = input.model.clone();
            move |key, lhs, rhs| join(model.as_ref(), key, lhs, rhs)
        });

        // collect all node input tuples and do logic
        let node_results = joined
            .concat(&source)
            .join_core(&nodes_arranged, node_logic)
            .distinct();

        // store facts with implications to corresponding relations
        let stored = node_results.flat_map(NodeResult::store);

        // return outputs
        Self {
            facts: stored.map(key),
            implies: stored.map(|(fact, cond)| (Key::new(&fact), cond)),
            tuples: node_results.flat_map(NodeResult::node),
            antijoins: node_results.flat_map(NodeResult::antijoin),
            constraints: node_results.flat_map(NodeResult::constraint),
        }
    }

    /// Inspects all outputs.
    pub fn inspect(self) -> Self {
        Self {
            facts: self.facts.inspect(inspect("fact")),
            implies: self.implies.inspect(inspect("imply")),
            tuples: self.tuples.inspect(inspect("tuple")),
            antijoins: self.antijoins.inspect(inspect("antijoin")),
            constraints: self.constraints.inspect(inspect("constraint")),
        }
    }
}

pub fn load_source<M, G, T, O, TupleTr, LoadMaskTr, RelationTr>(
    model: Arc<M>,
    cond_store: ConditionalStore<M>,
    tuples: &Arranged<G, TupleTr>,
    load_mask: &Arranged<G, LoadMaskTr>,
    relations: &Arranged<G, RelationTr>,
    map: fn(&T, Tuple<M>) -> O,
    source: &VecCollection<G, (NodeSource, T)>,
) -> VecCollection<G, O>
where
    M: DataflowModel,
    G: Scope,
    G::Timestamp: Lattice,
    T: ExchangeData,
    O: Data,
    TupleTr: Clone
        + for<'a> TraceReader<
            Key<'a> = &'a Key<Node>,
            Val<'a> = &'a Tuple<M>,
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
            let condition = if kind.is_basic() {
                model.from_const(true)
            } else {
                cond_store.get_conditional(*fact)
            };

            let tuple = Tuple {
                values: tail.clone(),
                condition,
            };

            [map(src, tuple)]
        });

    // return both node source and relation source tuples
    node.concat(&relation)
}

pub fn join_slice<M: DataflowModel>(
    (dst, num): &(Key<Node>, usize),
    tuple: Tuple<M>,
) -> ((Key<Node>, Values), Tuple<M>) {
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

pub fn join<M: DataflowModel>(
    model: &M,
    (dst, prefix): &(Key<Node>, Values),
    lhs: &Tuple<M>,
    rhs: &Tuple<M>,
) -> (Key<Node>, Tuple<M>) {
    let values: FixedValues = prefix
        .iter()
        .chain(lhs.values.iter())
        .chain(rhs.values.iter())
        .cloned()
        .collect();

    let condition = model.binary_op(
        BoolBinaryOp::And,
        lhs.condition.clone(),
        rhs.condition.clone(),
    );

    let tuple = Tuple { values, condition };

    (*dst, tuple)
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
        .map(|(idx, val)| (get_load_mask(mask, idx), val));

    let head = values
        .clone()
        .filter(|(masked, _)| !masked)
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

#[allow(unused_variables)]
pub fn inspect<T: Debug, D: Debug>(collection: &str) -> impl for<'a> Fn(&'a (T, D, Diff)) {
    let collection = collection.to_string();
    move |(data, time, diff)| {
        event!(Level::TRACE, collection, ?time, diff, message = ?data);
    }
}

pub fn node_logic<M: DataflowModel>(
    dst: &Key<Node>,
    tuple: &Tuple<M>,
    node: &Node,
) -> Option<NodeResult<M>> {
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
        NodeOutput::Antijoin {
            relation, query, ..
        } => {
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

            NodeResultKind::Store { fact }
        }
        NodeOutput::Constraint { head, .. } => NodeResultKind::Constraint {
            dst: *dst,
            head: head.iter().map(|idx| values[*idx].clone()).collect(),
        },
    };

    Some(NodeResult {
        cond: tuple.condition.clone(),
        kind,
    })
}

#[derive_where(
    Clone,
    Debug,
    PartialEq,
    Eq,
    Hash,
    PartialOrd,
    Ord,
    Deserialize,
    Serialize
)]
pub struct NodeResult<M: DataflowModel> {
    pub cond: Bool<M>,
    pub kind: NodeResultKind,
}

impl<M: DataflowModel> NodeResult<M> {
    pub fn node(self) -> Option<(Key<Node>, Tuple<M>)> {
        match self.kind {
            NodeResultKind::Node { dst, values } => {
                let condition = self.cond;
                let tuple = Tuple { values, condition };
                Some((dst, tuple))
            }
            _ => None,
        }
    }

    pub fn antijoin(self) -> Option<(Fact, (Key<Node>, Tuple<M>))> {
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

    pub fn store(self) -> Option<(Fact, Bool<M>)> {
        match self.kind {
            NodeResultKind::Store { fact } => Some((fact, self.cond)),
            _ => None,
        }
    }

    pub fn constraint(self) -> Option<((Key<Node>, FixedValues), Bool<M>)> {
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

pub struct ConditionalStore<M: DataflowModel>(Arc<DashMap<Key<Fact>, Bool<M>>>, Arc<M>);

impl<M: DataflowModel> Clone for ConditionalStore<M> {
    fn clone(&self) -> Self {
        Self(self.0.clone(), self.1.clone())
    }
}

impl<M: DataflowModel> ConditionalStore<M> {
    /// Creates an empty conditional store.
    pub fn new(model: Arc<M>) -> Self {
        Self(Default::default(), model)
    }

    /// Get the condition for a fact, or insert it if it doesn't exist.
    pub fn get_conditional(&self, fact: Key<Fact>) -> Bool<M> {
        todo!()
    }
}
