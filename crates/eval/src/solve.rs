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

use std::collections::{BTreeMap, BinaryHeap, HashMap};

use batsat::Callbacks;
use flume::Sender;
use rustsat::{
    encodings::{
        am1::{Commander, Encode, Pairwise},
        card::{totalizer::Totalizer, BoundBoth},
        pb::{BoundUpper, BoundUpperIncremental, GeneralizedTotalizer},
        CollectClauses,
    },
    instances::ManageVars,
    solvers::{Solve, SolveIncremental, SolverResult},
    types::{constraints::CardConstraint, Clause, Lit, Var},
};
use saturn_v_ir::{CardinalityConstraintKind, ConstraintKind, ConstraintWeight};
use tracing::{debug, span, trace, Level};

pub type Oracle = rustsat_batsat::Solver<SolverCallbacks>;

#[derive(Default)]
pub struct SolverCallbacks;

impl Callbacks for SolverCallbacks {}

use crate::{
    types::{Condition, ConditionalLink, ConstraintGroup, Fact, Gate},
    utils::{Key, OutputSink, Update},
};

pub struct Solver {
    conditional_sink: OutputSink<(Key<Fact>, ConditionalLink)>,
    gates_sink: OutputSink<Gate>,
    constraints_sink: OutputSink<ConstraintGroup>,
    outputs_sink: OutputSink<Fact>,
    output_tx: Sender<Update<Fact>>,
    model: Model,
}

impl Solver {
    pub fn new(
        conditional_sink: OutputSink<(Key<Fact>, ConditionalLink)>,
        gates_sink: OutputSink<Gate>,
        constraints_sink: OutputSink<ConstraintGroup>,
        outputs_sink: OutputSink<Fact>,
        output_tx: Sender<Update<Fact>>,
    ) -> Self {
        Self {
            conditional_sink,
            gates_sink,
            constraints_sink,
            outputs_sink,
            output_tx,
            model: Model::default(),
        }
    }

    pub async fn step(&mut self) -> Option<bool> {
        // fetch updates
        let conditional = self.conditional_sink.next_batch().await?;
        let gates = self.gates_sink.next_batch().await?;
        let constraints = self.constraints_sink.next_batch().await?;
        let outputs = self.outputs_sink.next_batch().await?;

        // update model
        let removed_outputs = log_time("updating SAT model", || {
            self.model.update(conditional, gates, constraints, outputs)
        });

        // remove any outputs just removed
        for output in removed_outputs {
            let _ = self.output_tx.send(Update::Push(output, false));
        }

        // solve
        let sat = self.model.solve()?;

        // update outputs
        self.update_outputs(sat);

        // done
        Some(sat)
    }

    pub fn update_outputs(&mut self, sat: bool) {
        // make sure that when we update outputs, we default to all outputs
        // being false if the SAT solver returned unknown or unsat
        for (output, (state, var)) in self.model.outputs.iter_mut() {
            // find what state this output should be in
            let value = match var {
                // look up value of conditional varaible
                Some(var) => {
                    sat && self
                        .model
                        .oracle
                        .var_val(*var)
                        .unwrap()
                        .to_bool_with_def(false)
                }
                // unconditional variables are forced to true
                None => true,
            };

            if *state != value {
                let _ = self.output_tx.send(Update::Push(output.clone(), value));
                *state = value;
            }
        }

        let _ = self.output_tx.send(Update::Flush);
    }
}

#[derive(Default)]
pub struct Model {
    oracle: Oracle,
    vars: VariablePool,
    gates: HashMap<Key<Gate>, EncodedGate>,
    conditionals: HashMap<Key<Fact>, EncodedGate>,
    constraints: HashMap<ConstraintGroup, (Var, bool)>,
    cost_totalizer: GeneralizedTotalizer,
    outputs: BTreeMap<Fact, (bool, Option<Var>)>,
}

impl Model {
    pub fn solve(&mut self) -> Option<bool> {
        // split up soft and hard constraints
        let hard_constraints = self
            .constraints
            .values()
            .filter(|(_guard, is_hard)| *is_hard)
            .map(|(guard, _is_hard)| guard.neg_lit());

        // assume all condition guards
        let condition_guards = self
            .gates
            .values()
            .chain(self.conditionals.values())
            .map(|enc| enc.guard.neg_lit());

        // assume conditions and hard constraint guards
        let assumptions: Vec<_> = hard_constraints.chain(condition_guards).collect();

        // display statistics
        debug!(
            assumptions = assumptions.len(),
            gates = self.gates.len(),
            conditionals = self.conditionals.len(),
            constraints = self.constraints.len(),
            outputs = self.outputs.len(),
            recyc_vars = self.vars.free_vars.len(),
            clauses = self.oracle.n_clauses(),
            "SAT model statistics"
        );

        // first, ensure that the model is SAT with no cost bounds
        let result = log_time("checking satisfiability of the unoptimized model", || {
            self.oracle.solve_assumps(&assumptions).unwrap()
        });

        // proceed accordingly
        match result {
            // optimize if the base model is SAT
            SolverResult::Sat => {}
            // if the base model is UNSAT, immediately give up (avoid infinite loop)
            SolverResult::Unsat => return Some(false),
            // if the solver was interrupted, abort search
            SolverResult::Interrupted => return None,
        }

        // run MaxSAT with progressively higher cost upper bounds
        log_time("optimizing lower cost bound", || {
            let mut cost = 0;
            loop {
                // update totalizer encodings for this upper bound
                self.cost_totalizer
                    .encode_ub_change(cost..=cost, &mut self.oracle, &mut self.vars)
                    .unwrap();

                // add assumptions to check cost upper bound
                let mut assumptions = assumptions.clone();
                let cost_assumps = self.cost_totalizer.enforce_ub(cost).unwrap();
                trace!("cost assumptions: {cost_assumps:?}");
                assumptions.extend(cost_assumps);

                // solve SAT
                let msg = format!("running SAT for cost {cost}");
                let result = log_time(&msg, || self.oracle.solve_assumps(&assumptions).unwrap());

                // increase cost lower bound for next iteration
                cost += 1;

                // return result
                match result {
                    SolverResult::Sat => return Some(true),
                    SolverResult::Unsat => continue,
                    SolverResult::Interrupted => return None,
                }
            }
        })
    }

    /// Atomically updates the model based on incremental changes to the parameters.
    ///
    /// Returns the list of outputs that have been disabled and removed.
    pub fn update(
        &mut self,
        conditional: Vec<((Key<Fact>, ConditionalLink), bool)>,
        gates: Vec<(Gate, bool)>,
        constraints: Vec<(ConstraintGroup, bool)>,
        outputs: Vec<(Fact, bool)>,
    ) -> Vec<Fact> {
        // split update batches into insertions and removals
        let (gates_insert, gates_remove) = split_batch(gates);
        let (outputs_insert, outputs_remove) = split_batch(outputs);

        // remove gates and force their guard variables
        // don't add the guard back to the queue because it is now forced
        log_time("removing old gates", || {
            for gate in gates_remove.iter() {
                let key = Key::new(gate);
                let enc = self.gates.remove(&key).unwrap();
                self.vars.recycle(enc.output);
                self.oracle.add_unit(enc.guard.pos_lit()).unwrap();
            }
        });

        // update conditionals, tracking links that need to be added
        let conditional_links = self.update_conditional(conditional);

        // create lookups for new gates
        log_time("inserting new gates", || {
            for gate in gates_insert.iter() {
                // encode the gate
                let guard = self.vars.new_var();
                let output = self.vars.new_var();
                self.encode_gate(gate, guard, output).unwrap();

                // insert it into the conditions
                let key = Key::new(gate);
                self.gates.insert(key, EncodedGate { guard, output });
            }
        });

        // now that gates are updated, encode conditional links
        log_time("linking updated conditionals", || {
            for (guard, lhs, rhs) in conditional_links.iter() {
                let guard = guard.pos_lit();
                let lhs = self.get_condition(lhs);
                let rhs = self.get_condition(rhs);
                self.oracle.add_ternary(guard, lhs, !rhs).unwrap();
                self.oracle.add_ternary(guard, !lhs, rhs).unwrap();
            }
        });

        // update constraint groups
        self.update_constraint_groups(constraints);

        // forward removal of outputs
        let mut removed_outputs = Vec::with_capacity(outputs_remove.len());
        log_time("removing old outputs", || {
            for output in outputs_remove.iter() {
                if self.outputs.remove(output).unwrap().0 {
                    removed_outputs.push(output.clone());
                }
            }
        });

        // insert new outputs defaulted to false
        log_time("inserting new outputs", || {
            for output in outputs_insert.iter() {
                // insert output value with conditional variable
                let key = Key::new(output);
                let var = self.conditionals.get(&key).map(|cond| cond.output);
                self.outputs.insert(output.clone(), (false, var));
            }
        });

        // return removed outputs
        removed_outputs
    }

    /// Atomically updates the conditional facts in the model.
    ///
    /// Returns the list of links that need to be built after dependent gates are
    /// updated and encoded with their guard variable.
    pub fn update_conditional(
        &mut self,
        conditional: Vec<((Key<Fact>, ConditionalLink), bool)>,
    ) -> Vec<(Var, Condition, Condition)> {
        // split update batch
        let (conditional_insert, conditional_remove) = split_batch(conditional);

        // for every condition that has been removed, remove its current encoding
        // dependent conditions are removed separately, so just ignore them
        // recycle the output variables for each fact
        let mut conditional_vars = HashMap::new();
        log_time("removing old conditionals", || {
            for (fact, _cond) in conditional_remove.iter() {
                let enc = self.conditionals.remove(fact).unwrap();
                self.oracle.add_unit(enc.guard.pos_lit()).unwrap();
                conditional_vars.insert(*fact, enc.output);
            }
        });

        // insert and encode new conditionals, recycling output variables
        // track which links need to be built
        let mut links = Vec::with_capacity(conditional_insert.len());
        log_time("inserting new conditionals", || {
            for (fact, link) in conditional_insert.iter() {
                // recycle an output variable for a removed conditional if possible
                let output = conditional_vars
                    .remove(fact)
                    .unwrap_or_else(|| self.vars.new_var());

                // create a new guard variable for the link
                let guard = self.vars.new_var();

                // insert the encoding
                self.conditionals
                    .insert(*fact, EncodedGate { guard, output });

                match link {
                    // if the conditional has a condition, link the condition
                    ConditionalLink::Link(cond) => {
                        links.push((guard, Condition::Fact(*fact), *cond))
                    }
                    // if unconditionally true, make the guard force the conditional
                    ConditionalLink::Unconditional => self
                        .oracle
                        .add_binary(guard.pos_lit(), output.pos_lit())
                        .unwrap(),
                    // if the conditional is unbound, do nothing
                    ConditionalLink::Free => {}
                }
            }
        });

        // recycle all conditional vars that were not recycled into conditions
        for var in conditional_vars.into_values() {
            self.vars.recycle(var);
        }

        // return the list of links to encode later
        links
    }

    /// Incrementally update constraint groups.
    pub fn update_constraint_groups(&mut self, constraints: Vec<(ConstraintGroup, bool)>) {
        // split update batch
        let (constraints_insert, constraints_remove) = split_batch(constraints);

        // remove old constraints and disable their guards
        // don't recycle guards because they have been forced
        log_time("removing constraint groups", || {
            for constraint in constraints_remove.iter() {
                let (guard, _weight) = self.constraints.remove(constraint).unwrap();
                self.oracle.add_unit(guard.pos_lit()).unwrap();
            }
        });

        // add new constraints
        log_time("inserting constraint groups", || {
            for constraint in constraints_insert.iter() {
                let guard = self.vars.new_var();
                self.encode_constraint_group(guard, constraint);

                let is_hard = match constraint.weight {
                    ConstraintWeight::Hard => true,
                    ConstraintWeight::Soft(weight) => {
                        let lit = (guard.pos_lit(), weight as usize);
                        self.cost_totalizer.extend([lit]);
                        false
                    }
                };

                self.constraints
                    .insert(constraint.clone(), (guard, is_hard));
            }
        });
    }

    /// Encodes a gate with the given guard and output variables.
    pub fn encode_gate(
        &mut self,
        gate: &Gate,
        guard: Var,
        output: Var,
    ) -> Result<(), rustsat::OutOfMemory> {
        let cond = |key: &Condition| self.get_condition(key);
        let output = output.pos_lit();
        let mut enc = GuardEncoder::new(guard.pos_lit());

        use Gate::*;
        match gate {
            And { lhs, rhs } => {
                let lhs = cond(lhs);
                let rhs = cond(rhs);
                enc.add([!lhs, !rhs, output]);
                enc.add([lhs, !output]);
                enc.add([rhs, !output]);
            }
            Or { terms } => {
                let mut all_false = Vec::with_capacity(terms.len() + 2);
                all_false.push(!output);

                let terms: Vec<_> = terms.iter().map(cond).collect();
                for term in terms {
                    enc.add([!term, output]);
                    all_false.push(term);
                }

                enc.add(all_false);
            }
            Decision { terms } => {
                let mut clause = Vec::with_capacity(terms.len() + 2);
                clause.push(!output);

                for term in terms {
                    clause.push(cond(term));
                }

                enc.add(clause);
            }
        }

        enc.drain(&mut self.oracle)
    }

    /// Encodes a constraint group.
    pub fn encode_constraint_group(&mut self, guard: Var, constraint: &ConstraintGroup) {
        // map term conditions into output variables
        let terms: Vec<_> = constraint
            .terms
            .iter()
            .map(|cond| self.get_condition(cond))
            .collect();

        let mut enc = GuardEncoder::new(guard.pos_lit());

        match &constraint.kind {
            ConstraintKind::Cardinality {
                kind: CardinalityConstraintKind::AtLeast,
                threshold: 1,
            } => {
                enc.add(terms);
            }
            ConstraintKind::Cardinality {
                kind: CardinalityConstraintKind::AtMost,
                threshold: 1,
            } => {
                let mut am1 = Commander::<4, Pairwise>::from_iter(terms);
                am1.encode(&mut enc, &mut self.vars).unwrap();
            }
            ConstraintKind::Cardinality { kind, threshold } => {
                let threshold = *threshold as usize;

                let constr = match kind {
                    CardinalityConstraintKind::AtLeast => CardConstraint::new_lb(terms, threshold),
                    CardinalityConstraintKind::AtMost => CardConstraint::new_ub(terms, threshold),
                    CardinalityConstraintKind::Only => CardConstraint::new_eq(terms, threshold),
                };

                Totalizer::encode_constr(constr, &mut enc, &mut self.vars).unwrap();
            }
        }

        enc.drain(&mut self.oracle).unwrap();
    }

    /// Retrieves a literal that represents the truthity of a [Condition].
    pub fn get_condition(&self, cond: &Condition) -> Lit {
        match cond {
            Condition::Gate(key) => self.gates[key].output.pos_lit(),
            Condition::Fact(key) => self.conditionals[key].output.pos_lit(),
            Condition::NotFact(key) => self.conditionals[key].output.neg_lit(),
        }
    }
}

/// Tracks an encoded gate.
#[derive(Copy, Clone, Debug)]
pub struct EncodedGate {
    /// The guard variable for this gate.
    pub guard: Var,

    /// The output variable for this gate.
    pub output: Var,
}

/// Helper struct to add clauses with a guard literal.
pub struct GuardEncoder {
    clauses: Vec<Clause>,
    guard: Lit,
}

impl CollectClauses for GuardEncoder {
    fn n_clauses(&self) -> usize {
        self.clauses.len()
    }

    fn extend_clauses<T>(&mut self, cl_iter: T) -> Result<(), rustsat::OutOfMemory>
    where
        T: IntoIterator<Item = Clause>,
    {
        for clause in cl_iter {
            self.add(clause);
        }

        Ok(())
    }
}

impl GuardEncoder {
    /// Creates a new guard encoder from the given literal.
    pub fn new(guard: Lit) -> Self {
        Self {
            clauses: Vec::new(),
            guard,
        }
    }

    /// Adds a clause to this encoder.
    pub fn add(&mut self, lits: impl IntoIterator<Item = Lit>) {
        let mut clause: Clause = lits.into_iter().collect();
        clause.add(self.guard);
        self.clauses.push(clause);
    }

    /// Drain the clauses in this guard encoder into an oracle.
    pub fn drain<T: CollectClauses>(self, oracle: &mut T) -> Result<(), rustsat::OutOfMemory> {
        oracle.extend_clauses(self.clauses)
    }
}

/// Allocator for SAT variables.
#[derive(Default)]
pub struct VariablePool {
    next_var: u32,
    free_vars: BinaryHeap<Var>,
    used_num: u32,
}

impl VariablePool {
    pub fn recycle(&mut self, var: Var) {
        self.free_vars.push(var);
        self.used_num -= 1;
    }
}

impl ManageVars for VariablePool {
    fn new_var(&mut self) -> Var {
        self.used_num += 1;
        self.free_vars.pop().unwrap_or_else(|| {
            let var = self.next_var;
            self.next_var += 1;
            Var::new(var)
        })
    }

    fn max_var(&self) -> Option<Var> {
        None
    }

    fn increase_next_free(&mut self, _v: Var) -> bool {
        false
    }

    fn combine(&mut self, _other: Self) {
        unimplemented!()
    }

    fn n_used(&self) -> u32 {
        self.used_num
    }

    fn forget_from(&mut self, _: Var) {
        unimplemented!()
    }
}

/// Splits an update batch into inserts and removals.
pub fn split_batch<T>(batch: Vec<(T, bool)>) -> (Vec<T>, Vec<T>) {
    let mut insert = Vec::new();
    let mut remove = Vec::new();
    for (item, update) in batch {
        match update {
            true => insert.push(item),
            false => remove.push(item),
        }
    }

    (insert, remove)
}

fn log_time<T>(message: &str, cb: impl FnOnce() -> T) -> T {
    let span = span!(
        Level::TRACE,
        "solver_time",
        message = message,
        duration_us = tracing::field::Empty
    );

    let _enter = span.enter();

    trace!("{message}...");

    let start = std::time::Instant::now();
    let result = cb();
    let duration = start.elapsed();
    trace!("{message} took {duration:?}");

    span.record("duration_us", duration.as_micros());

    result
}
