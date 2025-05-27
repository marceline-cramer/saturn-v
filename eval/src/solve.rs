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

use std::{
    collections::{BTreeMap, BinaryHeap, HashMap},
    sync::atomic::AtomicU16,
};

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

pub type Oracle = rustsat_batsat::BasicSolver;

use crate::{
    types::{Condition, ConstraintGroup, Fact, Gate},
    utils::{Key, OutputSink, Update},
};

pub struct Solver {
    conditional_sink: OutputSink<(Key<Fact>, Option<Condition>)>,
    gates_sink: OutputSink<Gate>,
    constraints_sink: OutputSink<ConstraintGroup>,
    outputs_sink: OutputSink<Fact>,
    output_tx: Sender<Update<Fact>>,
    model: Model,
}

impl Solver {
    pub fn new(
        conditional_sink: OutputSink<(Key<Fact>, Option<Condition>)>,
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

    pub async fn run(&mut self) {
        while self.step().await.is_some() {}
    }

    pub async fn step(&mut self) -> Option<bool> {
        // track time that step started
        let start = std::time::Instant::now();
        eprintln!("stepping solver...");

        // fetch updates
        let conditional = self.conditional_sink.next_batch().await?;
        let gates = self.gates_sink.next_batch().await?;
        let constraints = self.constraints_sink.next_batch().await?;
        let outputs = self.outputs_sink.next_batch().await?;

        // display how long dataflow took to process step
        eprintln!("received solver step after {:?}", start.elapsed());

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
    conditions: HashMap<Condition, EncodedGate>,
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

        // assume conditions and hard constraint guards
        let condition_guards = self.conditions.values().map(|enc| enc.guard.neg_lit());
        let assumptions: Vec<_> = hard_constraints.chain(condition_guards).collect();

        // display statistics
        eprintln!("SAT model statistics:");
        eprintln!("  {} assumptions", assumptions.len());
        eprintln!("  {} active conditions", self.conditions.len());
        eprintln!("  {} active constraints", self.constraints.len());
        eprintln!("  {} outputs", self.outputs.len());
        eprintln!("  {} recycleable variables", self.vars.free_vars.len());
        eprintln!("  {} total clauses", self.oracle.n_clauses());

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
                eprintln!("cost assumptions: {cost_assumps:?}");
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
        conditional: Vec<((Key<Fact>, Option<Condition>), bool)>,
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
                let key = Condition::Gate(Key::new(gate));
                let enc = self.conditions.remove(&key).unwrap();
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
                let key = Condition::Gate(Key::new(gate));
                self.conditions.insert(key, EncodedGate { guard, output });
            }
        });

        // now that gates are updated, encode conditional links
        log_time("linking updated conditionals", || {
            for (guard, lhs, rhs) in conditional_links.iter() {
                let guard = guard.pos_lit();
                let lhs = self.conditions[lhs].output;
                let rhs = self.conditions[rhs].output;
                self.oracle
                    .add_ternary(guard, lhs.pos_lit(), rhs.neg_lit())
                    .unwrap();
                self.oracle
                    .add_ternary(guard, lhs.neg_lit(), rhs.pos_lit())
                    .unwrap();
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
                let key = Condition::Fact(Key::new(output));
                self.outputs.insert(
                    output.clone(),
                    (false, self.conditions.get(&key).map(|var| var.output)),
                );
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
        conditional: Vec<((Key<Fact>, Option<Condition>), bool)>,
    ) -> Vec<(Var, Condition, Condition)> {
        // split update batch
        let (conditional_insert, conditional_remove) = split_batch(conditional);

        // for every condition that has been removed, remove its current encoding
        // dependent conditions are removed separately, so just ignore them
        // recycle the output variables for each fact
        let mut conditional_vars = HashMap::new();
        log_time("removing old conditionals", || {
            for (fact, _cond) in conditional_remove.iter() {
                let key = Condition::Fact(*fact);
                let enc = self.conditions.remove(&key).unwrap();
                self.oracle.add_unit(enc.guard.pos_lit()).unwrap();
                conditional_vars.insert(key, enc.output);
            }
        });

        // insert and encode new conditionals, recycling output variables
        // track which links need to be built
        let mut links = Vec::with_capacity(conditional_insert.len());
        log_time("inserting new conditionals", || {
            for (fact, cond) in conditional_insert.iter() {
                let key = Condition::Fact(*fact);

                // recycle an output variable for a removed conditional if possible
                let output = conditional_vars
                    .remove(&key)
                    .unwrap_or_else(|| self.vars.new_var());

                // create a new guard variable for the link
                let guard = self.vars.new_var();

                // insert the encoding
                self.conditions.insert(key, EncodedGate { guard, output });

                // if the conditional has a condition, link the condition
                if let Some(cond) = cond {
                    links.push((guard, key, *cond));
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
        let mut enc = GuardEncoder {
            inner: &mut self.oracle,
            guard: guard.pos_lit(),
        };

        let cond = |key: &Condition| {
            let encoded = self.conditions[key];
            // TODO: minimize assumptions. this breaks when conditionals are updated with new guards
            // enc.add_clause([encoded.guard.pos_lit()].into());
            encoded.output
        };

        use Gate::*;
        match gate {
            And { lhs, rhs } => {
                let lhs = cond(lhs);
                let rhs = cond(rhs);
                enc.add_clause([lhs.neg_lit(), rhs.neg_lit(), output.pos_lit()].into())?;
                enc.add_clause([lhs.pos_lit(), output.neg_lit()].into())?;
                enc.add_clause([rhs.pos_lit(), output.neg_lit()].into())?;
            }
            Or { terms } => {
                let mut all_false = Vec::with_capacity(terms.len() + 2);
                all_false.push(output.neg_lit());

                let terms: Vec<_> = terms.iter().map(cond).collect();
                for term in terms {
                    enc.add_clause([term.neg_lit(), output.pos_lit()].into())?;
                    all_false.push(term.pos_lit());
                }

                enc.add_clause(all_false.as_slice().into()).unwrap();
            }
            Decision { terms } => {
                let mut clause = Vec::with_capacity(terms.len() + 2);
                clause.push(output.neg_lit());

                for term in terms {
                    clause.push(cond(term).pos_lit());
                }

                enc.add_clause(clause.as_slice().into()).unwrap();
            }
        }

        Ok(())
    }

    /// Encodes a constraint group.
    pub fn encode_constraint_group(&mut self, guard: Var, constraint: &ConstraintGroup) {
        let mut enc = GuardEncoder {
            inner: &mut self.oracle,
            guard: guard.pos_lit(),
        };

        // map term conditions into output variables
        let terms = constraint
            .terms
            .iter()
            .map(|cond| self.conditions[cond].output.pos_lit());

        match &constraint.kind {
            ConstraintKind::Cardinality {
                kind: CardinalityConstraintKind::AtLeast,
                threshold: 1,
            } => {
                enc.add_clause(FromIterator::from_iter(terms)).unwrap();
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
pub struct GuardEncoder<'a> {
    inner: &'a mut Oracle,
    guard: Lit,
}

impl CollectClauses for GuardEncoder<'_> {
    fn n_clauses(&self) -> usize {
        self.inner.n_clauses()
    }

    fn extend_clauses<T>(&mut self, cl_iter: T) -> Result<(), rustsat::OutOfMemory>
    where
        T: IntoIterator<Item = Clause>,
    {
        self.inner.extend_clauses(cl_iter.into_iter().map(|mut cl| {
            cl.add(self.guard);
            cl
        }))
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
    static INDENT: AtomicU16 = AtomicU16::new(0);

    let indent = "  ".repeat(INDENT.fetch_add(1, std::sync::atomic::Ordering::Relaxed) as usize);
    eprintln!("{indent}{message}...");

    let start = std::time::Instant::now();
    let result = cb();
    eprintln!("{indent}{message} took {:?}", start.elapsed());

    INDENT.fetch_sub(1, std::sync::atomic::Ordering::Relaxed);

    result
}
