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

use flume::Sender;
use rustsat::{
    encodings::{
        am1::{Commander, Encode, Pairwise},
        card::{totalizer::Totalizer, BoundBoth},
        CollectClauses,
    },
    instances::ManageVars,
    solvers::{Solve, SolveIncremental, SolverResult},
    types::{constraints::CardConstraint, Lit, Var},
};
use saturn_v_ir::{CardinalityConstraintKind, ConstraintKind};

pub type Oracle = rustsat_batsat::BasicSolver;

use crate::{
    types::{Clause, Condition, Fact},
    utils::{Key, OutputSink, Update},
};

pub struct Solver {
    conditions_sink: OutputSink<Key<Condition>>,
    clauses_sink: OutputSink<Clause>,
    outputs_sink: OutputSink<Fact>,
    output_tx: Sender<Update<Fact>>,
    model: Model,
}

impl Solver {
    pub fn new(
        conditions_sink: OutputSink<Key<Condition>>,
        clauses_sink: OutputSink<Clause>,
        outputs_sink: OutputSink<Fact>,
        output_tx: Sender<Update<Fact>>,
    ) -> Self {
        Self {
            conditions_sink,
            clauses_sink,
            outputs_sink,
            output_tx,
            model: Model::default(),
        }
    }

    pub async fn run(&mut self) {
        while self.step().await.is_some() {}
    }

    pub async fn step(&mut self) -> Option<bool> {
        // fetch updates
        let conditions = self.conditions_sink.next_batch().await?;
        let clauses = self.clauses_sink.next_batch().await?;
        let outputs = self.outputs_sink.next_batch().await?;

        // update model
        let removed_outputs = self.model.update(conditions, clauses, outputs);

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
            let value = sat
                && self
                    .model
                    .oracle
                    .var_val(*var)
                    .unwrap()
                    .to_bool_with_def(false);

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
    clauses: HashMap<Clause, Var>,
    conditions: HashMap<Key<Condition>, Var>,
    outputs: BTreeMap<Fact, (bool, Var)>,
}

impl Model {
    pub fn solve(&mut self) -> Option<bool> {
        // time solving
        let start = std::time::Instant::now();

        // display statistics
        eprintln!("starting SAT solving...");
        eprintln!("  {} pending var recycs", self.vars.free_vars.len());
        eprintln!("  {} active clauses", self.clauses.len());
        eprintln!("  {} active conditions", self.conditions.len());
        eprintln!("  {} outputs", self.outputs.len());

        // solve SAT, assuming clause gates
        let assumptions: Vec<_> = self.clauses.values().map(|var| var.neg_lit()).collect();
        let result = self.oracle.solve_assumps(&assumptions).unwrap();

        // display solve time and SAT stats
        eprintln!("solved in {:?}", start.elapsed());

        // return result
        match result {
            SolverResult::Sat => Some(true),
            SolverResult::Unsat => Some(false),
            SolverResult::Interrupted => None,
        }
    }

    /// Returns the list of outputs that have been disabled and removed.
    pub fn update(
        &mut self,
        conditions: Vec<(Key<Condition>, bool)>,
        clauses: Vec<(Clause, bool)>,
        outputs: Vec<(Fact, bool)>,
    ) -> Vec<Fact> {
        // split update batches into insertions and removals
        let (conditions_insert, conditions_remove) = split_batch(conditions);
        let (clauses_insert, clauses_remove) = split_batch(clauses);
        let (outputs_insert, outputs_remove) = split_batch(outputs);

        // mapping constraints into clauses goes here...

        // remove clauses and force their gate variables
        // don't add the variable back to the queue because it is now forced
        log_time("removing old clauses...", || {
            for clause in clauses_remove.iter() {
                let gate = self.clauses.remove(clause).unwrap();
                self.oracle.add_unit(gate.pos_lit()).unwrap();
            }
        });

        // remove lookups for removed conditions
        // add variables back to pool because they aren't forced
        log_time("removing old conditions...", || {
            for cond in conditions_remove.iter() {
                let var = self.conditions.remove(cond).unwrap();
                self.vars.recycle(var);
            }
        });

        // create lookups for new conditions
        log_time("adding new conditions...", || {
            for cond in conditions_insert.iter() {
                let var = self.vars.new_var();
                self.conditions.insert(*cond, var);
            }
        });

        // create lookups for new clauses
        log_time("inserting new clauses...", || {
            for clause in clauses_insert.iter() {
                self.insert_clause(clause);
            }
        });

        // forward removal of outputs
        let mut removed_outputs = Vec::with_capacity(outputs_remove.len());
        log_time("removing old outputs...", || {
            for output in outputs_remove.iter() {
                if self.outputs.remove(output).unwrap().0 {
                    removed_outputs.push(output.clone());
                }
            }
        });

        // insert new outputs with default state of false
        log_time("inserting new outputs...", || {
            for output in outputs_insert.iter() {
                let cond = Key::new(&Condition::from(output.clone()));
                let var = self.conditions[&cond];
                self.outputs.insert(output.clone(), (false, var));
            }
        });

        // return removed outputs
        removed_outputs
    }

    fn insert_clause(&mut self, clause: &Clause) {
        use Clause::*;
        let gate = self.vars.new_var();
        self.clauses.insert(clause.clone(), gate);

        let mut enc = GatedEncoder {
            inner: &mut self.oracle,
            gate: gate.pos_lit(),
        };

        match clause {
            And { lhs, rhs, out } => {
                let lhs = self.conditions[lhs];
                let rhs = self.conditions[rhs];
                let out = self.conditions[out];
                enc.add_clause([lhs.neg_lit(), rhs.neg_lit(), out.pos_lit()].into())
                    .unwrap();
                enc.add_clause([lhs.pos_lit(), out.neg_lit()].into())
                    .unwrap();
                enc.add_clause([rhs.pos_lit(), out.neg_lit()].into())
                    .unwrap();
            }
            AndNot { lhs, rhs, out } => {
                let lhs = self.conditions[lhs];
                let rhs = self.conditions[rhs];
                let out = self.conditions[out];
                enc.add_clause([lhs.neg_lit(), rhs.pos_lit(), out.pos_lit()].into())
                    .unwrap();
                enc.add_clause([lhs.pos_lit(), out.neg_lit()].into())
                    .unwrap();
                enc.add_clause([rhs.neg_lit(), out.neg_lit()].into())
                    .unwrap();
            }
            Implies { term, out } => {
                let term = self.conditions[term];
                let out = self.conditions[out];
                enc.add_clause([term.neg_lit(), out.pos_lit()].into())
                    .unwrap();
            }
            Or { terms, out } => {
                let out = self.conditions[out];
                let mut all_false = Vec::with_capacity(terms.len() + 2);
                all_false.push(out.neg_lit());

                for term in terms {
                    let term = self.conditions[term];
                    enc.add_clause([term.neg_lit(), out.pos_lit()].into())
                        .unwrap();
                    all_false.push(term.pos_lit());
                }

                enc.add_clause(all_false.as_slice().into()).unwrap();
            }
            Decision { terms, out } => {
                let mut clause = Vec::with_capacity(terms.len() + 2);
                clause.push(self.conditions[out].neg_lit());

                for term in terms {
                    clause.push(self.conditions[term].pos_lit());
                }

                enc.add_clause(clause.as_slice().into()).unwrap();
            }
            ConstraintGroup { terms, kind, .. } => self.encode_constraint(
                gate.pos_lit(),
                terms
                    .iter()
                    .map(|key| self.conditions[key].pos_lit())
                    .collect(),
                kind,
            ),
        }
    }

    /// Encodes a constraint.
    pub fn encode_constraint(&mut self, gate: Lit, terms: Vec<Lit>, kind: &ConstraintKind) {
        let mut enc = GatedEncoder {
            inner: &mut self.oracle,
            gate,
        };

        match kind {
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

/// Helper struct to add clauses with a gate literal.
pub struct GatedEncoder<'a> {
    inner: &'a mut Oracle,
    gate: Lit,
}

impl CollectClauses for GatedEncoder<'_> {
    fn n_clauses(&self) -> usize {
        self.inner.n_clauses()
    }

    fn extend_clauses<T>(&mut self, cl_iter: T) -> Result<(), rustsat::OutOfMemory>
    where
        T: IntoIterator<Item = rustsat::types::Clause>,
    {
        self.inner.extend_clauses(cl_iter.into_iter().map(|mut cl| {
            cl.add(self.gate);
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

fn log_time(message: &str, mut cb: impl FnMut()) {
    eprintln!("{message}");
    let start = std::time::Instant::now();
    cb();
    eprintln!("done in {:?}", start.elapsed());
}
