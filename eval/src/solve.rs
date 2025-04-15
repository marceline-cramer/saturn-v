use std::collections::{BTreeMap, BinaryHeap, HashMap};

use flume::Sender;
use saturn_v_ir::{ConstraintKind, ConstraintWeight};

use crate::{
    types::{Clause, Condition, Fact},
    utils::{OutputSink, Update},
};

pub struct Solver {
    sat: cadical::Solver,
    next_var: i32,
    conditions_sink: OutputSink<Condition>,
    clauses_sink: OutputSink<Clause>,
    outputs_sink: OutputSink<Fact>,
    free_vars: BinaryHeap<i32>,
    clauses: HashMap<Clause, i32>,
    conditions: HashMap<Condition, i32>,
    outputs: BTreeMap<Fact, (bool, i32)>,
    output_tx: Sender<Update<Fact>>,
}

impl Solver {
    pub fn new(
        conditions_sink: OutputSink<Condition>,
        clauses_sink: OutputSink<Clause>,
        outputs_sink: OutputSink<Fact>,
        output_tx: Sender<Update<Fact>>,
    ) -> Self {
        Self {
            conditions_sink,
            clauses_sink,
            outputs_sink,
            output_tx,
            sat: cadical::Solver::default(),
            next_var: 1,
            free_vars: BinaryHeap::new(),
            clauses: HashMap::new(),
            conditions: HashMap::new(),
            outputs: BTreeMap::new(),
        }
    }

    pub async fn run(&mut self) {
        loop {
            self.step().await.unwrap();
            self.update_outputs();
        }
    }

    pub async fn step(&mut self) -> Option<bool> {
        // process the next batch of outputs
        let (conditions_insert, conditions_remove) =
            split_batch(self.conditions_sink.next_batch().await?);
        let (clauses_insert, clauses_remove) = split_batch(self.clauses_sink.next_batch().await?);
        let (outputs_insert, outputs_remove) = split_batch(self.outputs_sink.next_batch().await?);

        // mapping constraints into clauses goes here...

        // remove clauses and force their gate variables
        // don't add the variable back to the queue because it is now forced
        for clause in clauses_remove {
            let gate = self.clauses.remove(&clause).unwrap();
            self.sat.add_clause([-gate]);
        }

        // remove lookups for removed conditions
        // add variables back to pool because they aren't forced
        for cond in conditions_remove {
            let var = self.conditions.remove(&cond).unwrap();
            self.free_vars.push(var);
        }

        // create lookups for new conditions
        for cond in conditions_insert {
            let var = self.create_variable();
            self.conditions.insert(cond, var);
        }

        // create lookups for new clauses
        for clause in clauses_insert {
            self.insert_clause(clause);
        }

        // forward removal of outputs
        for output in outputs_remove {
            if self.outputs.remove(&output).unwrap().0 {
                let _ = self.output_tx.send(Update::Push(output, false));
            }
        }

        // insert new outputs with default state of false
        for output in outputs_insert {
            let cond = Condition::from(output.clone());
            let var = self.conditions[&cond];
            self.outputs.insert(output, (false, var));
        }

        // solve SAT, assuming clause gates
        self.sat.solve_with(self.clauses.values().copied())
    }

    fn create_variable(&mut self) -> i32 {
        self.free_vars.pop().unwrap_or_else(|| {
            let var = self.next_var;
            self.next_var += 1;
            var
        })
    }

    fn insert_clause(&mut self, clause: Clause) {
        use Clause::*;
        let gate = self.create_variable();
        self.clauses.insert(clause.clone(), -gate);
        match clause {
            And { lhs, rhs, out } => {
                let lhs = self.conditions[&lhs];
                let rhs = self.conditions[&rhs];
                let out = self.conditions[&out];
                self.sat.add_clause([gate, -lhs, -rhs, out]);
                self.sat.add_clause([gate, lhs, -out]);
                self.sat.add_clause([gate, rhs, -out]);
            }
            AndNot { lhs, rhs, out } => {
                let lhs = self.conditions[&lhs];
                let rhs = self.conditions[&rhs];
                let out = self.conditions[&out];
                self.sat.add_clause([gate, -lhs, rhs, out]);
                self.sat.add_clause([gate, lhs, -out]);
                self.sat.add_clause([gate, -rhs, -out]);
            }
            Implies { term, out } => {
                let term = self.conditions[&term];
                let out = self.conditions[&out];
                self.sat.add_clause([gate, -term, out]);
            }
            Or { terms, out } => {
                let out = self.conditions[&out];
                let mut all_false = Vec::with_capacity(terms.len() + 2);
                all_false.push(gate);
                all_false.push(-out);

                for term in terms {
                    let term = self.conditions[&term];
                    self.sat.add_clause([gate, -term, out]);
                    all_false.push(term);
                }

                self.sat.add_clause(all_false);
            }
            Decision { terms, out } => {
                let mut clause = Vec::with_capacity(terms.len() + 2);
                clause.push(gate);
                clause.push(-self.conditions[&out]);

                for term in terms {
                    clause.push(self.conditions[&term]);
                }

                self.sat.add_clause(clause);
            }
            ConstraintGroup {
                terms,
                weight: ConstraintWeight::Hard,
                kind: ConstraintKind::Any,
            } => {
                let mut clause = Vec::with_capacity(terms.len() + 1);
                clause.push(gate);

                for term in terms {
                    clause.push(self.conditions[&term]);
                }

                self.sat.add_clause(clause);
            }
            ConstraintGroup {
                terms,
                weight: ConstraintWeight::Hard,
                kind: ConstraintKind::One,
            } => {
                // simultaneously upper-bound and lower-bound term count
                let mut clause = Vec::with_capacity(terms.len() + 1);
                clause.push(gate);
                for (idx, lhs) in terms.iter().enumerate() {
                    // at least one term must be true
                    let lhs = self.conditions[lhs];
                    clause.push(lhs);

                    // for each pair of terms, both must not be true
                    for rhs in terms[(idx + 1)..].iter() {
                        let rhs = self.conditions[rhs];
                        self.sat.add_clause([gate, -lhs, -rhs]);
                    }
                }

                // add completed "OR" clause
                self.sat.add_clause(clause);
            }
            other => unimplemented!("unimplemented clause kind: {other:?}"),
        }
    }

    pub fn update_outputs(&mut self) {
        // make sure that when we update outputs, we default to all outputs
        // being false if the SAT solver returned unknown or unsat
        let sat = self.sat.status().unwrap_or(false);

        for (output, (state, var)) in self.outputs.iter_mut() {
            let value = sat && self.sat.value(*var).unwrap_or(false);
            if *state != value {
                let _ = self.output_tx.send(Update::Push(output.clone(), value));
                *state = value;
            }
        }

        let _ = self.output_tx.send(Update::Flush);
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
