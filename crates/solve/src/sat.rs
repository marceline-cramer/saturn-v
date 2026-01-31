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

use std::{
    collections::hash_map,
    hash::{BuildHasherDefault, DefaultHasher, Hash, Hasher},
    ops::Not,
    sync::{
        atomic::{AtomicU64, Ordering},
        Arc,
    },
};

use dashmap::DashMap;
use prehash::Passthru;
use rustsat::{
    encodings::{
        pb::{BoundUpper, BoundUpperIncremental, DynamicPolyWatchdog},
        CollectClauses,
    },
    instances::{BasicVarManager, ManageVars},
    solvers::SolveIncremental,
    types::{Lit, Var},
};
use smallvec::{smallvec, SmallVec};

use crate::{partial::PartialValue, *};

#[derive(Default)]
pub struct SatSolver<S> {
    solver: S,
    var_mgr: BasicVarManager,
    model: SatModel,

    /// Maps variable identifiers to this solver instance's variables.
    vars: hash_map::HashMap<u64, Var, BuildHasherDefault<Passthru>>,
}

impl<S> Solver for SatSolver<S>
where
    S: CollectClauses + SolveIncremental,
{
    type Model = SatModel;

    fn solve(&mut self, opts: SolveOptions<SatModel>) -> SolveResult {
        // encode and collect all hard constraint assumptions
        let mut assumptions = Vec::with_capacity(opts.hard.len());
        for var in opts.hard.iter() {
            use PartialValue::*;
            match var {
                Const(true) => {}
                Const(false) => return SolveResult::Unsat,
                Variable(lit) => {
                    assumptions.push(self.get_lit(*lit));
                }
            }
        }

        // save the number of hard assumptions
        // this may be less than the number of hard constraints if some are constant true
        let hard_assumption_num = assumptions.len();

        // create a cost totalizer for soft constraints
        let mut cost_totalizer: DynamicPolyWatchdog = opts
            .soft
            .iter()
            .flat_map(|(value, weight)| value.variable().map(|lit| (lit, *weight)))
            .map(|(lit, weight)| (!self.get_lit(lit), weight as usize))
            .collect();

        // initialize with no current assignment to queried Booleans
        let mut bool_values = None;

        // assign an initial, unused cost value (will update after first SAT)
        let mut cost = 0;

        // begin minimizing the cost upper bound
        loop {
            // check satisfiability with current assumptions
            // TODO: replace unwrap with tracing error + return unknown
            let result = self.solver.solve_assumps(&assumptions).unwrap();

            // handle non-sat solving results
            use rustsat::solvers::SolverResult::*;
            match result {
                Sat => {}
                Interrupted => return SolveResult::Unknown,
                Unsat => match bool_values {
                    Some(bool_values) => {
                        return SolveResult::Sat { cost, bool_values };
                    }
                    None => {
                        return SolveResult::Unsat;
                    }
                },
            }

            // evaluate the current queried Boolean values
            bool_values = Some(self.eval_bools(opts.bool_eval));

            // clear any soft assumptions from the previous iteration
            assumptions.truncate(hard_assumption_num);

            // calculate the cost of the current assignment
            cost = opts
                .soft
                .iter()
                .filter(|(value, _weight)| !self.eval_bool(*value))
                .map(|(_value, weight)| *weight)
                .sum();

            // if cost has hit zero, this is the best solution
            if cost == 0 {
                return SolveResult::Sat {
                    cost,
                    bool_values: bool_values.unwrap(),
                };
            }

            // otherwise, attempt to find a better cost upper bound
            let cost_ub = (cost - 1) as usize;

            // update the totalizer's encodings for the new cost bound
            cost_totalizer
                .encode_ub_change(cost_ub..=cost_ub, &mut self.solver, &mut self.var_mgr)
                .unwrap();

            // add soft assumptions for this new cost upper bound
            assumptions.extend(cost_totalizer.enforce_ub(cost_ub).unwrap());
        }
    }

    fn as_model(&mut self) -> &mut Self::Model {
        &mut self.model
    }

    fn into_model(self) -> Self::Model {
        self.model
    }
}

impl<S: SolveIncremental + CollectClauses> SatSolver<S> {
    /// Evaluates a list of Boolean values in the current solver model.
    pub fn eval_bools(&mut self, values: &[PartialValue<bool, SatLit>]) -> Vec<bool> {
        values
            .iter()
            .cloned()
            .map(|value| self.eval_bool(value))
            .collect()
    }

    /// Evaluate a Boolean value in the current solver model.
    pub fn eval_bool(&mut self, value: PartialValue<bool, SatLit>) -> bool {
        value.eval(|lit| {
            let var = self.get_var(lit.variable);
            let model = self.solver.var_val(var).unwrap();
            model.to_bool_with_def(false) ^ !lit.polarity
        })
    }

    /// Returns the instance's variable index for the model's variable ID.
    pub fn get_var(&mut self, id: u64) -> Var {
        // reuse existing variable if possible
        use hash_map::Entry;
        let var = match self.vars.entry(id) {
            Entry::Occupied(existing) => return *existing.get(),
            Entry::Vacant(entry) => {
                // allocate and insert new variable otherwise
                let var = self.var_mgr.new_var();
                entry.insert(var);
                var
            }
        };

        // get the variable's gate, if available
        let Some(gate) = self
            .model
            .gates
            .get(&id)
            .map(|entry| entry.value().to_owned())
        else {
            // if no gate is available, the variable is unconstrained
            return var;
        };

        // get each variable in the gate
        // will invoke this function recursively, so stack overflow is a possibility
        let gate_vars: SmallVec<[Lit; 8]> =
            gate.literals.iter().map(|lit| self.get_lit(*lit)).collect();

        // create a closure to convert gate terms to instance literals
        let term_to_lit = |term: &GateTerm| match *term {
            GateTerm::Output { polarity } => Lit::new(var.idx32(), !polarity),
            GateTerm::Literal { variable, polarity } => {
                let lit = *gate_vars.get(variable as usize).unwrap();

                if polarity {
                    lit
                } else {
                    !lit
                }
            }
        };

        // encode each clause in the gate
        let clauses = gate
            .clauses
            .iter()
            .map(|clause| clause.iter().map(term_to_lit).collect());

        // add clauses to the solver
        self.solver.extend_clauses(clauses).unwrap();

        // return the variable ID
        var
    }

    /// Returns the instance's literal for a model literal.
    pub fn get_lit(&mut self, lit: SatLit) -> Lit {
        let var = self.get_var(lit.variable);
        Lit::new(var.idx32(), !lit.polarity)
    }
}

pub type SatModel = Arc<SatModelInner>;

// TODO: garbage collection
pub struct SatModelInner {
    /// Maps variable IDs to their [Gate] encodings.
    ///
    /// If a variable ID does not have a gate, it is considered unconstrained.
    gates: DashMap<u64, Gate, BuildHasherDefault<Passthru>>,

    /// The ID of the next fresh variable.
    // TODO: either ensure this doesn't need to be cryptographic *or* generate randomly.
    next_var: AtomicU64,
}

impl Default for SatModelInner {
    fn default() -> Self {
        Self {
            gates: Default::default(),
            next_var: AtomicU64::from(1),
        }
    }
}

impl Model for SatModel {
    type Encoder = Self;

    fn encode(&self) -> Self::Encoder {
        self.clone()
    }

    type Bool = PartialValue<bool, SatLit>;
}

impl SatModelInner {
    /// Adds a gate to this model and returns its variable ID.
    ///
    /// It's crucial that the hash function used here is cryptographic and that
    /// risk of collision is effectively zero. Collisions are not explicitly
    /// handled so this is a possibility.
    ///
    /// Determinism is not needed currently but may be needed for future cluster execution.
    pub fn add_gate(&self, gate: Gate) -> u64 {
        // hash the gate to get a variable ID
        let mut hasher = DefaultHasher::new();
        gate.hash(&mut hasher);
        let var = hasher.finish();

        // add the gate to the model
        self.gates.insert(var, gate);

        // return the variable ID
        var
    }

    /// Creates a new unbound variable identifier.
    pub fn add_var(&self) -> u64 {
        self.next_var.fetch_add(1, Ordering::Relaxed)
    }
}

/// A logical gate, which encodes CNF clauses to constrain values.
///
/// For now, it's assumed that all gates force exactly one literal as output.
/// When support for bitvectors is added, gates will support constraining
/// multiple output literals at once.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Gate {
    /// A mapping from gate term variable indices to [SatLit].
    pub literals: SmallVec<[SatLit; 2]>,

    /// The list of clauses in the gate.
    ///
    /// Optimized for data locality (hash-consing + encoding). AND and OR gates are three clauses each.
    pub clauses: SmallVec<[Clause; 3]>,
}

/// A macro for easily instantiating a [GateTerm].
macro_rules! term {
    (~output) => {
        GateTerm::Output { polarity: false }
    };

    (output) => {
        GateTerm::Output { polarity: true }
    };

    (~$var:expr) => {
        GateTerm::Literal {
            variable: $var,
            polarity: false,
        }
    };

    ($var:expr) => {
        GateTerm::Literal {
            variable: $var,
            polarity: true,
        }
    };
}

/// A singular clause in a [Gate].
///
/// Optimized for data locality. Three is the maximum number of terms in
/// Tseitin encodings of AND and OR gates, which are very common.
pub type Clause = SmallVec<[GateTerm; 3]>;

/// A term within a [Gate] clause list.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum GateTerm {
    /// A literal, indexed by the gate's literal table.
    Literal {
        /// The variable's index in the gate table.
        variable: u32,

        /// This literal's polarity.
        polarity: bool,
    },

    /// The output of this gate.
    Output {
        /// The polarity of this output in a clause.
        polarity: bool,
    },
}

/// A SAT literal.
///
/// This represents a hash-consed literal within [SatModel], which has not
/// yet been added to a SAT solver via conventional 32-bit, solver-local
/// encodings. This conversion is deferred so that evaluation may add and
/// remove constraints independently of an append-only SAT solver and support
/// rebuilding a solver entirely from scratch.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct SatLit {
    /// The unique variable identifier of this literal.
    pub variable: u64,

    /// This literal's polarity.
    pub polarity: bool,
}

impl Fresh<SatModel> for SatLit {
    fn fresh(encoder: &mut SatModel) -> Self {
        SatLit {
            variable: encoder.add_var(),
            polarity: true,
        }
    }
}

impl<E> UnaryOp<E> for SatLit {
    type Op = BoolUnaryOp;

    fn unary_op(self, _encoder: &mut E, op: Self::Op) -> Self {
        match op {
            BoolUnaryOp::Not => self.not(),
        }
    }
}

impl BinaryOp<SatModel> for SatLit {
    type Op = BoolBinaryOp;

    fn binary_op(self, encoder: &mut SatModel, op: Self::Op, rhs: Self) -> Self {
        // choose Tseitin encoding depending on operation
        let clauses = match op {
            BoolBinaryOp::And => smallvec![
                smallvec!(term!(~0), term!(~1), term!(output)),
                smallvec!(term!(0), term!(~output)),
                smallvec!(term!(1), term!(~output))
            ],
            BoolBinaryOp::Or => smallvec!(
                smallvec!(term!(0), term!(1), term!(~output)),
                smallvec!(term!(~0), term!(output)),
                smallvec!(term!(~1), term!(output))
            ),
        };

        // create the gate encoding
        let gate = Gate {
            literals: smallvec![self, rhs],
            clauses,
        };

        // return the gate's output as a literal
        SatLit {
            variable: encoder.add_gate(gate),
            polarity: true,
        }
    }
}

impl BinaryOp<SatModel, bool> for PartialValue<bool, SatLit> {
    type Op = BoolBinaryOp;

    fn binary_op(self, _encoder: &mut SatModel, op: Self::Op, rhs: bool) -> Self {
        use BoolBinaryOp::*;
        use PartialValue::*;
        match (op, rhs) {
            (And, false) => Const(false),
            (And, true) => self,
            (Or, true) => Const(true),
            (Or, false) => self,
        }
    }
}

impl<E> ToRust<E, bool> for SatLit {
    fn to_const(&self, _encoder: &mut E) -> Option<bool> {
        // CNF variables are never known before solve
        None
    }
}

impl Not for SatLit {
    type Output = Self;

    fn not(self) -> Self {
        Self {
            variable: self.variable,
            polarity: !self.polarity,
        }
    }
}
