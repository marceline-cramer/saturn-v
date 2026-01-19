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
    collections::HashMap,
    hash::{BuildHasherDefault, DefaultHasher, Hash, Hasher},
};

use prehash::Passthru;
use smallvec::{smallvec, SmallVec};

use crate::{partial::PartialValue, *};

pub struct SatSolver {
    model: SatModel,
}

impl Solver for SatSolver {
    type Model = SatModel;

    fn solve(&mut self, opts: SolveOptions<SatModel>) -> SolveResult {
        todo!()
    }

    fn as_model(&mut self) -> &mut Self::Model {
        &mut self.model
    }

    fn into_model(self) -> Self::Model {
        self.model
    }
}

// TODO: garbage collection
pub struct SatModel {
    /// Maps variable IDs to their [Gate] encodings.
    ///
    /// If a variable ID does not have a gate, it is considered unconstrained.
    gates: HashMap<u64, Gate, BuildHasherDefault<Passthru>>,

    /// The ID of the next fresh variable.
    next_var: u64,
}

impl Model for SatModel {
    type Bool = PartialValue<bool, Lit>;
}

impl SatModel {
    /// Adds a gate to this model and returns its variable ID.
    ///
    /// It's crucial that the hash function used here is cryptographic and that
    /// risk of collision is effectively zero. Collisions are not explicitly
    /// handled so this is a possibility.
    ///
    /// Determinism is not needed currently but may be needed for future cluster execution.
    pub fn add_gate(&mut self, gate: Gate) -> u64 {
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
    pub fn add_var(&mut self) -> u64 {
        let id = self.next_var;
        self.next_var += 1;
        id
    }
}

/// A logical gate, which encodes CNF clauses to constrain values.
///
/// For now, it's assumed that all gates force exactly one literal, When support
/// for bitvectors is added, gates will support constraining multiple output
/// literals at once.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Gate {
    /// A mapping from gate term variable indices to [Lit].
    pub variables: SmallVec<[Lit; 2]>,

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
pub struct Lit {
    /// The unique variable identifier of this literal.
    pub variable: u64,

    /// This literal's polarity.
    pub polarity: bool,
}

impl Fresh<SatModel> for Lit {
    fn fresh(state: &mut SatModel) -> Self {
        Lit {
            variable: state.add_var(),
            polarity: true,
        }
    }
}

impl<S> UnaryOp<S> for Lit {
    type Op = BoolUnaryOp;

    fn unary_op(self, _state: &mut S, op: Self::Op) -> Self {
        match op {
            BoolUnaryOp::Not => self.not(),
        }
    }
}

impl BinaryOp<SatModel> for Lit {
    type Op = BoolBinaryOp;

    fn binary_op(self, state: &mut SatModel, op: Self::Op, rhs: Self) -> Self {
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
            variables: smallvec![self, rhs],
            clauses,
        };

        // return the gate's output as a literal
        Lit {
            variable: state.add_gate(gate),
            polarity: true,
        }
    }
}

impl BinaryOp<SatModel, bool> for PartialValue<bool, Lit> {
    type Op = BoolBinaryOp;

    fn binary_op(self, _state: &mut SatModel, op: Self::Op, rhs: bool) -> Self {
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

impl<S> ToRust<S, bool> for Lit {
    fn to_const(&self, _state: &mut S) -> Option<bool> {
        // CNF variables are never known before solve
        None
    }
}

impl Lit {
    /// Negates the polarity of this literal.
    pub fn not(self) -> Self {
        Self {
            variable: self.variable,
            polarity: !self.polarity,
        }
    }
}
