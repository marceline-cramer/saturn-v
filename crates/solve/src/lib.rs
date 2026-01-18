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

pub mod partial;

#[cfg(feature = "sat")]
pub mod sat;

#[cfg(feature = "z3")]
pub mod z3;

// TODO: state concurrency wrappers
// TODO: consider a lazy encoding wrapper to minimize cost of large aggregates
// TODO: hash-consing memoization wrappers?

/// A solver.
///
/// The solver owns the model so that it may track incremental updates to it
/// idiomatically.
pub trait Solver {
    /// The type of [Model] this solver works with.
    type Model: Model;

    /// Solves the internal model with the given [SolveOptions].
    fn solve(&mut self, opts: SolveOptions<Self::Model>) -> SolveResult;

    /// Accesses the model in the solver.
    fn as_model(&mut self) -> &mut Self::Model;

    /// Destroys this solver and returns the internal model.
    fn into_model(self) -> Self::Model;
}

/// Parameters for a [Solver] run.
pub struct SolveOptions<'a, M: Model> {
    /// The hard assumptions.
    pub hard: &'a [M::Bool],

    /// The soft assumptions to use.
    pub soft: &'a [(M::Bool, u32)],

    /// The Boolean values to evaluate after solving.
    pub bool_eval: &'a [M::Bool],
}

impl<'a, M: Model> Default for SolveOptions<'a, M> {
    fn default() -> Self {
        Self {
            hard: &[],
            soft: &[],
            bool_eval: &[],
        }
    }
}

/// The result of a solve.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SolveResult {
    /// A solution could not be found.
    Unknown,

    /// There is no solution.
    Unsat,

    /// The solve was successful.
    Sat {
        /// The total cost of this solution.
        cost: u32,

        /// Each Boolean value's evaluation in the solution.
        bool_values: Vec<bool>,
    },
}

impl SolveResult {
    /// Tests if the result is [SolveResult::Sat].
    pub fn is_sat(&self) -> bool {
        matches!(self, SolveResult::Sat { .. })
    }

    /// Tests if the result is [SolveResult::Unsat].
    pub fn is_unsat(&self) -> bool {
        matches!(self, SolveResult::Unsat { .. })
    }
}

/// A logic model for encoding problems within.
pub trait Model {
    /// The type of this model's Boolean values.
    type Bool: Bool<Self>;
}

/// A trait for Boolean values within given state.
pub trait Bool<S: ?Sized>:
    Fresh<S>
    + FromRust<S, bool>
    + ToRust<S, bool>
    + Value<S, UnaryOp = BoolUnaryOp, BinaryOp = BoolBinaryOp>
{
}

impl<S: ?Sized, T> Bool<S> for T where
    T: Fresh<S>
        + FromRust<S, bool>
        + ToRust<S, bool>
        + Value<S, UnaryOp = BoolUnaryOp, BinaryOp = BoolBinaryOp>
{
}

/// Convert a value from a Rust value.
pub trait FromRust<S: ?Sized, T> {
    /// Creates a value of this type from a Rust value.
    fn from_const(state: &mut S, value: T) -> Self;
}

/// Convert a value to a Rust value.
pub trait ToRust<S: ?Sized, T> {
    /// Attempts to convert a value of this type to a Rust value.
    fn to_const(&self, state: &mut S) -> Option<T>;
}

/// Create a unique, unconstrained value.
///
/// If a value is equivalent via [Eq], it is guaranteed to refer only to the
/// same fresh value.
pub trait Fresh<S: ?Sized>: Eq {
    /// Create an unconstrained value.
    fn fresh(state: &mut S) -> Self;
}

/// Operations on values with the given state as context.
pub trait Value<S: ?Sized>: BinaryOp<S, Self> {
    /// The type of unary operations on this value.
    type UnaryOp;

    /// Performs a unary operation on this value.
    fn unary_op(self, state: &mut S, op: Self::UnaryOp) -> Self;
}

/// Implements binary operations with a specific right-hand operand type.
pub trait BinaryOp<S: ?Sized, Rhs: ?Sized> {
    /// The type of binary operations on this value.
    type BinaryOp;

    /// Performs a binary operation on this value.
    fn binary_op(self, state: &mut S, op: Self::BinaryOp, rhs: Rhs) -> Self;
}

/// Binary operations that can be performed on a Boolean value.
pub enum BoolBinaryOp {
    And,
    Or,
}

/// Unary operations that can be performed on a Boolean value.
pub enum BoolUnaryOp {
    Not,
}
