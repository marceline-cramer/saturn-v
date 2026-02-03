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

pub mod partial;

#[cfg(feature = "sat")]
pub mod sat;

#[cfg(feature = "z3")]
pub mod z3;

#[cfg(test)]
pub mod tests;

// TODO: consider a lazy encoding wrapper to minimize cost of large aggregates

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

impl<S: Solver, T: Ops> Encoder<T> for S
where
    S::Model: Encoder<T>,
{
    type Repr = <<S as Solver>::Model as Encoder<T>>::Repr;

    fn fresh(&self) -> Self::Repr {
        self.as_model().fresh()
    }

    fn from_const(&self, value: impl Into<T>) -> Self::Repr {
        self.as_model().from_const(value)
    }

    fn to_const(&self, repr: Self::Repr) -> Option<T> {
        self.as_model().to_const(repr)
    }

    fn unary_op(&self, op: <T as Ops>::UnaryOp, repr: Self::Repr) -> Self::Repr {
        self.as_model().unary_op(op, repr)
    }

    fn binary_op(&self, op: <T as Ops>::BinaryOp, lhs: Self::Repr, rhs: Self::Repr) -> Self::Repr {
        self.as_model().binary_op(op, lhs, rhs)
    }
}

/// Parameters for a [Solver] run.
pub struct SolveOptions<'a, M: Model> {
    /// The hard assumptions.
    pub hard: &'a [Bool<M>],

    /// The soft assumptions to use.
    pub soft: &'a [(Bool<M>, u32)],

    /// The Boolean values to evaluate after solving.
    pub bool_eval: &'a [Bool<M>],
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
        matches!(self, SolveResult::Unsat)
    }
}

/// Type alias for the representation of Boolean values in an encoder.
pub type Bool<M: Encoder<bool>> = M::Repr;

/// An incrementally-constructed logic model.
pub trait Model: Encoder<bool> {}

/// Operations for manipulated encoded values.
pub trait Encoder<T: Ops> {
    /// The representation of this value in the solver.
    type Repr: Copy + Send + Sync + 'static;

    /// Creates a fresh, uninterpreted variable.
    fn fresh(&self) -> Self::Repr;

    /// Creates a value of this type from a Rust constant.
    fn from_const(&self, value: impl Into<T>) -> Self::Repr;

    /// Attempts to convert a value of this type back to a constant.
    fn to_const(&self, repr: Self::Repr) -> Option<T>;

    /// Encodes a unary operation on a value.
    fn unary_op(&self, op: T::UnaryOp, repr: Self::Repr) -> Self::Repr;

    /// Encodes a binary operation on two values.
    fn binary_op(&self, op: T::BinaryOp, lhs: Self::Repr, rhs: Self::Repr) -> Self::Repr;
}

/// Defines associated operation kinds on a type.
pub trait Ops {
    /// The type of unary operations on this value.
    type UnaryOp;

    /// The type of binary operations on this value.
    type BinaryOp;
}

impl Ops for bool {
    type BinaryOp = BoolBinaryOp;
    type UnaryOp = BoolUnaryOp;
}

/// Binary operations that can be performed on a Boolean value.
pub enum BoolBinaryOp {
    And,
    Or,
}

impl Commutative for BoolBinaryOp {}

/// Unary operations that can be performed on a Boolean value.
pub enum BoolUnaryOp {
    Not,
}

/// A marker trait for binary operations that are always commutative.
pub trait Commutative {}
