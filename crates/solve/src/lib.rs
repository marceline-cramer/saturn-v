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
// TODO: hash-consing memoization wrappers

/// A solver for a given [Model].
pub trait Solver<M: Model> {}

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
    fn from_const(state: S, value: T) -> Self;
}

/// Convert a value to a Rust value.
pub trait ToRust<S: ?Sized, T> {
    /// Attempts to convert a value of this type to a Rust value.
    fn to_const(&self, state: S) -> Option<T>;
}

/// Create a unique, unconstrained value.
///
/// If a value is equivalent via [Eq], it is guaranteed to refer only to the
/// same fresh value.
pub trait Fresh<S: ?Sized>: Eq {
    /// Create an unconstrained value.
    fn fresh(state: S) -> Self;
}

/// Operations on values with the given state as context.
pub trait Value<S: ?Sized>: BinaryOp<S, Self> {
    /// The type of unary operations on this value.
    type UnaryOp;

    /// Performs a unary operation on this value.
    fn unary_op(self, state: S, op: Self::UnaryOp) -> Self;
}

/// Implements binary operations with a specific right-hand operand type.
pub trait BinaryOp<S: ?Sized, Rhs: ?Sized> {
    /// The type of binary operations on this value.
    type BinaryOp;

    /// Performs a binary operation on this value.
    fn binary_op(self, state: S, op: Self::BinaryOp, rhs: Rhs) -> Self;
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
