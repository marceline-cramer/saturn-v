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

use crate::*;

/// A wrapper for types that can be partially-evaluated.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum PartialValue<C, V> {
    Const(C),
    Variable(V),
}

impl<C, V> PartialValue<C, V> {
    /// Fully evaluate (i.e. convert to const).
    pub fn eval(self, cb: impl FnOnce(V) -> C) -> C {
        match self {
            PartialValue::Const(value) => value,
            PartialValue::Variable(var) => cb(var),
        }
    }

    /// Filter out constants.
    pub fn variable(self) -> Option<V> {
        match self {
            PartialValue::Const(_) => None,
            PartialValue::Variable(var) => Some(var),
        }
    }
}

impl<E: PartialEncoder<bool>> Encoder<bool> for E {
    type Repr = PartialValue<bool, E::Repr>;

    fn fresh(&self) -> Self::Repr {
        PartialValue::Variable(self.fresh_variable())
    }

    fn from_const(&self, value: impl Into<bool>) -> Self::Repr {
        PartialValue::Const(value.into())
    }

    fn to_const(&self, repr: Self::Repr) -> Option<bool> {
        match repr {
            PartialValue::Const(value) => Some(value),
            PartialValue::Variable(_) => None,
        }
    }

    fn unary_op(&self, op: BoolUnaryOp, repr: Self::Repr) -> Self::Repr {
        use PartialValue::*;
        match repr {
            Variable(var) => Variable(self.unary_op_variable(op, var)),
            Const(value) => match op {
                BoolUnaryOp::Not => Const(!value),
            },
        }
    }

    fn binary_op(&self, op: BoolBinaryOp, lhs: Self::Repr, rhs: Self::Repr) -> Self::Repr {
        use PartialValue::*;
        match (lhs, rhs) {
            (Variable(lhs), Variable(rhs)) => self.binary_op_variable(op, lhs, rhs),
            (Variable(lhs), Const(rhs)) | (Const(rhs), Variable(lhs)) => {
                self.binary_op_const(op, lhs, rhs)
            }
            (Const(lhs), Const(rhs)) => Const(match op {
                BoolBinaryOp::And => lhs && rhs,
                BoolBinaryOp::Or => lhs || rhs,
            }),
        }
    }
}

/// An encoder that relies on partial evaluation for constant values.
pub trait PartialEncoder<T: Ops> {
    /// The representation of variable values in the encoder.
    type Repr: Clone + 'static;

    /// Creates a fresh, uninterpreted variable value.
    fn fresh_variable(&self) -> Self::Repr;

    /// Evaluates a unary operation on a variable.
    fn unary_op_variable(&self, op: T::UnaryOp, repr: Self::Repr) -> Self::Repr;

    /// Evaluates a binary operation of a variable against a constant.
    fn binary_op_const(
        &self,
        op: T::BinaryOp,
        lhs: Self::Repr,
        rhs: T,
    ) -> PartialValue<T, Self::Repr>;

    /// Evaluates a binary operation of a variable against another variable.
    fn binary_op_variable(
        &self,
        op: T::BinaryOp,
        lhs: Self::Repr,
        rhs: Self::Repr,
    ) -> PartialValue<T, Self::Repr>;
}
