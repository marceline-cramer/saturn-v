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

use crate::*;

/// A wrapper for types that can be partially-evaluated.
#[derive(PartialEq, Eq)]
pub enum PartialValue<C, V> {
    Const(C),
    Variable(V),
}

impl<S, C: Eq, V: Fresh<S>> Fresh<S> for PartialValue<C, V> {
    fn fresh(state: &mut S) -> Self {
        PartialValue::Variable(V::fresh(state))
    }
}

impl<S, C, V> FromRust<S, C> for PartialValue<C, V> {
    fn from_const(_state: &mut S, value: C) -> Self {
        PartialValue::Const(value)
    }
}

impl<S, C: Clone, V: ToRust<S, C>> ToRust<S, C> for PartialValue<C, V> {
    fn to_const(&self, state: &mut S) -> Option<C> {
        match self {
            PartialValue::Const(value) => Some(value.clone()),
            PartialValue::Variable(var) => var.to_const(state),
        }
    }
}

impl<S, V> Value<S> for PartialValue<bool, V>
where
    V: Value<S, UnaryOp = BoolUnaryOp, BinaryOp = BoolBinaryOp>
        + BinaryOp<S, V, BinaryOp = BoolBinaryOp>
        + BinaryOp<S, bool, BinaryOp = BoolBinaryOp>,
{
    type UnaryOp = V::UnaryOp;

    fn unary_op(self, state: &mut S, op: Self::UnaryOp) -> Self {
        let value = match self {
            PartialValue::Const(value) => value,
            PartialValue::Variable(var) => return PartialValue::Variable(var.unary_op(state, op)),
        };

        match op {
            BoolUnaryOp::Not => PartialValue::Const(!value),
        }
    }
}

impl<S, V> BinaryOp<S, Self> for PartialValue<bool, V>
where
    V: BinaryOp<S, V, BinaryOp = BoolBinaryOp> + BinaryOp<S, bool, BinaryOp = BoolBinaryOp>,
{
    type BinaryOp = BoolBinaryOp;

    fn binary_op(self, state: &mut S, op: Self::BinaryOp, rhs: Self) -> Self {
        use PartialValue::*;

        // all Boolean operations are commutative, so matching is straightforward
        let (lhs, rhs) = match (self, rhs) {
            (Variable(lhs), Variable(rhs)) => return Variable(lhs.binary_op(state, op, rhs)),
            (Const(lhs), rhs) | (rhs, Const(lhs)) => (lhs, rhs),
        };

        // handle constant-variable arithmetic
        let rhs = match rhs {
            Const(value) => value,
            Variable(var) => return Variable(var.binary_op(state, op, lhs)),
        };

        // implement constant-constant arithmetic
        Const(match op {
            BoolBinaryOp::And => lhs && rhs,
            BoolBinaryOp::Or => lhs || rhs,
        })
    }
}
