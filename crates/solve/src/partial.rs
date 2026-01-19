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

impl<S, V> UnaryOp<S> for PartialValue<bool, V>
where
    V: UnaryOp<S, Op = BoolUnaryOp>,
{
    type Op = BoolUnaryOp;

    fn unary_op(self, state: &mut S, op: Self::Op) -> Self {
        let value = match self {
            PartialValue::Const(value) => value,
            PartialValue::Variable(var) => return PartialValue::Variable(var.unary_op(state, op)),
        };

        match op {
            BoolUnaryOp::Not => PartialValue::Const(!value),
        }
    }
}

impl<S, C, V, Op> BinaryOp<S> for PartialValue<C, V>
where
    V: BinaryOp<S, Op = Op>,
    PartialValue<C, V>: BinaryOp<S, C, Op = Op>,
    Op: Commutative,
{
    type Op = Op;

    fn binary_op(self, state: &mut S, op: Self::Op, rhs: Self) -> Self {
        use PartialValue::*;
        match (self, rhs) {
            (Variable(lhs), Variable(rhs)) => Variable(lhs.binary_op(state, op, rhs)),
            (partial, Const(rhs)) | (Const(rhs), partial) => partial.binary_op(state, op, rhs),
        }
    }
}

impl<S> BinaryOp<S> for bool {
    type Op = BoolBinaryOp;

    fn binary_op(self, _state: &mut S, op: Self::Op, rhs: Self) -> Self {
        use BoolBinaryOp::*;
        match op {
            And => self && rhs,
            Or => self || rhs,
        }
    }
}
