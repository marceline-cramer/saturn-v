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

impl<E, C: Eq, V: Fresh<E>> Fresh<E> for PartialValue<C, V> {
    fn fresh(encoder: &mut E) -> Self {
        PartialValue::Variable(V::fresh(encoder))
    }
}

impl<E, C, V> FromRust<E, C> for PartialValue<C, V> {
    fn from_const(_encoder: &mut E, value: C) -> Self {
        PartialValue::Const(value)
    }
}

impl<E, C: Clone, V: ToRust<E, C>> ToRust<E, C> for PartialValue<C, V> {
    fn to_const(&self, encoder: &mut E) -> Option<C> {
        match self {
            PartialValue::Const(value) => Some(value.clone()),
            PartialValue::Variable(var) => var.to_const(encoder),
        }
    }
}

impl<E, V> UnaryOp<E> for PartialValue<bool, V>
where
    V: UnaryOp<E, Op = BoolUnaryOp>,
{
    type Op = BoolUnaryOp;

    fn unary_op(self, encoder: &mut E, op: Self::Op) -> Self {
        let value = match self {
            PartialValue::Const(value) => value,
            PartialValue::Variable(var) => {
                return PartialValue::Variable(var.unary_op(encoder, op))
            }
        };

        match op {
            BoolUnaryOp::Not => PartialValue::Const(!value),
        }
    }
}

impl<E, C, V, Op> BinaryOp<E> for PartialValue<C, V>
where
    V: BinaryOp<E, Op = Op>,
    PartialValue<C, V>: BinaryOp<E, C, Op = Op>,
    Op: Commutative,
{
    type Op = Op;

    fn binary_op(self, encoder: &mut E, op: Self::Op, rhs: Self) -> Self {
        use PartialValue::*;
        match (self, rhs) {
            (Variable(lhs), Variable(rhs)) => Variable(lhs.binary_op(encoder, op, rhs)),
            (partial, Const(rhs)) | (Const(rhs), partial) => partial.binary_op(encoder, op, rhs),
        }
    }
}

impl<E> BinaryOp<E> for bool {
    type Op = BoolBinaryOp;

    fn binary_op(self, _encoder: &mut E, op: Self::Op, rhs: Self) -> Self {
        use BoolBinaryOp::*;
        match op {
            And => self && rhs,
            Or => self || rhs,
        }
    }
}
