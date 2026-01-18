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

pub struct Z3Solver {
    inner: ::z3::Solver,
}

impl Solver<Z3Model> for Z3Solver {}

pub struct Z3Model;

impl Model for Z3Model {
    type Bool = Z3Bool;
}

pub struct Z3Bool;

impl<S> FromRust<S, bool> for Z3Bool {
    fn from_const(state: S, value: bool) -> Self {
        todo!()
    }
}

impl<S> ToRust<S, bool> for Z3Bool {
    fn to_const(&self, state: S) -> Option<bool> {
        todo!()
    }
}

impl<S> Value<S> for Z3Bool {
    type UnaryOp = BoolUnaryOp;

    fn unary_op(self, _state: S, op: Self::UnaryOp) -> Self {
        todo!()
    }
}

impl<S> BinaryOp<S, Z3Bool> for Z3Bool {
    type BinaryOp = BoolBinaryOp;

    fn binary_op(self, _state: S, op: Self::BinaryOp, rhs: Self) -> Self {
        todo!()
    }
}
