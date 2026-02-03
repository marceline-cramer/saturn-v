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

use ::z3::{ast, Optimize, SatResult};

use crate::*;

#[derive(Default)]
pub struct Z3Solver {
    inner: Optimize,
    model: Z3Model,
}

impl Solver for Z3Solver {
    type Model = Z3Model;

    fn solve(&mut self, opts: SolveOptions<Self::Model>) -> SolveResult {
        // push unconstrained solver state
        self.inner.push();

        // add soft constraints
        for (soft, weight) in opts.soft {
            self.inner.assert_soft(soft, *weight, None);
        }

        // run solver
        let result = self.inner.check(opts.hard);

        // fetch model info before popping solver
        let model = self.inner.get_model();

        // discard temporary assertions
        self.inner.pop();

        // handle solve result
        match result {
            SatResult::Unsat => return SolveResult::Unsat,
            SatResult::Unknown => return SolveResult::Unknown,
            SatResult::Sat => {}
        }

        // unwrap model now that we know it's SAT
        let model = model.unwrap();

        // calculate cost value
        let cost = opts
            .soft
            .iter()
            .filter(|(soft, _cost)| !model.eval(soft, true).unwrap().as_bool().unwrap())
            .map(|(_soft, cost)| cost)
            .sum();

        // evaluate requests bools
        let bool_values = opts
            .bool_eval
            .iter()
            .map(|val| model.eval(val, true).unwrap().as_bool().unwrap())
            .collect();

        // return complete SAT info
        SolveResult::Sat { cost, bool_values }
    }

    fn as_model(&self) -> &Self::Model {
        &self.model
    }

    fn into_model(self) -> Self::Model {
        self.model
    }
}

#[derive(Default)]
pub struct Z3Model {}

impl Model for Z3Model {}

impl Encoder<bool> for Z3Model {
    type Repr = ast::Bool;

    fn fresh(&self) -> Self::Repr {
        ast::Bool::fresh_const("Encoder<bool>")
    }

    fn from_const(&self, value: impl Into<bool>) -> Self::Repr {
        ast::Bool::from_bool(value.into())
    }

    fn to_const(&self, repr: Self::Repr) -> Option<bool> {
        repr.as_bool()
    }

    fn unary_op(&self, op: <bool as Ops>::UnaryOp, repr: Self::Repr) -> Self::Repr {
        match op {
            BoolUnaryOp::Not => repr.not(),
        }
    }

    fn binary_op(
        &self,
        op: <bool as Ops>::BinaryOp,
        lhs: Self::Repr,
        rhs: Self::Repr,
    ) -> Self::Repr {
        match op {
            BoolBinaryOp::And => ast::Bool::and(&[lhs, rhs]),
            BoolBinaryOp::Or => ast::Bool::or(&[lhs, rhs]),
        }
    }
}
