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

    fn as_model(&mut self) -> &mut Self::Model {
        &mut self.model
    }

    fn into_model(self) -> Self::Model {
        self.model
    }
}

#[derive(Default)]
pub struct Z3Model {}

impl Model for Z3Model {
    type Bool = Z3Bool;
}

pub type Z3Bool = ast::Bool;

impl<S> Fresh<S> for Z3Bool {
    fn fresh(_state: &mut S) -> Self {
        Z3Bool::fresh_const("Z3Bool")
    }
}

impl<S> FromRust<S, bool> for Z3Bool {
    fn from_const(_state: &mut S, value: bool) -> Self {
        Z3Bool::from_bool(value)
    }
}

impl<S> ToRust<S, bool> for Z3Bool {
    fn to_const(&self, _state: &mut S) -> Option<bool> {
        self.as_bool()
    }
}

impl<S> Value<S> for Z3Bool {
    type UnaryOp = BoolUnaryOp;

    fn unary_op(self, _state: &mut S, op: Self::UnaryOp) -> Self {
        match op {
            BoolUnaryOp::Not => self.not(),
        }
    }
}

impl<S> BinaryOp<S, Z3Bool> for Z3Bool {
    type BinaryOp = BoolBinaryOp;

    fn binary_op(self, _state: &mut S, op: Self::BinaryOp, rhs: Self) -> Self {
        match op {
            BoolBinaryOp::And => Z3Bool::and(&[self, rhs]),
            BoolBinaryOp::Or => Z3Bool::or(&[self, rhs]),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_assume_true() {
        let mut solver = Z3Solver::default();
        let model = solver.as_model();
        let val = Z3Bool::from_const(model, true);

        let result = solver.solve(SolveOptions {
            hard: &[val],
            ..Default::default()
        });

        assert!(result.is_sat());
    }

    #[test]
    fn test_assume_false() {
        let mut solver = Z3Solver::default();
        let model = solver.as_model();
        let val = Z3Bool::from_const(model, false);

        let result = solver.solve(SolveOptions {
            hard: &[val],
            ..Default::default()
        });

        assert!(result.is_unsat());
    }

    #[test]
    fn test_assume_not_false() {
        let mut solver = Z3Solver::default();
        let model = solver.as_model();
        let val = Z3Bool::from_const(model, false);
        let not_val = val.unary_op(model, BoolUnaryOp::Not);

        let result = solver.solve(SolveOptions {
            hard: &[not_val],
            ..Default::default()
        });

        assert!(result.is_sat());
    }

    #[test]
    fn test_assume_not_true() {
        let mut solver = Z3Solver::default();
        let model = solver.as_model();
        let val = Z3Bool::from_const(model, true);
        let not_val = val.unary_op(model, BoolUnaryOp::Not);

        let result = solver.solve(SolveOptions {
            hard: &[not_val],
            ..Default::default()
        });

        assert!(result.is_unsat());
    }

    #[test]
    fn test_assume_fresh() {
        let mut solver = Z3Solver::default();
        let model = solver.as_model();
        let val = Z3Bool::fresh(model);

        let result = solver.solve(SolveOptions {
            hard: &[val.clone()],
            bool_eval: &[val],
            ..Default::default()
        });

        assert_eq!(
            result,
            SolveResult::Sat {
                cost: 0,
                bool_values: vec![true]
            }
        );
    }

    #[test]
    fn test_and_nor_unsat() {
        let mut solver = Z3Solver::default();
        let model = solver.as_model();
        let lhs = Z3Bool::fresh(model);
        let rhs = Z3Bool::fresh(model);

        let and = lhs.clone().binary_op(model, BoolBinaryOp::And, rhs.clone());
        let or = lhs.binary_op(model, BoolBinaryOp::Or, rhs);
        let nor = or.unary_op(model, BoolUnaryOp::Not);

        let result = solver.solve(SolveOptions {
            hard: &[and, nor],
            ..Default::default()
        });

        assert!(result.is_unsat());
    }

    #[test]
    fn test_minimize_either_or() {
        let mut solver = Z3Solver::default();
        let model = solver.as_model();
        let lhs = Z3Bool::fresh(model);
        let rhs = Z3Bool::fresh(model);

        let and = lhs.clone().binary_op(model, BoolBinaryOp::And, rhs.clone());
        let nand = and.clone().unary_op(model, BoolUnaryOp::Not);

        let result = solver.solve(SolveOptions {
            hard: &[nand],
            soft: &[(lhs.clone(), 1), (rhs.clone(), 2)],
            bool_eval: &[and, lhs, rhs],
        });

        assert_eq!(
            result,
            SolveResult::Sat {
                cost: 1,
                bool_values: vec![false, false, true]
            }
        );
    }
}
