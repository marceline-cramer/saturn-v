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

fn test_assume_true<S: Solver + Default>() {
    let mut solver = S::default();
    let val = solver.as_model().from_const(true);

    let result = solver.solve(SolveOptions {
        hard: &[val],
        ..Default::default()
    });

    assert!(result.is_sat());
}

fn test_assume_false<S: Solver + Default>() {
    let mut solver = S::default();
    let val = solver.as_model().from_const(false);

    let result = solver.solve(SolveOptions {
        hard: &[val],
        ..Default::default()
    });

    assert!(result.is_unsat());
}

fn test_assume_not_false<S: Solver + Default>() {
    let mut solver = S::default();
    let model = solver.as_model();
    let val = model.from_const(false);
    let not_val = model.unary_op(BoolUnaryOp::Not, val);

    let result = solver.solve(SolveOptions {
        hard: &[not_val],
        ..Default::default()
    });

    assert!(result.is_sat());
}

fn test_assume_not_true<S: Solver + Default>() {
    let mut solver = S::default();
    let model = solver.as_model();
    let val = model.from_const(true);
    let not_val = model.unary_op(BoolUnaryOp::Not, val);

    let result = solver.solve(SolveOptions {
        hard: &[not_val],
        ..Default::default()
    });

    assert!(result.is_unsat());
}

fn test_assume_fresh<S: Solver + Default>() {
    let mut solver = S::default();
    let val = solver.as_model().fresh();

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

fn test_and_nor_unsat<S: Solver + Default>() {
    let mut solver = S::default();
    let model = solver.as_model();

    let lhs = model.fresh();
    let rhs = model.fresh();

    let and = model.binary_op(BoolBinaryOp::And, lhs.clone(), rhs.clone());
    let or = model.binary_op(BoolBinaryOp::Or, lhs, rhs);
    let nor = model.unary_op(BoolUnaryOp::Not, or);

    let result = solver.solve(SolveOptions {
        hard: &[and, nor],
        ..Default::default()
    });

    assert!(result.is_unsat());
}

fn test_minimize_either_or<S: Solver + Default>() {
    let mut solver = S::default();
    let model = solver.as_model();

    let lhs = model.fresh();
    let rhs = model.fresh();

    let and = model.binary_op(BoolBinaryOp::And, lhs.clone(), rhs.clone());
    let nand = model.unary_op(BoolUnaryOp::Not, and.clone());

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

macro_rules! tests_with_solver {
    ($solver:ty, ) => {};
    ($solver:ty, $head:ident $($rest:ident)*) => {
        #[test]
        fn $head() {
            super::$head::<$solver>();
        }

        tests_with_solver!($solver, $($rest)*);
    };
}

macro_rules! tests_all_solvers {
    ($($tests:ident)*) => {
        #[cfg(feature = "sat")]
        pub mod sat {
            tests_with_solver!(crate::sat::SatSolver<rustsat_cadical::CaDiCaL>, $($tests)*);
        }

        #[cfg(feature = "z3")]
        pub mod z3 {
            tests_with_solver!(crate::z3::Z3Solver, $($tests)*);
        }
    }
}

tests_all_solvers!(
    test_assume_true
    test_assume_false
    test_assume_not_false
    test_assume_not_true
    test_assume_fresh
    test_and_nor_unsat
    test_minimize_either_or
);
