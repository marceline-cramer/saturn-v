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

    /// Filter out variables.
    pub fn as_const(self) -> Option<C> {
        match self {
            PartialValue::Const(value) => Some(value),
            PartialValue::Variable(_) => None,
        }
    }

    /// Filter out constants.
    pub fn as_variable(self) -> Option<V> {
        match self {
            PartialValue::Const(_) => None,
            PartialValue::Variable(var) => Some(var),
        }
    }
}

impl<E: PartialPbEncoder> PbEncoder for E {
    fn pb(&self, kind: PbKind, thresh: i32, terms: &[(&Bool<E>, i32)]) -> Bool<Self> {
        use PartialValue::*;
        use PbKind::*;

        // remove sign from weights
        let terms = terms.iter().map(|(value, weight)| {
            let weight: u32 = (*weight).try_into().expect("weights must be non-negative");
            (value.to_owned(), weight)
        });

        // assert non-negative weight
        let thresh: u32 = thresh.try_into().expect("threshold must be non-negative");

        // calculate a constant lower bound on the PB sum
        let lb: u32 = terms
            .clone()
            .filter(|(value, _)| value.to_owned().to_owned().as_const().unwrap_or(false))
            .map(|(_value, weight)| weight)
            .sum();

        // calculate a constant lower bound on the PB sum
        let ub: u32 = terms
            .clone()
            .filter(|(value, _)| value.to_owned().to_owned().as_const().unwrap_or(true))
            .map(|(_value, weight)| weight)
            .sum();

        // early constant evaluation
        if lb == ub {
            let const_eval = match kind {
                Eq => ub == thresh,
                Le => ub <= thresh,
                Ge => ub >= thresh,
            };

            return Const(const_eval);
        }

        // extract variable-only terms
        let var_terms = terms.clone().flat_map(|(value, weight)| {
            value.clone().clone().as_variable().map(|var| (var, weight))
        });

        // if all variable term weights are one, this is a cardinality constraint
        let is_card = var_terms.clone().all(|(_var, weight)| weight == 1);

        // extract variables from variable-only terms
        let vars = var_terms.clone().map(|(var, _weight)| var);

        // negate variables
        let not_vars = vars
            .clone()
            .map(|var| self.unary_op_variable(BoolUnaryOp::Not, var));

        // select best fine-grained encoding based on constant lower bound
        match kind {
            // if bounds have exceeded range of constraint, return const false
            Eq | Le if lb > thresh => return Const(false),
            Eq | Ge if ub < thresh => return Const(false),

            // if bounds are always within range, return const true
            Ge if lb >= thresh => return Const(true),
            Le if ub <= thresh => return Const(true),

            // if only extrema of bounds are within range, constrain all variables
            Eq | Ge if ub == thresh => Variable(self.none_of(not_vars)),
            Eq | Le if lb == thresh => Variable(self.none_of(vars)),

            // encode non-trivial constraints
            _ => {
                if is_card {
                    Variable(self.card_nontrivial(kind, (thresh - lb).try_into().unwrap(), vars))
                } else {
                    Variable(self.pb_nontrivial(kind, (thresh - lb).try_into().unwrap(), var_terms))
                }
            }
        }
    }
}

/// A pseudo-Boolean constraint encoder that does preprocessing on partial evaluation.
pub trait PartialPbEncoder: PartialEncoder<bool> {
    /// Encodes a Boolean "nor" operation of arbitrary arity.
    fn none_of(&self, terms: impl IntoIterator<Item = Self::Repr>) -> Self::Repr;

    /// Encodes a non-trivial cardinality constraint.
    fn card_nontrivial(
        &self,
        kind: PbKind,
        thresh: u32,
        terms: impl IntoIterator<Item = Self::Repr>,
    ) -> Self::Repr;

    /// Encodes a non-trivial pseudo-Boolean constraint.
    fn pb_nontrivial(
        &self,
        kind: PbKind,
        thresh: u32,
        terms: impl IntoIterator<Item = (Self::Repr, u32)>,
    ) -> Self::Repr;
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
