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

#![warn(missing_docs)]

use ordered_float::OrderedFloat;
pub use saturn_v_ir::{self as ir, StructuredType};
use serde::{Deserialize, Serialize};
use thiserror::Error;

pub type ServerResult<T> = std::result::Result<T, ServerError>;

#[derive(Clone, Debug, PartialEq, Eq, Error, Deserialize, Serialize)]
pub enum ServerError {
    #[error("program did not pass validation. error: {0}")]
    InvalidProgram(ir::validate::Error<String>),

    #[error("no program is loaded")]
    NoProgramLoaded,

    #[error("input with ID {0:?} does not exist")]
    NoSuchInput(String),

    #[error("output with ID {0:?} does not exist")]
    NoSuchOutput(String),

    #[error("type mismatch: expected {expected}, got {got}")]
    TypeMismatch {
        expected: StructuredType,
        got: StructuredType,
    },

    #[error("the server had an internal database error")]
    DatabaseError,

    #[error("the transaction had a conflict and was rolled back")]
    Conflict,

    #[error("the server side event stream has lagged")]
    Lagged,
}

/// An individual tuple update within a relation.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Deserialize, Serialize)]
pub struct TupleUpdate {
    /// The new state of the tuple. `true` for present, `false` for absent.
    pub state: bool,

    /// The tuple being updated.
    pub value: StructuredValue,
}

/// The metadata for a relation (input or output).
#[derive(Clone, Debug, PartialEq, Eq, Hash, Deserialize, Serialize)]
pub struct RelationInfo {
    /// A user-readable name for the relation.
    pub name: String,

    /// A identifier for this relation unique to the currently loaded program.
    pub id: String,

    /// The type of this relation.
    pub ty: StructuredType,
}

impl RelationInfo {
    /// Helper method to test if a type matches this relation.
    pub fn check_ty<T: Typed>(&self) -> ServerResult<()> {
        if self.matches_ty::<T>() {
            Ok(())
        } else {
            Err(ServerError::TypeMismatch {
                expected: self.ty.clone(),
                got: T::ty(),
            })
        }
    }

    /// Checks if a typed Saturn V value matches this relation's type.
    pub fn matches_ty<T: Typed>(&self) -> bool {
        T::ty() == self.ty
    }
}

/// A monotonically increasing identifier for input transaction results.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Deserialize, Serialize)]
pub struct SequenceId(pub u64);

/// A Saturn V-compatible value type.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Deserialize, Serialize)]
pub enum StructuredValue {
    /// A nested list of other values.
    Tuple(Vec<StructuredValue>),

    /// A string value.
    String(String),

    /// A Boolean value.
    Boolean(bool),

    /// An integer value.
    Integer(i64),

    /// A real-numbered value, approximated as a float.
    Real(OrderedFloat<f64>),

    /// A symbol.
    Symbol(String),
}

impl StructuredValue {
    /// Returns the type of this value.
    pub fn ty(&self) -> StructuredType {
        use ir::{StructuredType::*, Type::*};
        match self {
            StructuredValue::Tuple(els) => Tuple(els.iter().map(|val| val.ty()).collect()),
            StructuredValue::String(_) => Primitive(String),
            StructuredValue::Boolean(_) => Primitive(Boolean),
            StructuredValue::Integer(_) => Primitive(Integer),
            StructuredValue::Real(_) => Primitive(Real),
            StructuredValue::Symbol(_) => Primitive(Symbol),
        }
    }
}

/// A trait for Rust types that have corresponding Saturn V types.
pub trait Typed {
    /// Retrieves the Saturn V type for this type.
    fn ty() -> StructuredType;
}

/// Converts a Rust type into a Saturn V type.
pub trait AsValue: Typed {
    /// Converts this Rust value to a [Value].
    fn as_value(&self) -> StructuredValue;
}

/// Converts a Saturn V type into a Rust type.
pub trait FromValue: Typed {
    /// Converts to this Rust value from a [Value].
    fn from_value(val: StructuredValue) -> Self;
}

macro_rules! impl_typed_primitive {
    ($ty:ty, $name:ident) => {
        impl Typed for $ty {
            fn ty() -> StructuredType {
                StructuredType::Primitive(ir::Type::$name)
            }
        }

        impl AsValue for $ty {
            fn as_value(&self) -> StructuredValue {
                StructuredValue::$name(self.clone().into())
            }
        }

        impl FromValue for $ty {
            fn from_value(val: StructuredValue) -> Self {
                match val {
                    StructuredValue::$name(inner) => inner.into(),
                    _ => unreachable!(),
                }
            }
        }
    };
}

impl_typed_primitive!(String, String);
impl_typed_primitive!(bool, Boolean);
impl_typed_primitive!(i64, Integer);
impl_typed_primitive!(f64, Real);
impl_typed_primitive!(OrderedFloat<f64>, Real);

macro_rules! impl_typed_tuple {
    ($($el:ident),+) => {
        impl<$($el: Typed),+> Typed for ($($el),+) {
            fn ty() -> StructuredType {
                StructuredType::Tuple(vec![$($el::ty()),+])
            }
        }

        impl<$($el: AsValue),+> AsValue for ($($el),+) {
            #[allow(non_snake_case)]
            fn as_value(&self) -> StructuredValue {
                let ($($el),+) = self;
                StructuredValue::Tuple(vec![$($el.as_value()),+])
            }
        }

        impl<$($el: FromValue),+> FromValue for ($($el),+) {
            #[allow(non_snake_case)]
            fn from_value(val: StructuredValue) -> Self {
                let els = match val {
                    StructuredValue::Tuple(els) => els,
                    _ => unreachable!(),
                };

                let mut els = els.into_iter();
                $(let $el = els.next().unwrap();)+
                ($($el::from_value($el)),+)
            }
        }
    };
}

macro_rules! typed_tuple {
    ($base:ident) => {};
    ($head:ident, $($tail:ident),+) => {
        impl_typed_tuple!($head, $($tail),+);
        typed_tuple!($($tail),+);
    };
}

typed_tuple!(A, B, C, D, E, F, G, H);

/// Type alias for IR programs that can be loaded on the server.
pub type Program = ir::Program<String>;
