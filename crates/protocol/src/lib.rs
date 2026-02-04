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

//! Defines the network protocol for interacting with the Saturn V server.

#![warn(missing_docs)]

use std::{borrow::Cow, collections::BTreeSet, future::Future, marker::PhantomData};

use ordered_float::OrderedFloat;
use serde::{de::DeserializeOwned, Deserialize, Serialize};
use thiserror::Error;
use wasm_bindgen::prelude::*;

pub use saturn_v_ir::{self as ir, StructuredType};

/// A trait that bounds the handling of the entire server RPC interface.
///
/// This is used server-side to bound the server but also client-side to bound
/// a complete RPC protocol implementation.
pub trait Rpc:
    HandleTx<GetProgram>
    + HandleTx<SetProgram>
    + HandleTx<ListInputs>
    + HandleTx<GetInput>
    + HandleTx<UpdateInput>
    + HandleTx<ListOutputs>
    + HandleTx<GetOutput>
{
}

/// Implements a subscription handler for a subscription type.
pub trait HandleSubscribe<T: Subscription> {
    /// Handles a whole subscription lifetime.
    ///
    /// The future lasts the duration of the subscription if successful or
    /// will return with an error if either subscribing or unsubscribing is
    /// unsuccessful.
    fn on_subscribe(
        &self,
        request: T,
        on_update: impl FnMut(T::Response) + Send,
    ) -> impl Future<Output = ServerResult<()>> + Send;
}

/// Implements a request handler for a transactional method.
///
/// All transactional requests can also be executed in one-shot commits using
/// [TxMethod].
pub trait HandleTx<T: TxRequest>:
    Handle<T> + Handle<BeginTx> + Handle<CommitTx> + Handle<TxMethod<T>>
{
}

impl<T: TxRequest, H> HandleTx<T> for H where
    H: Handle<T> + Handle<BeginTx> + Handle<CommitTx> + Handle<TxMethod<T>>
{
}

/// Implements a request handler for a particular request type.
pub trait Handle<T: Request> {
    /// Handles a given request.
    fn on_request(&self, request: T) -> impl Future<Output = ServerResult<T::Response>> + Send;
}

/// Retrieves the current loaded program.
#[derive(Deserialize, Serialize)]
pub struct GetProgram {}

impl TxRequest for GetProgram {
    type Response = Program;

    fn name() -> Cow<'static, str> {
        "GetProgram".into()
    }
}

/// Sets the current program.
#[derive(Deserialize, Serialize)]
pub struct SetProgram {
    /// The program to set.
    pub program: Program,
}

impl TxRequest for SetProgram {
    type Response = ();

    fn name() -> Cow<'static, str> {
        "SetProgram".into()
    }
}

/// Lists the information on each input relation.
#[derive(Deserialize, Serialize)]
pub struct ListInputs {}

impl TxRequest for ListInputs {
    type Response = Vec<RelationInfo>;

    fn name() -> Cow<'static, str> {
        "ListInputs".into()
    }
}

/// Retrieves all tuples currently occupying an input relation.
#[derive(Deserialize, Serialize)]
pub struct GetInput {
    /// The ID of the input relation.
    pub id: String,
}

impl TxRequest for GetInput {
    type Response = BTreeSet<StructuredValue>;

    fn name() -> Cow<'static, str> {
        "GetInput".into()
    }
}

/// Applies updates to the contents of an input relation.
#[derive(Deserialize, Serialize)]
pub struct UpdateInput {
    /// The ID of the input relation to update.
    pub id: String,

    /// A list of tuple updates to apply to the input.
    pub updates: Vec<TupleUpdate>,
}

impl TxRequest for UpdateInput {
    type Response = ();

    fn name() -> Cow<'static, str> {
        "UpdateInput".into()
    }
}

/// Lists the information on each output relation.
#[derive(Deserialize, Serialize)]
pub struct ListOutputs {}

impl TxRequest for ListOutputs {
    type Response = Vec<RelationInfo>;

    fn name() -> Cow<'static, str> {
        "ListOutputs".into()
    }
}

/// Retrieves all tuples currently occupying an output relation.
#[derive(Deserialize, Serialize)]
pub struct GetOutput {
    /// The ID of the output relation.
    pub id: String,
}

impl TxRequest for GetOutput {
    type Response = BTreeSet<StructuredValue>;

    fn name() -> Cow<'static, str> {
        "GetOutput".into()
    }
}

/// An RPC request to create a [Subscription].
#[derive(Deserialize, Serialize)]
pub struct Subscribe<T> {
    /// The request parameters to the subscription.
    pub param: T,

    /// The ID of the new subscription object.
    pub id: usize,
}

impl<T: Subscription> Request for Subscribe<T> {
    type Response = ();

    fn name() -> Cow<'static, str> {
        format!("Subscribe{}", T::name()).into()
    }
}

/// An RPC request to unsubscribe from and destroy an subscription object.
#[derive(Deserialize, Serialize)]
pub struct Unsubscribe<T> {
    /// The ID of the subscription object.
    pub id: usize,

    /// Ignore the type of the subscription.
    pub _phantom: PhantomData<T>,
}

impl<T: Subscription> Request for Unsubscribe<T> {
    type Response = ();

    fn name() -> Cow<'static, str> {
        format!("Unsubscribe{}", T::name()).into()
    }
}

/// The type of a subscription response notification.
#[derive(Deserialize, Serialize)]
pub struct SubscriptionEvent<T> {
    /// The ID of the subscription object.
    pub id: usize,

    /// The contents of the event.
    pub event: T,
}

/// An RPC subscription schema.
///
/// The `Self` type is the contents of the intial subscription request.
pub trait Subscription: DeserializeOwned + Serialize + Send + Sync {
    /// The name of this subscription object.
    fn name() -> Cow<'static, str>;

    /// The type of each element in the subscription's response.
    type Response: DeserializeOwned + Serialize + Sync;
}

/// Begins an atomic transaction.
#[derive(Deserialize, Serialize)]
pub struct BeginTx {
    /// The ID of this transaction.
    pub tx: usize,
}

impl Request for BeginTx {
    type Response = ();

    fn name() -> Cow<'static, str> {
        "BeginTx".into()
    }
}

/// Atomically commits a transaction with rollback on failure.
#[derive(Deserialize, Serialize)]
pub struct CommitTx {
    /// The ID of the transaction.
    pub tx: usize,
}

impl Request for CommitTx {
    type Response = TxOutput;

    fn name() -> Cow<'static, str> {
        "CommitTx".into()
    }
}

/// An RPC server request to the ambient request context.
pub trait Request: DeserializeOwned + Serialize + Send + Sync {
    /// The name of this request method.
    fn name() -> Cow<'static, str>;

    /// The type of this request's response.
    ///
    /// This is implicitly wrapped in [ServerResult].
    type Response: DeserializeOwned + Serialize + Sync;
}

impl<T: TxRequest> Request for T {
    type Response = TxResponse<T::Response>;

    fn name() -> Cow<'static, str> {
        T::name()
    }
}

/// Adds [TxOutput] to a response type.
#[derive(Deserialize, Serialize)]
pub struct TxResponse<T> {
    /// The output of the transactional commit.
    pub tx: TxOutput,

    /// The response to the particular method.
    pub response: T,
}

/// The result of a transactional commit.
#[derive(Deserialize, Serialize)]
pub struct TxOutput {}

/// Wraps a request with a transaction ID for context, making it a transaction method.
#[derive(Deserialize, Serialize)]
pub struct TxMethod<T> {
    /// The ID of this transaction.
    pub tx: usize,

    /// The inner method request.
    pub request: T,
}

impl<T: TxRequest> Request for TxMethod<T> {
    type Response = T::Response;

    fn name() -> Cow<'static, str> {
        format!("Tx{}", T::name()).into()
    }
}

/// A trait for transactional requests.
///
/// Transactional requests can be invoked as a transaction method to yield
/// their result or standalone outside of a method to receive their result and
/// the output of a one-shot committed transaction.
pub trait TxRequest: DeserializeOwned + Serialize + Send + Sync {
    /// The name of this request method.
    fn name() -> Cow<'static, str>;

    /// The type of this request's response.
    ///
    /// This is implicitly wrapped in [ServerResult].
    type Response: DeserializeOwned + Serialize + Sync;
}

/// A type alias for results that only have [ServerError] for errors.
pub type ServerResult<T> = std::result::Result<T, ServerError>;

/// An error originating from the server, usually stemming from incorrect use
/// of the API.
#[derive(Clone, Debug, PartialEq, Eq, Error, Deserialize, Serialize)]
#[allow(missing_docs)]
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
pub struct TupleUpdate<T = StructuredValue> {
    /// The new state of the tuple. `true` for present, `false` for absent.
    pub state: bool,

    /// The tuple being updated.
    pub value: T,
}

impl<T> TupleUpdate<T> {
    /// Maps this tuple update from one type to another.
    pub fn map<O>(self, cb: impl FnOnce(T) -> O) -> TupleUpdate<O> {
        TupleUpdate {
            value: cb(self.value),
            state: self.state,
        }
    }

    /// Create an update to insert this value.
    pub fn insert(value: T) -> Self {
        Self { state: true, value }
    }

    /// Create an update to remove this value.
    pub fn remove(value: T) -> Self {
        Self {
            state: false,
            value,
        }
    }
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

/// A monotonically increasing identifier for input transaction results.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Deserialize, Serialize)]
pub struct SequenceId(pub u64);

/// A Saturn V-compatible value type.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
#[serde(rename_all = "lowercase")]
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

/// A trait for Rust types that can be compatible with particular Saturn V types.
pub trait CheckType {
    /// Checks if this type is compatible with a Saturn V type.
    fn check_ty(ty: &StructuredType) -> ServerResult<()>;

    /// Checks if an instance of this type is compatible with a Saturn V type.
    fn check_value(&self, ty: &StructuredType) -> ServerResult<()>;
}

impl<T: Clone + Into<StructuredValue>> CheckType for T {
    fn check_ty(_ty: &StructuredType) -> ServerResult<()> {
        Ok(())
    }

    fn check_value(&self, ty: &StructuredType) -> ServerResult<()> {
        let val: StructuredValue = self.clone().into();

        if ty == &val.ty() {
            Ok(())
        } else {
            Err(ServerError::TypeMismatch {
                expected: ty.clone(),
                got: val.ty(),
            })
        }
    }
}

/// A trait for Rust types that have corresponding Saturn V types.
pub trait Typed: CheckType {
    /// Retrieves the concrete, singular Saturn V type for this type.
    fn ty() -> StructuredType;
}

/// Converts a Rust type into a Saturn V type.
pub trait IntoValue: CheckType {
    /// Converts this Rust value to a [Value].
    fn into_value(self) -> StructuredValue;
}

impl<T: CheckType + Into<StructuredValue>> IntoValue for T {
    fn into_value(self) -> StructuredValue {
        self.into()
    }
}

/// Converts a Saturn V type into a Rust type.
pub trait FromValue: CheckType {
    /// Converts to this Rust value from a [Value].
    fn from_value(val: StructuredValue) -> Self;
}

impl<T: CheckType + From<StructuredValue>> FromValue for T {
    fn from_value(val: StructuredValue) -> Self {
        Self::from(val)
    }
}

macro_rules! impl_typed_primitive {
    ($ty:ty, $name:ident) => {
        impl Typed for $ty {
            fn ty() -> StructuredType {
                StructuredType::Primitive(ir::Type::$name)
            }
        }

        impl From<$ty> for StructuredValue {
            fn from(val: $ty) -> StructuredValue {
                StructuredValue::$name(val.into())
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

        impl<$($el: CheckType),+> CheckType for ($($el),+) {
            fn check_ty(ty: &StructuredType) -> ServerResult<()> {
                let els = match ty {
                    StructuredType::Tuple(els) => els,
                    _ => unreachable!(),
                };

                let mut els = els.into_iter();
                $($el::check_ty(els.next().unwrap())?;)*
                Ok(())
            }

            #[allow(non_snake_case)]
            fn check_value(&self, ty: &StructuredType) -> ServerResult<()> {
                let els = match ty {
                    StructuredType::Tuple(els) => els,
                    _ => unreachable!(),
                };

                let mut els = els.into_iter();
                let ($($el),+) = self;
                $($el.check_value(els.next().unwrap())?;)*
                Ok(())
            }
        }

        impl<$($el: IntoValue),+> IntoValue for ($($el),+) {
            #[allow(non_snake_case)]
            fn into_value(self) -> StructuredValue {
                let ($($el),+) = self;
                StructuredValue::Tuple(vec![$($el.into_value()),+])
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

macro_rules! serde_js {
    ($ty:ty) => {
        impl From<JsValue> for $ty {
            fn from(value: JsValue) -> Self {
                serde_wasm_bindgen::from_value(value).unwrap()
            }
        }

        impl From<$ty> for JsValue {
            fn from(value: $ty) -> JsValue {
                serde_wasm_bindgen::to_value(&value).unwrap()
            }
        }
    };
}

serde_js!(ServerError);
serde_js!(RelationInfo);
serde_js!(StructuredValue);

impl<T: FromValue> From<JsValue> for TupleUpdate<T> {
    fn from(value: JsValue) -> Self {
        serde_wasm_bindgen::from_value::<TupleUpdate>(value)
            .unwrap()
            .map(T::from_value)
    }
}

impl<T: IntoValue> From<TupleUpdate<T>> for JsValue {
    fn from(value: TupleUpdate<T>) -> Self {
        serde_wasm_bindgen::to_value(&value.map(T::into_value)).unwrap()
    }
}
