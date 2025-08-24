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

//! Client library to the Saturn V server.

#![warn(missing_docs)]

use std::{fmt::Debug, ops::Deref};

use futures_util::{Stream, StreamExt};
use ordered_float::OrderedFloat;
use reqwest::{Method, RequestBuilder, Url};
use reqwest_eventsource::{Event, RequestBuilderExt};
use saturn_v_ir::{self as ir};
use serde::{Deserialize, Serialize};

pub use ir::StructuredType;
use thiserror::Error;

/// Type alias for IR programs that can be loaded on the server.
pub type Program = saturn_v_ir::Program<String>;

/// A client to a Saturn V server.
#[derive(Clone, Debug)]
pub struct Client {
    server: Url,
    web: reqwest::Client,
}

impl Client {
    /// Creates a client to the Saturn V server at the given base URL.
    pub fn new(base: Url) -> Self {
        Self {
            server: base,
            web: reqwest::Client::new(),
        }
    }

    /// Gets the program currently loaded.
    pub async fn get_program(&self) -> Result<Program> {
        self.get_json("/program").await
    }

    /// Replaces the program currently loaded with a new program.
    pub async fn set_program(&self, program: &Program) -> Result<()> {
        self.post_json("/program", program).await
    }

    /// Gets a list of all inputs currently on the server.
    pub async fn get_inputs(&self) -> Result<Vec<Input>> {
        Ok(self
            .get_json::<Vec<RelationInfo>>("/inputs/list")
            .await?
            .into_iter()
            .map(|info| Input {
                client: self.clone(),
                info,
            })
            .collect())
    }

    /// Gets an input by name.
    pub async fn get_input(&self, name: &str) -> Result<Option<Input>> {
        Ok(self
            .get_inputs()
            .await?
            .into_iter()
            .find(|input| input.name == name))
    }

    /// Gets a list of all outputs currently on the server.
    pub async fn get_outputs(&self) -> Result<Vec<Output>> {
        Ok(self
            .get_json::<Vec<RelationInfo>>("/outputs/list")
            .await?
            .into_iter()
            .map(|info| Output {
                client: self.clone(),
                info,
            })
            .collect())
    }

    /// Gets an output by name.
    pub async fn get_output(&self, name: &str) -> Result<Option<Output>> {
        Ok(self
            .get_outputs()
            .await?
            .into_iter()
            .find(|output| output.name == name))
    }

    /// Builds a request to the server with specified method and path.
    ///
    /// Automatically adds client-wide headers such as authentication.
    pub(crate) fn begin_request(&self, method: Method, path: &str) -> RequestBuilder {
        let url = self.server.join(path).unwrap();
        self.web.request(method, url)
    }

    /// Makes a GET request and parses it to JSON.
    pub(crate) async fn get_json<T: for<'a> Deserialize<'a>>(&self, path: &str) -> Result<T> {
        let response: ServerResult<T> = self
            .begin_request(Method::GET, path)
            .send()
            .await?
            .json()
            .await?;

        Ok(response?)
    }

    /// POSTs a JSON payload.
    pub(crate) async fn post_json<T: Serialize>(&self, path: &str, json: &T) -> Result<()> {
        let response: ServerResult<()> = self
            .begin_request(Method::POST, path)
            .json(json)
            .send()
            .await?
            .json()
            .await?;

        Ok(response?)
    }
}

#[cfg(feature = "invalid-requests")]
impl Client {
    /// Creates an output by name, even if it doesn't necessarily exist.
    pub fn get_invalid_output(&self, name: &str, ty: StructuredType) -> Output {
        Output {
            client: self.clone(),
            info: RelationInfo {
                name: name.to_string(),
                id: name.to_string(),
                ty,
            },
        }
    }

    /// Creates an output by name, even if it doesn't necessarily exist.
    pub fn get_invalid_input(&self, id: &str, ty: StructuredType) -> Input {
        Input {
            client: self.clone(),
            info: RelationInfo {
                name: id.to_string(),
                id: id.to_string(),
                ty,
            },
        }
    }
}

/// A Saturn V server's input relation.
#[derive(Clone, Debug)]
pub struct Input {
    client: Client,
    info: RelationInfo,
}

impl Deref for Input {
    type Target = RelationInfo;

    fn deref(&self) -> &Self::Target {
        &self.info
    }
}

impl Input {
    /// Inserts a value into this relation.
    pub async fn insert<T: AsValue>(&self, val: &T) -> Result<()> {
        self.update(val, true).await
    }

    /// Removes a value from this relation.
    pub async fn remove<T: AsValue>(&self, val: &T) -> Result<()> {
        self.update(val, false).await
    }

    /// Updates a value in this relation. `true` adds, `false` removes.
    pub async fn update<T: AsValue>(&self, val: &T, state: bool) -> Result<()> {
        self.check_ty::<T>()?;

        let value = val.as_value();
        let body = vec![TupleUpdate { state, value }];

        self.client
            .post_json(&format!("/input/{}/update", self.id), &body)
            .await?;

        Ok(())
    }
}

/// A Saturn V server's output relation.
#[derive(Clone, Debug)]
pub struct Output {
    client: Client,
    info: RelationInfo,
}

impl Deref for Output {
    type Target = RelationInfo;

    fn deref(&self) -> &Self::Target {
        &self.info
    }
}

impl Output {
    /// Gets the set of values currently in this output.
    pub async fn get_all<T: FromValue>(&self) -> Result<Vec<T>> {
        self.check_ty::<T>()?;

        Ok(self
            .client
            .get_json::<Vec<Value>>(&format!("/output/{}", self.id))
            .await?
            .into_iter()
            .map(|val| T::from_value(val))
            .collect())
    }

    /// Subscribes to live updates on values in this output.
    pub fn subscribe<T: FromValue>(&self) -> Result<impl Stream<Item = Result<(T, bool)>>> {
        self.check_ty::<T>()?;

        let src = self
            .client
            .begin_request(Method::GET, &format!("/output/{}/subscribe", self.id))
            .eventsource()
            .unwrap();

        Ok(src.filter_map(|ev| {
            std::future::ready(match ev {
                Ok(Event::Open) => None,
                Err(err) => Some(Err(Error::EventSource(Box::new(err)))),
                Ok(Event::Message(msg)) => serde_json::from_reader(msg.data.as_bytes())
                    .map_err(Into::into)
                    .map(|update: TupleUpdate| Some((T::from_value(update.value), update.state)))
                    .transpose(),
            })
        }))
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

impl RelationInfo {
    /// Helper method to test if a type matches this relation.
    pub fn check_ty<T: Typed>(&self) -> Result<()> {
        if self.matches_ty::<T>() {
            Ok(())
        } else {
            Err(Error::Server(ServerError::TypeMismatch {
                expected: self.ty.clone(),
                got: T::ty(),
            }))
        }
    }

    /// Checks if a typed Saturn V value matches this relation's type.
    pub fn matches_ty<T: Typed>(&self) -> bool {
        T::ty() == self.ty
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
    fn as_value(&self) -> Value;
}

/// Converts a Saturn V type into a Rust type.
pub trait FromValue: Typed {
    /// Converts to this Rust value from a [Value].
    fn from_value(val: Value) -> Self;
}

/// An individual tuple update within a relation.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Deserialize, Serialize)]
pub struct TupleUpdate {
    /// The new state of the tuple. `true` for present, `false` for absent.
    pub state: bool,

    /// The tuple being updated.
    pub value: Value,
}

/// A Saturn V-compatible value type.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Deserialize, Serialize)]
pub enum Value {
    /// A nested list of other values.
    Tuple(Vec<Value>),

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

impl Value {
    /// Returns the type of this value.
    pub fn ty(&self) -> StructuredType {
        use StructuredType::*;
        use ir::Type::*;
        match self {
            Value::Tuple(els) => Tuple(els.iter().map(|val| val.ty()).collect()),
            Value::String(_) => Primitive(String),
            Value::Boolean(_) => Primitive(Boolean),
            Value::Integer(_) => Primitive(Integer),
            Value::Real(_) => Primitive(Real),
            Value::Symbol(_) => Primitive(Symbol),
        }
    }
}

macro_rules! impl_typed_primitive {
    ($ty:ty, $name:ident) => {
        impl Typed for $ty {
            fn ty() -> StructuredType {
                StructuredType::Primitive(ir::Type::$name)
            }
        }

        impl AsValue for $ty {
            fn as_value(&self) -> Value {
                Value::$name(self.clone().into())
            }
        }

        impl FromValue for $ty {
            fn from_value(val: Value) -> Self {
                match val {
                    Value::$name(inner) => inner.into(),
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
            fn as_value(&self) -> Value {
                let ($($el),+) = self;
                Value::Tuple(vec![$($el.as_value()),+])
            }
        }

        impl<$($el: FromValue),+> FromValue for ($($el),+) {
            #[allow(non_snake_case)]
            fn from_value(val: Value) -> Self {
                let els = match val {
                    Value::Tuple(els) => els,
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

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Error, Debug)]
pub enum Error {
    #[error(transparent)]
    Server(#[from] ServerError),
    #[error(transparent)]
    Request(#[from] reqwest::Error),
    #[error(transparent)]
    EventSource(#[from] Box<reqwest_eventsource::Error>),
    #[error(transparent)]
    Parse(#[from] serde_json::Error),
}

impl Error {
    /// Attempts to convert this error into a server error.
    pub fn into_server_error(self) -> Result<ServerError> {
        match self {
            Error::Server(err) => Ok(err),
            other => Err(other),
        }
    }
}

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

    #[error("the server side event stream has lagged")]
    Lagged,
}
