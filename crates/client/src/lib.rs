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
use reqwest::{Method, RequestBuilder, Url};
use reqwest_eventsource::{Event, RequestBuilderExt};
use saturn_v_protocol::*;
use serde::{Deserialize, Serialize};
use wasm_bindgen::prelude::*;

pub use ir::StructuredType;
use thiserror::Error;

/// A client to a Saturn V server.
#[derive(Clone, Debug)]
#[wasm_bindgen]
pub struct Client {
    server: Url,
    web: reqwest::Client,
}

#[wasm_bindgen]
impl Client {
    /// Creates a client to the Saturn V server at the given base URL.
    #[wasm_bindgen(constructor)]
    pub fn js_new(base: String) -> Self {
        Self::new(Url::parse(&base).unwrap())
    }

    /// Gets a list of all inputs currently on the server.
    #[wasm_bindgen(js_name = "getInputs")]
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
    #[wasm_bindgen(js_name = "getInput")]
    pub async fn get_input(&self, name: &str) -> Result<Input> {
        self.get_inputs()
            .await?
            .into_iter()
            .find(|input| input.name == name)
            .ok_or_else(|| ServerError::NoSuchInput(name.to_string()))
            .map_err(Into::into)
    }

    /// Gets a list of all outputs currently on the server.
    #[wasm_bindgen(js_name = "getOutputs")]
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
    #[wasm_bindgen(js_name = "getOutput")]
    pub async fn get_output(&self, name: &str) -> Result<Output> {
        self.get_outputs()
            .await?
            .into_iter()
            .find(|output| output.name == name)
            .ok_or_else(|| ServerError::NoSuchOutput(name.to_string()))
            .map_err(Into::into)
    }
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
#[wasm_bindgen]
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
    /// Inserts a typed value into this relation.
    pub async fn insert<T: AsValue>(&self, val: &T) -> Result<()> {
        self.update(val, true).await
    }

    /// Removes a typed value from this relation.
    pub async fn remove<T: AsValue>(&self, val: &T) -> Result<()> {
        self.update(val, false).await
    }

    /// Updates a typed value in this relation. `true` adds, `false` removes.
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

#[wasm_bindgen]
impl Input {
    /// Inserts a value into this relation.
    #[wasm_bindgen(js_name = "insert")]
    pub async fn js_insert(&self, val: JsValue) -> Result<()> {
        self.js_update(val, true).await
    }

    /// Removes a value from this relation.
    #[wasm_bindgen(js_name = "remove")]
    pub async fn js_remove(&self, val: JsValue) -> Result<()> {
        self.js_update(val, false).await
    }

    /// Updates a value in this relation. `true` adds, `false` removes.
    #[wasm_bindgen(js_name = "update")]
    pub async fn js_update(&self, value: JsValue, state: bool) -> Result<()> {
        // TODO: type-check

        let value = serde_wasm_bindgen::from_value(value).unwrap();
        let body = vec![TupleUpdate { state, value }];

        self.client
            .post_json(&format!("/input/{}/update", self.id), &body)
            .await?;

        Ok(())
    }
}

/// A Saturn V server's output relation.
#[derive(Clone, Debug)]
#[wasm_bindgen]
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
            .get_json::<Vec<StructuredValue>>(&format!("/output/{}", self.id))
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
                Ok(Event::Message(msg)) => Some(
                    match serde_json::from_reader::<_, ServerResult<TupleUpdate>>(
                        msg.data.as_bytes(),
                    ) {
                        Ok(Ok(update)) => Ok((T::from_value(update.value), update.state)),
                        Ok(Err(err)) => Err(Error::Server(err)),
                        Err(err) => Err(Error::Parse(err)),
                    },
                ),
            })
        }))
    }
}

#[wasm_bindgen]
impl Output {
    /// Gets the set of values currently in this output.
    #[wasm_bindgen(js_name = get_all)]
    pub async fn get_all_raw(&self) -> Result<Vec<JsValue>> {
        todo!()
    }
}

/// A type alias for client results with only [Error] as the error.
pub type Result<T> = std::result::Result<T, Error>;

/// An error that has occurred through misuse of the API ([ServerError]) or through some
/// unexpected client-side error.
#[derive(Error, Debug)]
#[allow(missing_docs)]
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

impl From<Error> for JsValue {
    fn from(err: Error) -> Self {
        let server = err.into_server_error().unwrap();
        serde_wasm_bindgen::to_value(&server).unwrap()
    }
}
