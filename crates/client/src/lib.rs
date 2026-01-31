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

//! Client library to the Saturn V server.

#![warn(missing_docs)]

use std::{fmt::Debug, future::Future, ops::Deref};

use futures_util::{Stream, StreamExt, TryStreamExt};
use parking_lot::Mutex;
use reqwest::{Method, RequestBuilder, Url};
use reqwest_eventsource::{Event, RequestBuilderExt};
use saturn_v_protocol::*;
use serde::{Deserialize, Serialize};
use slab::Slab;
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
    pub fn js_new(base: String) -> std::result::Result<Self, String> {
        Url::parse(&base)
            .map(Self::new)
            .map_err(|err| err.to_string())
    }

    /// Gets a list of all inputs currently on the server.
    #[wasm_bindgen(js_name = "getInputs")]
    pub async fn get_inputs(&self) -> Result<Vec<Input>> {
        Ok(self
            .get_json::<Vec<RelationInfo>>("inputs/list")
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
            .get_json::<Vec<RelationInfo>>("outputs/list")
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
    pub async fn insert<T: IntoValue>(&self, val: T) -> Result<()> {
        self.update(val, true).await
    }

    /// Removes a typed value from this relation.
    pub async fn remove<T: IntoValue>(&self, val: T) -> Result<()> {
        self.update(val, false).await
    }

    /// Updates a typed value in this relation. `true` adds, `false` removes.
    pub async fn update<T: IntoValue>(&self, val: T, state: bool) -> Result<()> {
        val.check_value(&self.ty)?;

        let value = val.into_value();
        let body = vec![TupleUpdate { state, value }];

        self.client
            .post_json(&format!("input/{}/update", self.id), &body)
            .await?;

        Ok(())
    }
}

impl ImplQueryRelation for Input {
    const ENDPOINT: &'static str = "input";

    fn client(&self) -> &Client {
        &self.client
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
        self.update(value, state).await
    }

    /// Gets the set of values currently in this input.
    #[wasm_bindgen(js_name = get_all)]
    pub async fn js_get_all(&self) -> Result<Vec<JsValue>> {
        self.get_all::<StructuredValue>()
            .await
            .map(|values| values.into_iter().map(|val| val.into()).collect())
    }

    /// Subscribes to live updates on values in this input.
    #[wasm_bindgen(js_name = subscribe)]
    pub async fn js_subscribe(&self) -> Result<wasm_streams::readable::sys::ReadableStream> {
        let stream = self
            .subscribe::<JsValue>()
            .await?
            .map_ok(JsValue::from)
            .map_err(JsValue::from);

        Ok(wasm_streams::ReadableStream::from_stream(stream).into_raw())
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

impl ImplQueryRelation for Output {
    const ENDPOINT: &'static str = "output";

    fn client(&self) -> &Client {
        &self.client
    }
}

#[wasm_bindgen]
impl Output {
    /// Gets the set of values currently in this output.
    #[wasm_bindgen(js_name = get_all)]
    pub async fn js_get_all(&self) -> Result<Vec<JsValue>> {
        self.get_all::<StructuredValue>()
            .await
            .map(|values| values.into_iter().map(|val| val.into()).collect())
    }

    /// Subscribes to live updates on values in this output.
    #[wasm_bindgen(js_name = subscribe)]
    pub async fn js_subscribe(&self) -> Result<wasm_streams::readable::sys::ReadableStream> {
        let stream = self
            .subscribe::<JsValue>()
            .await?
            .map_ok(JsValue::from)
            .map_err(JsValue::from);

        Ok(wasm_streams::ReadableStream::from_stream(stream).into_raw())
    }
}

/// A trait for relations whose contents can be directly queried.
pub trait QueryRelation {
    /// Get the set of values currently in this relation.
    #[cfg(target_arch = "wasm32")]
    fn get_all<T: FromValue>(&self) -> impl Future<Output = Result<Vec<T>>>;

    /// Get the set of values currently in this relation.
    #[cfg(not(target_arch = "wasm32"))]
    fn get_all<T: FromValue>(&self) -> impl Future<Output = Result<Vec<T>>> + Send;

    /// Subscribes to live updates on values in this output.
    #[allow(async_fn_in_trait)]
    async fn subscribe<T: FromValue + 'static>(
        &self,
    ) -> Result<impl Stream<Item = Result<TupleUpdate<T>>> + 'static>;
}

/// A utility trait to implement [QueryRelation].
trait ImplQueryRelation: Deref<Target = RelationInfo> + Send + Sync {
    /// The HTTP path of this relation's operations.
    const ENDPOINT: &'static str;

    /// Gets the client on this relation.
    fn client(&self) -> &Client;
}

impl<R: ImplQueryRelation> QueryRelation for R {
    /// Gets the set of values currently in this output.
    async fn get_all<T: FromValue>(&self) -> Result<Vec<T>> {
        T::check_ty(&self.ty)?;

        Ok(self
            .client()
            .get_json::<Vec<StructuredValue>>(&format!("{}/{}", R::ENDPOINT, self.id))
            .await?
            .into_iter()
            .map(|val| T::from_value(val))
            .collect())
    }

    /// Subscribes to live updates on values in this output.
    async fn subscribe<T: FromValue + 'static>(
        &self,
    ) -> Result<impl Stream<Item = Result<TupleUpdate<T>>> + 'static> {
        T::check_ty(&self.ty)?;

        let path = format!("{}/{}/subscribe", R::ENDPOINT, self.id);

        // send request for subscription
        let mut src = self
            .client()
            .begin_request(Method::GET, &path)
            .eventsource()
            .map_err(|_| Error::CannotCloneRequest)?;

        // wait for ready event
        // avoids client-side race conditions
        match src.next().await {
            Some(Ok(Event::Open)) => {}
            _ => todo!(),
        }

        // transform incoming events into tuple updates
        Ok(src.filter_map(|ev| {
            std::future::ready(match ev {
                Ok(Event::Open) => None,
                Err(err) => Some(Err(Error::EventSource(Box::new(err)))),
                Ok(Event::Message(msg)) => Some(
                    match serde_json::from_reader::<_, ServerResult<TupleUpdate>>(
                        msg.data.as_bytes(),
                    ) {
                        Ok(Ok(update)) => Ok(update.map(T::from_value)),
                        Ok(Err(err)) => Err(Error::Server(err)),
                        Err(err) => Err(Error::Parse(err)),
                    },
                ),
            })
        }))
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
    #[error("cannot clone request")]
    CannotCloneRequest,
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
        match err {
            Error::Server(server) => JsValue::from(server),
            other => JsValue::from_str(&format!("{other:#?}")),
        }
    }
}

/// A JSON-RPC client.
pub struct JsonRpcClient {
    /// A table matching request IDs to senders to their recipients.
    requests: Mutex<Slab<flume::Sender<serde_json::Value>>>,

    /// A table matching subscription IDs to senders to their recipients.
    subscriptions: Mutex<Slab<flume::Sender<serde_json::Value>>>,

    /// A sender of serialized JSON values to the outgoing transport.
    tx: flume::Sender<String>,
}

impl Rpc for JsonRpcClient {}

impl<T: Subscription> HandleSubscribe<T> for JsonRpcClient {
    async fn on_subscribe(
        &self,
        request: T,
        mut on_update: impl FnMut(T::Response) + Send,
    ) -> ServerResult<()> {
        // create event handler channel and insert into table
        let (req_tx, req_rx) = flume::unbounded();
        let subscription_id = self.subscriptions.lock().insert(req_tx);

        // send initial subscription request
        self.on_request(Subscribe {
            params: request,
            id: subscription_id,
        })
        .await
        .inspect_err(|_| {
            // clean up subscription ID if request failed
            self.subscriptions.lock().remove(subscription_id);
        })?;

        // stream subscription events into callback
        while let Ok(value) = req_rx.recv_async().await {
            // deserialize object
            // TODO: log error if parse fails
            if let Ok(ev) = serde_json::from_value(value) {
                on_update(ev);
            }
        }

        // remove subscription sender
        self.subscriptions.lock().remove(subscription_id);

        // return result of unsubscription request
        self.on_request(Unsubscribe {
            id: subscription_id,
            _phantom: std::marker::PhantomData::<T>,
        })
        .await
    }
}

impl<T: Request> Handle<T> for JsonRpcClient {
    async fn on_request(&self, request: T) -> ServerResult<<T as Request>::Response> {
        // create request handler oneshot channel and insert into table
        let (req_tx, req_rx) = flume::bounded(1);
        let request_id = self.requests.lock().insert(req_tx);

        // create the JSON-RPC request body
        let request_json = serde_json::json!({
            "jsonrpc": "2.0",
            "method": T::name(),
            "id": request_id,
            "param": request,
        });

        // send the request to the transport
        let request = serde_json::to_string(&request_json).unwrap();

        // TODO: handle channel send error without unwrapping?
        self.tx.send_async(request).await.unwrap();

        // TODO: handle channel cancellation without unwrapping?
        let response = req_rx.into_recv_async().await.unwrap();

        // TODO: handle deserialization without unwrapping?
        serde_json::from_value(response).unwrap()
    }
}
