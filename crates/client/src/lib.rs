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

use std::{fmt::Debug, future::Future, ops::Deref, str::FromStr, sync::Arc};

use futures_util::{Stream, TryStreamExt};
use parking_lot::Mutex;
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
    rpc: Arc<JsonRpcClient>,
}

#[wasm_bindgen]
impl Client {
    /// Creates a client to the Saturn V server at the given base URL.
    #[wasm_bindgen(constructor)]
    pub fn js_new(base: String) -> std::result::Result<Self, String> {
        todo!()
    }

    /// Gets a list of all inputs currently on the server.
    #[wasm_bindgen(js_name = "getInputs")]
    pub async fn get_inputs(&self) -> Result<Vec<Input>> {
        Ok(self
            .rpc
            .on_request(ListRelations {})
            .await?
            .response
            .into_iter()
            .filter(|info| info.is_input)
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
            .ok_or_else(|| ServerError::NoSuchRelation(name.to_string()))
            .map_err(Into::into)
    }

    /// Gets a list of all outputs currently on the server.
    #[wasm_bindgen(js_name = "getOutputs")]
    pub async fn get_outputs(&self) -> Result<Vec<Output>> {
        Ok(self
            .rpc
            .on_request(ListRelations {})
            .await?
            .response
            .into_iter()
            .filter(|info| !info.is_input)
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
            .ok_or_else(|| ServerError::NoSuchRelation(name.to_string()))
            .map_err(Into::into)
    }
}

impl Client {
    /// Creates a client to the Saturn V server at the given base URL.
    pub fn new(base: url::Url) -> Self {
        todo!()
    }

    /// Gets the program currently loaded.
    pub async fn get_program(&self) -> Result<Program> {
        Ok(self.rpc.on_request(GetProgram {}).await?.response)
    }

    /// Replaces the program currently loaded with a new program.
    pub async fn set_program(&self, program: &Program) -> Result<()> {
        Ok(self
            .rpc
            .on_request(SetProgram {
                program: program.to_owned(),
            })
            .await?
            .response)
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
                is_input: false,
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
                is_input: true,
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
        let updates = vec![TupleUpdate { state, value }];

        self.client
            .rpc
            .on_request(UpdateInput {
                id: self.id.clone(),
                updates,
            })
            .await?;

        Ok(())
    }
}

impl ImplQueryRelation for Input {
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
            .subscribe::<StructuredValue>()
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
            .subscribe::<StructuredValue>()
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
    async fn subscribe<T: FromValue + Send + 'static>(
        &self,
    ) -> Result<impl Stream<Item = Result<TupleUpdate<T>>> + 'static>;
}

/// A utility trait to implement [QueryRelation].
trait ImplQueryRelation: Deref<Target = RelationInfo> + Send + Sync {
    /// Gets the client on this relation.
    fn client(&self) -> &Client;
}

impl<R: ImplQueryRelation> QueryRelation for R {
    /// Gets the set of values currently in this output.
    async fn get_all<T: FromValue>(&self) -> Result<Vec<T>> {
        T::check_ty(&self.ty)?;

        Ok(self
            .client()
            .rpc
            .on_request(GetTuples {
                id: self.id.clone(),
            })
            .await?
            .response
            .into_iter()
            .map(|val| T::from_value(val))
            .collect())
    }

    /// Subscribes to live updates on values in this output.
    async fn subscribe<T: FromValue + Send + 'static>(
        &self,
    ) -> Result<impl Stream<Item = Result<TupleUpdate<T>>> + 'static> {
        T::check_ty(&self.ty)?;

        let (tx, rx) = flume::unbounded::<Result<TupleUpdate<T>>>();

        let request = WatchRelation {
            id: self.id.clone(),
        };

        let on_update = {
            let tx = tx.clone();
            move |update: TupleUpdate| tx.send(Ok(update.map(T::from_value))).is_ok()
        };

        let rpc = self.client().rpc.to_owned();

        tokio::spawn(async move {
            if let Err(err) = rpc.on_subscribe(request, on_update).await {
                let _ = tx.send(Err(err.into())).is_err();
            }
        });

        Ok(rx.into_stream())
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
#[derive(Debug)]
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
        mut on_update: impl FnMut(T::Response) -> bool + Send,
    ) -> ServerResult<()> {
        // create event handler channel and insert into table
        let (req_tx, req_rx) = flume::unbounded();
        let subscription_id = self.subscriptions.lock().insert(req_tx);

        // send initial subscription request
        self.on_request(Subscribe {
            param: request,
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
                if !on_update(ev) {
                    break;
                }
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
        let request_json = JsonRpcRequest {
            jsonrpc: "2.0".to_string(),
            method: T::name().to_string(),
            id: serde_json::Value::from(request_id),
            param: request,
        };

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

impl JsonRpcClient {
    /// Creates a JSON-RPC client over the given duplex message channel.
    pub fn new(tx: flume::Sender<String>, rx: flume::Receiver<String>) -> Arc<Self> {
        // create shared client handle
        let client = Arc::new(Self {
            requests: Default::default(),
            subscriptions: Default::default(),
            tx,
        });

        // spawn event pump for incoming messages
        tokio::spawn({
            let client = client.clone();
            async move {
                while let Ok(json) = rx.recv_async().await {
                    client.handle_incoming(json);
                }
            }
        });

        // return remaining client handle
        client
    }

    /// Handle a single incoming message.
    fn handle_incoming(&self, message: String) {
        use serde_json::*;

        // deserialize the incoming JSON object
        let Ok(value) = Map::<String, Value>::from_str(&message) else {
            // TODO: log errors
            return;
        };

        // confirm that the incoming value is marked as JSON-RPC
        if value.get("jsonrpc") != Some(&Value::String("2.0".to_string())) {
            // TODO: log error
            return;
        }

        // if the incoming value has a "method" field, it is a subscription notification
        if value.get("method").is_some() {
            // the type of untyped subscription notification requests
            type Event = JsonRpcRequest<SubscriptionEvent<Value>>;

            // deserialize the request
            // ignore the method name since the notif will have the ID
            // TODO: handle incoming requests with IDs somehow
            let Ok(request) = serde_json::from_value::<Event>(value.into()) else {
                // TODO: log error
                return;
            };

            // send subscription event to corresponding subscription ID
            // if the channel is missing or closed, assume we've unsubscribed
            self.subscriptions
                .lock()
                .get(request.param.id)
                .map(|tx| tx.send(request.param.event));
        }
    }
}
