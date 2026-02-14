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

use std::{fmt::Debug, future::Future, marker::PhantomData, ops::Deref, sync::Arc};

use futures_util::{SinkExt, Stream, StreamExt};
use parking_lot::Mutex;
use saturn_v_protocol::*;
use slab::Slab;
use thiserror::Error;
use tracing::{error, trace};
use wasm_bindgen::prelude::*;

pub use ir::StructuredType;
pub use saturn_v_protocol::{
    FromValue, IntoValue, ServerError, StructuredValue, Symbol, TupleUpdate,
};

/// A client to a Saturn V server.
#[derive(Clone, Debug)]
#[wasm_bindgen]
pub struct Client {
    rpc: JsonRpcClient,
}

#[wasm_bindgen]
impl Client {
    /// Creates a client to the Saturn V server at the given RPC URL.
    #[cfg(target_arch = "wasm32")]
    #[wasm_bindgen(constructor)]
    pub fn new(url: &str) -> std::result::Result<Self, JsError> {
        use gloo_net::websocket::*;

        // open initial WebSocket connection
        let ws = futures::WebSocket::open(&url)?;

        // split WebSocket into write and read halves
        let (mut source, mut sink) = ws.split();

        // adapt WS source to Flume channel
        let (source_tx, source_rx) = flume::unbounded();
        wasm_bindgen_futures::spawn_local(async move {
            while let Ok(msg) = source_rx.recv_async().await {
                if source.send(Message::Bytes(msg)).await.is_err() {
                    return;
                }
            }
        });

        // adapt WS sink to Flume channel
        let (sink_tx, sink_rx) = flume::unbounded();
        wasm_bindgen_futures::spawn_local(async move {
            while let Some(msg) = sink.next().await {
                let msg = match msg {
                    Ok(Message::Text(json)) => json.into_bytes(),
                    Ok(Message::Bytes(json)) => json,
                    Err(err) => {
                        error!("WebSocket error: {err:?}");
                        continue;
                    }
                };

                if sink_tx.send(msg).is_err() {
                    return;
                }
            }
        });

        // construct JSON-RPC client
        let rpc = JsonRpcClient::new(source_tx, sink_rx);

        Ok(Self { rpc })
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
    /// Creates a client to the Saturn V server at the given RPC URL.
    #[cfg(not(target_arch = "wasm32"))]
    pub async fn new(url: &str) -> Result<Self> {
        use tokio_tungstenite::tungstenite::{Bytes, Message};

        // connect to WebSocket
        let (ws, _response) = tokio_tungstenite::connect_async(url).await?;

        // split WebSocket into write and read halves
        let (mut source, mut sink) = ws.split();

        // adapt WS source to Flume channel
        let (source_tx, source_rx) = flume::unbounded::<Vec<u8>>();
        tokio::spawn(async move {
            while let Ok(msg) = source_rx.recv_async().await {
                if let Err(err) = source.send(Message::Binary(msg.into())).await {
                    error!("WebSocket TX error: {err:?}");
                    return;
                }
            }
        });

        // adapt WS sink to Flume channel
        let (sink_tx, sink_rx) = flume::unbounded();
        tokio::spawn(async move {
            while let Some(msg) = sink.next().await {
                let msg = match msg {
                    Ok(Message::Text(json)) => Bytes::from(json).to_vec(),
                    Ok(Message::Binary(json)) => json.to_vec(),
                    Ok(msg) => {
                        trace!("received server message: {msg:?}");
                        continue; // tungstenite handles everything else
                    }
                    Err(err) => {
                        error!("WebSocket RX error: {err:?}");
                        continue;
                    }
                };

                if sink_tx.send(msg).is_err() {
                    return; // RPC was dropped; silently abort
                }
            }
        });

        // construct JSON-RPC client
        let rpc = JsonRpcClient::new(source_tx, sink_rx);

        Ok(Self { rpc })
    }

    /// Creates a client to a Saturn V server with a raw transport.
    pub fn from_transport(tx: flume::Sender<Vec<u8>>, rx: flume::Receiver<Vec<u8>>) -> Self {
        Self {
            rpc: JsonRpcClient::new(tx, rx),
        }
    }

    /// Gets the program currently loaded.
    pub async fn get_program(&self) -> Result<Program> {
        Ok(self.rpc.on_request(GetProgram {}).await?.response)
    }

    /// Replaces the program currently loaded with a new program.
    pub async fn set_program(&self, program: &Program) -> Result<()> {
        self.rpc
            .on_request(SetProgram {
                program: program.to_owned(),
            })
            .await
            .map(|tx| tx.response)
            .map_err(Into::into)
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
            .map(JsValue::from)
            .map(Ok);

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
            .map(JsValue::from)
            .map(Ok);

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
    ) -> Result<impl Stream<Item = TupleUpdate<T>> + Unpin + 'static>;
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
            .into_iter()
            .map(|val| T::from_value(val))
            .collect())
    }

    /// Subscribes to live updates on values in this output.
    async fn subscribe<T: FromValue + Send + 'static>(
        &self,
    ) -> Result<impl Stream<Item = TupleUpdate<T>> + 'static> {
        T::check_ty(&self.ty)?;

        let request = WatchRelation {
            id: self.id.clone(),
        };

        let stream = self
            .client()
            .rpc
            .to_owned()
            .on_subscribe(request)
            .await?
            .map(move |update| update.map(T::from_value))
            .boxed();

        Ok(stream)
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
    #[cfg(not(target_arch = "wasm32"))]
    #[error(transparent)]
    WebSocket(#[from] tokio_tungstenite::tungstenite::Error),
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
#[derive(Clone, Debug)]
pub struct JsonRpcClient(Arc<JsonRpcClientInner>);

impl Deref for JsonRpcClient {
    type Target = JsonRpcClientInner;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// The inner JSON-RPC state machine.
#[derive(Debug)]
pub struct JsonRpcClientInner {
    /// A table matching request IDs to senders to their recipients.
    requests: Mutex<Slab<flume::Sender<serde_json::Value>>>,

    /// A table matching subscription IDs to senders to their recipients.
    subscriptions: Mutex<Slab<flume::Sender<serde_json::Value>>>,

    /// A sender of serialized JSON values to the outgoing transport.
    tx: flume::Sender<Vec<u8>>,
}

impl Rpc for JsonRpcClient {}

impl<T: Subscription + 'static> HandleSubscribe<T> for JsonRpcClient {
    async fn on_subscribe(
        &self,
        request: T,
    ) -> ServerResult<impl Stream<Item = T::Response> + Unpin + Send + 'static> {
        // create event handler channel and insert into table
        let (req_tx, req_rx) = flume::unbounded();
        let subscription_id = self.subscriptions.lock().insert(req_tx);

        // send initial subscription request
        let () = self
            .on_request(Subscribe {
                param: request,
                id: subscription_id,
            })
            .await
            .inspect_err(|_| {
                // clean up subscription ID if request failed
                self.subscriptions.lock().remove(subscription_id);
            })?;

        // convert channel into stream of responses
        let stream = req_rx.into_stream().filter_map(|value| async move {
            match serde_json::from_value::<T::Response>(value) {
                Ok(ev) => Some(ev),
                Err(err) => {
                    error!("failed to deserialize subscription event: {err:?}");
                    None
                }
            }
        });

        // wrap stream in automatic unsubscriber
        Ok(SubscribeStream {
            inner: Box::pin(stream),
            id: subscription_id,
            rpc: self.clone(),
            _request: PhantomData::<T>,
        })
    }
}

/// A stream that automatically unsubscribes from the server when dropped.
pub struct SubscribeStream<S, T: Subscription> {
    inner: S,
    id: usize,
    rpc: JsonRpcClient,
    _request: PhantomData<T>,
}

impl<S, T: Subscription> Drop for SubscribeStream<S, T> {
    fn drop(&mut self) {
        // Wasm-specific: unsubscribe from stream
        #[cfg(target_arch = "wasm32")]
        wasm_bindgen_futures::spawn_local(self.unsubscribe());

        // non-Wasm: spawn event pump for incoming messages
        #[cfg(not(target_arch = "wasm32"))]
        tokio::spawn(self.unsubscribe());
    }
}

impl<S: Unpin, T: Subscription> Unpin for SubscribeStream<S, T> {}

impl<S: Stream + Unpin, T: Subscription> Stream for SubscribeStream<S, T> {
    type Item = S::Item;

    fn poll_next(
        mut self: std::pin::Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Option<Self::Item>> {
        S::poll_next(std::pin::Pin::new(&mut self.inner), cx)
    }
}

impl<S, T: Subscription> SubscribeStream<S, T> {
    fn unsubscribe(&self) -> impl Future<Output = ()> + 'static {
        let rpc = self.rpc.clone();
        let id = self.id;
        async move {
            let _ = rpc
                .on_request(Unsubscribe::<T> {
                    id,
                    _phantom: PhantomData,
                })
                .await;

            rpc.subscriptions.lock().remove(id);
        }
    }
}

impl<T: Request> Handle<T> for JsonRpcClient {
    async fn on_request(&self, request: T) -> ServerResult<<T as Request>::Response> {
        // create request handler oneshot channel and insert into table
        let (req_tx, req_rx) = flume::bounded(1);
        let request_id = self.requests.lock().insert(req_tx);

        // create the JSON-RPC request body
        let request_json = serde_json::to_value(JsonRpcRequest {
            jsonrpc: "2.0".to_string(),
            method: T::name().to_string(),
            id: serde_json::Value::from(request_id),
            param: request,
        })
        .unwrap();

        // log request
        trace!("request: {request_json:?}");

        // send the request to the transport
        let request = serde_json::to_vec(&request_json).unwrap();
        self.tx
            .send_async(request)
            .await
            .map_err(|_| ServerError::Disconnected)?;

        // wait for response
        let response = req_rx
            .into_recv_async()
            .await
            .map_err(|_| ServerError::Disconnected)?;

        // TODO: handle deserialization without unwrapping?
        serde_json::from_value(response).unwrap()
    }
}

impl JsonRpcClient {
    /// Creates a JSON-RPC client over the given duplex message channel.
    pub fn new(tx: flume::Sender<Vec<u8>>, rx: flume::Receiver<Vec<u8>>) -> Self {
        // create shared client handle
        let client = Self(Arc::new(JsonRpcClientInner {
            requests: Default::default(),
            subscriptions: Default::default(),
            tx,
        }));

        // Wasm-specific: spawn event pump for incoming messages
        #[cfg(target_arch = "wasm32")]
        wasm_bindgen_futures::spawn_local(client.handle_all(rx));

        // non-Wasm: spawn event pump for incoming messages
        #[cfg(not(target_arch = "wasm32"))]
        tokio::spawn(client.handle_all(rx));

        // return remaining client handle
        client
    }

    /// Handles all incoming messages.
    fn handle_all(&self, rx: flume::Receiver<Vec<u8>>) -> impl Future<Output = ()> + 'static {
        let client = self.clone();
        async move {
            while let Ok(json) = rx.recv_async().await {
                client.handle_incoming(json);
            }
        }
    }

    /// Handle a single incoming message.
    fn handle_incoming(&self, message: Vec<u8>) {
        use serde_json::*;

        // deserialize the incoming JSON object
        let value: Map<String, Value> = match serde_json::from_slice(&message) {
            Ok(value) => value,
            Err(err) => {
                error!("failed to deserialize incoming JSON object: {err:?}");
                return;
            }
        };

        // log incoming message
        trace!("received: {value:?}");

        // confirm that the incoming value is marked as JSON-RPC
        if value.get("jsonrpc") != Some(&Value::String("2.0".to_string())) {
            error!("incoming JSON object was not marked as jsonrpc = 2.0");
            return;
        }

        // if the incoming value has a "method" field, it is a subscription notification
        if value.get("method").is_some() {
            // the type of untyped subscription notification requests
            type Event = JsonRpcRequest<SubscriptionEvent<Value>>;

            // deserialize the request
            // ignore the method name since the notif will have the ID
            // TODO: handle incoming requests with IDs somehow
            let request = match serde_json::from_value::<Event>(value.into()) {
                Ok(request) => request,
                Err(err) => {
                    error!("failed to deserialize request: {err:?}");
                    return;
                }
            };

            // send subscription event to corresponding subscription ID
            // if the channel is missing or closed, assume we've unsubscribed
            self.subscriptions
                .lock()
                .get(request.param.id)
                .map(|tx| tx.send(request.param.event));
        } else if value.get("error").is_some() {
            // if there is an error field, this is a failure response
            let response: JsonRpcFailure = match serde_json::from_value(value.into()) {
                Ok(request) => request,
                Err(err) => {
                    error!("failed to deserialize failure response: {err:?}");
                    return;
                }
            };

            // convert RPC error to ServerResult
            let result: ServerResult<()> = Err(ServerError::JsonRpcError {
                code: response.error.code,
                message: response.error.message,
            });

            // forward result to handler
            self.on_response(response.id, serde_json::to_value(result).unwrap());
        } else {
            // otherwise, it's a response
            let response: JsonRpcSuccess<Value> = match serde_json::from_value(value.into()) {
                Ok(request) => request,
                Err(err) => {
                    error!("failed to deserialize success response: {err:?}");
                    return;
                }
            };

            // forward result to handler
            self.on_response(response.id, response.result);
        }
    }

    /// Delivers a response to a request handle by ID.
    fn on_response(&self, id: serde_json::Value, result: serde_json::Value) {
        // extract request ID
        let Some(request_id) = id.as_u64() else {
            error!("expected request ID to be int, got {id:?}");
            return;
        };

        // retrieve pending request sender
        let mut requests = self.requests.lock();
        let Some(response_tx) = requests.try_remove(request_id as usize) else {
            error!("unknown request ID {request_id}");
            return;
        };

        // send response
        let _ = response_tx.send(result);
    }
}
