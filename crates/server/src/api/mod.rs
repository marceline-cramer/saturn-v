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

use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    convert::Infallible,
    future::Future,
    ops::{Deref, DerefMut},
    sync::Arc,
};

use anyhow::Context;
use axum::{
    body::Bytes,
    extract::{ws::Message, WebSocketUpgrade},
    response::{sse::Event, Sse},
    routing::get,
    Json, Router,
};
use futures_util::{stream::BoxStream, SinkExt, Stream, StreamExt, TryStreamExt};
use saturn_v_eval::{
    solve::Solver,
    types::{Fact, Relation},
    utils::{Key, Update},
    DataflowInputs, InputEvent, InputEventKind,
};
use saturn_v_protocol::{ir::RelationIO, *};
use tokio::sync::{broadcast, Mutex};
use tokio_stream::wrappers::BroadcastStream;
use tracing::{error, trace};

use crate::db::*;

pub use axum;

#[cfg(test)]
pub mod tests;

pub fn route(server: Server) -> Router {
    Router::new()
        .route("/ws", get(websocket))
        .with_state(server)
}

async fn websocket(server: ExtractState, ws: WebSocketUpgrade) -> axum::response::Response {
    ws.on_upgrade(move |socket| async move {
        let rpc = server.0.connect();
        let (mut tx, mut rx) = socket.split();

        let (incoming_tx, incoming_rx) = flume::unbounded();
        tokio::spawn(async move {
            while let Some(msg) = rx.next().await {
                let msg = match msg {
                    Ok(Message::Text(json)) => Bytes::from(json).to_vec(),
                    Ok(Message::Binary(json)) => json.to_vec(),
                    Ok(_) => continue, // axum handles everything else
                    Err(err) => {
                        error!("WebSocket RX error: {err:?}");
                        return;
                    }
                };

                if incoming_tx.send(msg).is_err() {
                    return;
                }
            }
        });

        let (outgoing_tx, outgoing_rx) = flume::unbounded::<Vec<u8>>();
        tokio::spawn(async move {
            while let Ok(msg) = outgoing_rx.recv_async().await {
                if let Err(err) = tx.send(Message::Binary(msg.into())).await {
                    error!("WebSocket TX error: {err:?}");
                    return;
                }
            }
        });

        tokio::spawn(rpc.serve(outgoing_tx, incoming_rx));
    })
}

pub type ServerResponse<T> = Json<ServerResult<T>>;

pub async fn start_server(database: Database) -> anyhow::Result<Server> {
    let config = timely::Config::thread();
    let routers = saturn_v_eval::DataflowRouters::default();

    let workers = timely::execute(config, {
        let handle = tokio::runtime::Handle::current();
        let routers = routers.clone();
        move |worker| {
            let (input, output) = saturn_v_eval::dataflow::backend(worker, &routers);
            saturn_v_eval::utils::run_pumps(worker, handle.clone(), input, output);
        }
    })
    .expect("failed to start dataflows");

    std::thread::spawn(move || drop(workers));

    let (inputs, solver, output_rx) = routers.split();

    let server = Server(Arc::new(Mutex::new(ServerInner {
        database,
        inputs,
        sequence: 0,
        program_map: Default::default(),
        relations: HashMap::new(),
    })));

    server
        .make_transaction(|tx| tx.load_dataflow())
        .await
        .context("failed to load database into dataflow")?;

    tokio::spawn(server.clone().handle_dataflow(solver, output_rx));

    Ok(server)
}

pub type ExtractState = axum::extract::State<Server>;

/// A stateful connection from a client.
pub struct Connection {
    /// The server the connection is accessing.
    pub server: Server,

    /// A map of each of the client's transaction handles to actual transactions.
    pub transactions: Mutex<BTreeMap<usize, Transaction<Server>>>,
}

impl Handle<GetTuples> for Connection {
    async fn on_request(&self, request: GetTuples) -> ServerResult<BTreeSet<StructuredValue>> {
        self.server.lock().await.get_relation_values(&request.id)
    }
}

impl HandleSubscribe<WatchRelation> for Connection {
    async fn on_subscribe(
        &self,
        request: WatchRelation,
    ) -> ServerResult<impl Stream<Item = TupleUpdate> + Unpin + Send + 'static> {
        let rx = self
            .server
            .lock()
            .await
            .get_relation(&request.id)?
            .watcher
            .subscribe();

        Ok(BroadcastStream::new(rx)
            .filter_map(move |ev| async move { ev.ok() })
            .boxed())
    }
}

impl Handle<BeginTx> for Connection {
    async fn on_request(&self, request: BeginTx) -> ServerResult<()> {
        let mut transactions = self.transactions.lock().await;

        use std::collections::btree_map::Entry;
        let Entry::Vacant(entry) = transactions.entry(request.tx) else {
            return Err(ServerError::ExistingTransaction);
        };

        let tx = self
            .server
            .lock()
            .await
            .database
            .transaction(self.server.clone())?;

        entry.insert(tx);

        Ok(())
    }
}

impl Handle<CommitTx> for Connection {
    async fn on_request(&self, request: CommitTx) -> ServerResult<TxOutput> {
        self.transactions
            .lock()
            .await
            .remove(&request.tx)
            .ok_or(ServerError::UnknownTransaction)?
            .commit()
            .await
            .map(|_| TxOutput {})
    }
}

impl<T: TxRequest> Handle<TxMethod<T>> for Connection
where
    Transaction<Server>: HandleTx<T>,
{
    async fn on_request(
        &self,
        request: TxMethod<T>,
    ) -> ServerResult<<TxMethod<T> as Request>::Response> {
        self.transactions
            .lock()
            .await
            .get_mut(&request.tx)
            .ok_or(ServerError::UnknownTransaction)?
            .on_request(request.request)
            .await
    }
}

impl<T: TxRequest> Handle<T> for Connection
where
    Server: Handle<T>,
{
    async fn on_request(&self, request: T) -> ServerResult<<T as Request>::Response> {
        self.server.on_request(request).await
    }
}

impl Rpc for Connection {}

#[derive(Clone)]
pub struct Server(pub Arc<Mutex<ServerInner>>);

impl Deref for Server {
    type Target = Mutex<ServerInner>;

    fn deref(&self) -> &Self::Target {
        self.0.as_ref()
    }
}

impl CommitDataflow for Server {
    async fn commit(&mut self, program_map: ProgramMap, events: Vec<InputEvent>) -> SequenceId {
        // acquire lock
        let mut server = self.lock().await;

        // dereference server mutex to permit split mutable borrow
        let server = server.deref_mut();

        // update program map before flushing updates
        server.update_program(program_map);

        // allocate sequence
        let sequence = server.sequence;
        server.sequence += 1;

        // split borrow dataflow inputs and relations
        let (dataflow, relations) = (&mut server.inputs, &mut server.relations);

        // retrieve input relation references
        let mut relations: BTreeMap<_, _> = relations
            .values_mut()
            .filter(|rel| rel.io == RelationIO::Input)
            .map(|input| (input.rel, input))
            .collect();

        // process events
        for event in events {
            // extract an input fact update, if one is set
            let input = match &event {
                InputEvent::Insert(InputEventKind::Fact(fact)) => Some(TupleUpdate::insert(fact)),
                InputEvent::Remove(InputEventKind::Fact(fact)) => Some(TupleUpdate::remove(fact)),
                _ => None,
            };

            // apply an input fact update to relation state
            if let Some(TupleUpdate { state, value }) = input {
                if let Some(relation) = relations.get_mut(&value.relation) {
                    let value = relation.structure_values(&mut value.values.iter());
                    relation.push(TupleUpdate { value, state });
                }
            }

            // push event into dataflow
            use InputEvent::*;
            match event {
                Insert(ev) => dataflow.events.insert(ev),
                Remove(ev) => dataflow.events.remove(ev),
            };
        }

        // flush events to dataflow
        dataflow.events.flush();

        // return sequence
        SequenceId(sequence)
    }
}

impl<T: TxRequest> Handle<T> for Server
where
    Transaction<Self>: HandleTx<T>,
{
    async fn on_request(&self, request: T) -> ServerResult<TxResponse<T::Response>> {
        let mut tx = self.lock().await.database.transaction(self.to_owned())?;
        let result = tx.on_request(request).await?;
        tx.commit().await?;

        Ok(TxResponse {
            tx: TxOutput {},
            response: result,
        })
    }
}

impl Server {
    pub async fn make_transaction<T>(
        &self,
        inner: impl FnOnce(&mut Transaction<Server>) -> ServerResult<T>,
    ) -> ServerResult<T> {
        let mut tx = self.lock().await.database.transaction(self.to_owned())?;
        let result = inner(&mut tx)?;
        tx.commit().await?;
        Ok(result)
    }

    pub async fn handle_dataflow(
        self,
        mut solver: Solver,
        output_rx: flume::Receiver<Update<Fact>>,
    ) {
        let mut running = true;
        while running {
            let _ = solver.step().await;

            let mut outputs = Vec::new();
            loop {
                match output_rx.recv_async().await {
                    Ok(Update::Push(output, state)) => outputs.push((output, state)),
                    Ok(Update::Flush) => break,
                    Err(_) => {
                        running = false;
                        break;
                    }
                }
            }

            if outputs.is_empty() {
                continue;
            }

            let mut server = self.lock().await;

            let mut relations: BTreeMap<_, _> = server
                .relations
                .values_mut()
                .filter(|rel| rel.io == RelationIO::Output)
                .map(|output| (output.rel, output))
                .collect();

            for (value, state) in outputs {
                let relation = relations.get_mut(&value.relation).unwrap();
                let value = relation.structure_values(&mut value.values.iter());
                relation.push(TupleUpdate { value, state });
            }
        }
    }

    pub fn connect(self) -> JsonRpcServer<Connection> {
        let conn = Connection {
            server: self,
            transactions: Default::default(),
        };

        let mut jsonrpc = JsonRpcServer::new(conn);
        jsonrpc.handle_subscription::<WatchRelation>();
        jsonrpc.handle::<GetTuples>();
        jsonrpc.handle_tx::<GetProgram>();
        jsonrpc.handle_tx::<SetProgram>();
        jsonrpc.handle_tx::<ListRelations>();
        jsonrpc.handle_tx::<CheckTuples>();
        jsonrpc.handle_tx::<UpdateInput>();
        jsonrpc.handle_tx::<ClearInput>();
        jsonrpc
    }
}

pub struct ServerInner {
    database: Database,
    inputs: DataflowInputs,
    sequence: u64,
    program_map: ProgramMap,
    relations: HashMap<String, RelationBag>,
}

impl ServerInner {
    /// Updates the current program map after a transaction.
    fn update_program(&mut self, program_map: ProgramMap) {
        // if map has not changed, do not do anything
        if program_map == self.program_map {
            return;
        }

        // otherwise, set new program map
        self.program_map = program_map;

        // clear current relations
        // TODO: reuse relations that share IDs
        self.relations.clear();

        // populate inputs
        for (name, input) in self.program_map.input_relations.iter() {
            self.relations
                .insert(name.clone(), RelationBag::make_input(input));
        }

        // populate outputs
        for (name, output) in self.program_map.output_relations.iter() {
            self.relations
                .insert(name.clone(), RelationBag::make_output(output));
        }
    }

    pub fn get_relation_values(&mut self, name: &str) -> ServerResult<BTreeSet<StructuredValue>> {
        self.get_relation(name).map(|rel| rel.state.clone())
    }

    pub fn subscribe_to_relation(
        &mut self,
        name: &str,
    ) -> Sse<BoxStream<'static, std::result::Result<Event, Infallible>>> {
        match self.get_relation(name) {
            Ok(rel) => Sse::new(
                BroadcastStream::new(rel.watcher.subscribe())
                    .map(move |update| match update {
                        Ok(tuple) => Ok(tuple),
                        Err(_) => Err(ServerError::Lagged),
                    })
                    .map(move |data| Event::default().json_data(data))
                    .map_err(move |_| unreachable!())
                    .boxed(),
            ),
            Err(err) => {
                let ev = Ok(Event::default()
                    .json_data(ServerResult::<()>::Err(err))
                    .unwrap());
                let fut = std::future::ready(ev);
                Sse::new(futures_util::stream::once(fut).boxed())
            }
        }
    }

    pub fn get_relation(&mut self, name: &str) -> ServerResult<&mut RelationBag> {
        self.relations
            .get_mut(name)
            .ok_or(ServerError::NoSuchRelation(name.to_string()))
    }
}

/// Incremental, observable relation contents.
pub struct RelationBag {
    /// The [Bag] containing this relation's values.
    pub values: Bag<StructuredValue>,

    /// The type of this relation.
    pub ty: StructuredType,

    /// The dataflow key of this relation.
    pub rel: Key<Relation>,

    /// The IO of this relation.
    pub io: RelationIO,
}

impl Deref for RelationBag {
    type Target = Bag<StructuredValue>;

    fn deref(&self) -> &Self::Target {
        &self.values
    }
}

impl DerefMut for RelationBag {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.values
    }
}

impl RelationBag {
    /// Creates a relation bag from an [InputRelation].
    pub fn make_input(rel: &InputRelation) -> Self {
        Self {
            values: Default::default(),
            ty: rel.ty.clone(),
            rel: rel.key,
            io: RelationIO::Input,
        }
    }

    /// Creates a relation bag from an [OutputRelation].
    pub fn make_output(rel: &OutputRelation) -> Self {
        Self {
            values: Default::default(),
            ty: rel.ty.clone(),
            rel: rel.key,
            io: RelationIO::Output,
        }
    }

    /// Structures a flat list of values into a [StructuredValue] of this relation's type.
    pub fn structure_values<'a>(
        &self,
        values: &mut impl Iterator<Item = &'a ir::Value>,
    ) -> StructuredValue {
        Self::structure_values_inner(&self.ty, values)
    }

    fn structure_values_inner<'a>(
        ty: &StructuredType,
        values: &mut impl Iterator<Item = &'a ir::Value>,
    ) -> StructuredValue {
        match ty {
            StructuredType::Tuple(els) => StructuredValue::Tuple(
                els.iter()
                    .map(move |ty| Self::structure_values_inner(ty, values))
                    .collect(),
            ),
            StructuredType::Primitive(ty) => {
                use ir::Type;
                use StructuredValue::*;
                let val = values.next().unwrap();
                match (val, ty) {
                    (ir::Value::Boolean(val), Type::Boolean) => Boolean(*val),
                    (ir::Value::Integer(val), Type::Integer) => Integer(*val),
                    (ir::Value::Real(val), Type::Real) => Real(*val),
                    (ir::Value::String(val), Type::String) => String(val.clone()),
                    (ir::Value::Symbol(val), Type::Symbol) => Symbol(val.clone()),
                    _ => panic!(),
                }
            }
        }
    }
}

/// A structure for maintaining incremental, observable "bags" of data (e.g. relation contents).
pub struct Bag<T> {
    /// The instantaneous state of this bag.
    pub state: BTreeSet<T>,

    /// A broadcast sender to send updates to this bag.
    pub watcher: broadcast::Sender<TupleUpdate<T>>,

    /// A broadcast receiver to receive updates to this bag.
    ///
    /// Mainly kept in this struct so that the channel does not close without
    /// active subscriptions.
    pub watcher_rx: broadcast::Receiver<TupleUpdate<T>>,
}

impl<T: Clone> Default for Bag<T> {
    fn default() -> Self {
        let (watcher, watcher_rx) = broadcast::channel(1024);

        Self {
            state: Default::default(),
            watcher,
            watcher_rx,
        }
    }
}

impl<T: Clone + std::fmt::Debug + Ord> Bag<T> {
    /// Pushes a [TupleUpdate] to this bag.
    pub fn push(&mut self, update: TupleUpdate<T>) {
        let changed = match update.state {
            false => self.state.remove(&update.value),
            true => self.state.insert(update.value.clone()),
        };

        if changed {
            self.watcher.send(update).unwrap();
        }
    }
}

/// A JSON-RPC server.
pub struct JsonRpcServer<T> {
    /// The server's state.
    state: Arc<T>,

    /// A slab of subscription thread cancellation tokens.
    cancel_tokens: Arc<Mutex<BTreeMap<usize, flume::Sender<()>>>>,

    /// A map of method names to their handlers.
    handlers: BTreeMap<String, DynHandler>,
}

impl<T: Send + Sync + 'static> JsonRpcServer<T> {
    /// Creates a blank JSON-RPC server.
    pub fn new(state: T) -> Self {
        Self {
            state: Arc::new(state),
            handlers: Default::default(),
            cancel_tokens: Default::default(),
        }
    }

    /// Adds subscription handlers.
    pub fn handle_subscription<R: Subscription + 'static>(&mut self)
    where
        T: HandleSubscribe<R>,
    {
        // register subscription request
        let state = self.state.clone();
        let cancel_tokens = self.cancel_tokens.clone();
        self.add_handler(move |request: Subscribe<R>, tx| {
            let state = state.clone();
            let cancel_tokens = cancel_tokens.clone();
            async move {
                // invoke subscription handler
                let stream = state.on_subscribe(request.param).await?;

                // prepare subscription registration
                let mut cancel_tokens = cancel_tokens.lock().await;

                // ensure token ID is not taken
                use std::collections::btree_map::Entry;
                let Entry::Vacant(entry) = cancel_tokens.entry(request.id) else {
                    return Err(ServerError::ExistingTransaction);
                };

                // create cancellation token channel
                let (cancel_tx, cancel_rx) = flume::bounded(0);

                // register cancellation token
                entry.insert(cancel_tx);

                // asynchronously notify client of events
                tokio::spawn(serve_subscription::<R>(request.id, stream, cancel_rx, tx));

                // success!
                Ok(())
            }
        });

        // register unsubscription request
        let cancel_tokens = self.cancel_tokens.clone();
        self.add_handler(move |request: Unsubscribe<R>, _tx| {
            let cancel_tokens = cancel_tokens.clone();
            async move {
                // attempt to cancel subscription
                cancel_tokens
                    .lock()
                    .await
                    .remove(&request.id)
                    .ok_or(ServerError::UnknownSubscription)?;

                // success
                Ok(())
            }
        });
    }

    /// Adds a handler for a transactional method.
    pub fn handle_tx<R: TxRequest + 'static>(&mut self)
    where
        T: HandleTxMethod<R>,
    {
        self.handle::<R>();
        self.handle::<BeginTx>();
        self.handle::<CommitTx>();
        self.handle::<TxMethod<R>>();
    }

    /// Adds a handler for a request by its state.
    pub fn handle<R: Request + 'static>(&mut self)
    where
        T: Handle<R>,
    {
        let state = self.state.clone();
        self.add_handler(move |request, _tx| {
            let state = state.clone();
            async move { state.on_request(request).await }
        });
    }

    /// Adds a handler closure for a request.
    pub fn add_handler<R: Request + 'static, Fut>(
        &mut self,
        handler: impl Fn(R, flume::Sender<Vec<u8>>) -> Fut + Send + Sync + 'static,
    ) where
        Fut: Future<Output = Result<R::Response, ServerError>> + Send,
    {
        // wrap handler in arc so it can be invoked multiple times
        let handler = Arc::new(handler);

        // initialize a dynamic-dispatch closure
        let handler = move |id, value, reply: flume::Sender<Vec<u8>>| {
            let request = match serde_json::from_value(value) {
                Ok(request) => request,
                Err(err) => {
                    let result = JsonRpcFailure {
                        jsonrpc: "2.0".to_string(),
                        id,
                        error: JsonRpcError {
                            code: -32700,
                            message: format!("Invalid JSON received: {err:?}"),
                        },
                    };

                    let response = serde_json::to_vec(&result).unwrap();
                    let _ = reply.send(response);

                    return;
                }
            };

            let handler = handler.clone();
            tokio::spawn(async move {
                let result = handler(request, reply.clone()).await;

                if id.is_null() {
                    return;
                }

                let success = JsonRpcSuccess {
                    jsonrpc: "2.0".to_string(),
                    id,
                    result,
                };

                let response = serde_json::to_vec(&success).unwrap();
                let _ = reply.send(response);
            });
        };

        // handlers are type-keyed, so ignore if handler already exists
        self.handlers
            .entry(R::name().to_string())
            .or_insert_with(|| Arc::new(handler));
    }

    /// Serves this JSON-RPC server.
    pub async fn serve(self, tx: flume::Sender<Vec<u8>>, rx: flume::Receiver<Vec<u8>>) {
        while let Ok(request) = rx.recv_async().await {
            // deserialize request
            let request: JsonRpcRequest<serde_json::Value> = match serde_json::from_slice(&request)
            {
                Ok(request) => request,
                Err(err) => {
                    error!("failed to deserialize incoming JSON-RPC object: {err:?}");
                    continue;
                }
            };

            // log request
            trace!("recv: {request:?}");

            // check that jsonrpc is set correctly
            if request.jsonrpc != "2.0" {
                error!("incoming JSON object was not marked as jsonrpc = 2.0");
                continue;
            }

            // lookup appropriate handler
            let Some(handler) = self.handlers.get(&request.method) else {
                let result = JsonRpcFailure {
                    jsonrpc: "2.0".to_string(),
                    id: request.id,
                    error: JsonRpcError {
                        code: -32601,
                        message: "Method not found.".to_string(),
                    },
                };

                let response = serde_json::to_vec(&result).unwrap();
                let _ = tx.send(response);

                continue;
            };

            // invoke handler
            (*handler)(request.id, request.param, tx.clone());
        }
    }
}

/// A boxed function for dynamic dispatch in [JsonRpcServer].
pub type DynHandler = Arc<
    dyn Fn(serde_json::Value, serde_json::Value, flume::Sender<Vec<u8>>) + Send + Sync + 'static,
>;

/// Helper method to handle a subscription notification.
pub async fn serve_subscription<R: Subscription>(
    id: usize,
    mut stream: impl Stream<Item = R::Response> + Unpin + Send + 'static,
    cancel_rx: flume::Receiver<()>,
    tx: flume::Sender<Vec<u8>>,
) {
    loop {
        tokio::select! {
            _ = cancel_rx.recv_async() => break,
            ev = stream.next() => match ev {
                None => break, // TODO: implement stream cancellation
                Some(event) => {
                    // serialize JSON-RPC notification
                    let notification = JsonRpcRequest {
                        jsonrpc: "2.0".to_string(),
                        id: serde_json::Value::Null,
                        method: R::name().to_string(),
                        param: SubscriptionEvent {
                            id, event
                        },
                    };

                    // send notification to client
                    // TODO: stream cancellation on close
                    let message = serde_json::to_vec(&notification).unwrap();
                    let _ = tx.send(message);
                }
            }
        }
    }
}
