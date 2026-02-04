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
    collections::{BTreeMap, HashMap, HashSet},
    convert::Infallible,
    hash::Hash,
    ops::{Deref, DerefMut},
    sync::Arc,
};

use anyhow::Context;
use axum::{
    extract::Path,
    response::{sse::Event, Sse},
    routing::{get, post},
    Json, Router,
};
use futures_util::{stream::BoxStream, StreamExt, TryStreamExt};
use saturn_v_eval::{
    solve::Solver,
    types::{Fact, Relation},
    utils::{Key, Update},
    DataflowInputs, InputEvent, InputEventKind,
};
use saturn_v_protocol::{ir::RelationIO, *};
use tokio::sync::{broadcast, Mutex};
use tokio_stream::wrappers::BroadcastStream;

use crate::db::*;

pub use axum;

#[cfg(test)]
pub mod tests;

pub fn route(server: Server) -> Router {
    Router::new()
        .route("/program", get(get_program).post(post_program))
        .route("/inputs/list", get(inputs_list))
        .route("/input/{input}", get(get_input))
        .route("/input/{input}/subscribe", get(subscribe_to_input))
        .route("/input/{input}/update", post(input_update))
        .route("/outputs/list", get(outputs_list))
        .route("/output/{output}", get(get_output))
        .route("/output/{output}/subscribe", get(subscribe_to_output))
        .with_state(server)
}

async fn get_program(server: ExtractState) -> ServerResponse<Program> {
    server.make_transaction(|tx| tx.get_program()).await.into()
}

async fn post_program(server: ExtractState, Json(program): Json<Program>) -> ServerResponse<()> {
    server
        .make_transaction(|tx| tx.set_program(program))
        .await
        .into()
}

async fn inputs_list(server: ExtractState) -> ServerResponse<Vec<RelationInfo>> {
    Ok(server
        .lock()
        .await
        .program_map
        .input_relations
        .values()
        .map(InputRelation::to_info)
        .collect::<Vec<_>>())
    .into()
}

async fn get_input(
    server: ExtractState,
    Path(input): Path<String>,
) -> ServerResponse<HashSet<StructuredValue>> {
    server
        .lock()
        .await
        .get_relation_values(&input, RelationIO::Input)
        .into()
}

async fn subscribe_to_input(
    server: ExtractState,
    Path(input): Path<String>,
) -> Sse<BoxStream<'static, std::result::Result<Event, Infallible>>> {
    server
        .lock()
        .await
        .subscribe_to_relation(&input, RelationIO::Input)
}

async fn input_update(
    server: ExtractState,
    input: Path<String>,
    Json(updates): Json<Vec<TupleUpdate>>,
) -> ServerResponse<()> {
    server
        .make_transaction(|tx| tx.update_input(input.as_str(), &updates))
        .await
        .into()
}

async fn outputs_list(server: ExtractState) -> ServerResponse<Vec<RelationInfo>> {
    Ok(server
        .lock()
        .await
        .program_map
        .output_relations
        .iter()
        .map(|(name, output)| RelationInfo {
            name: name.clone(),
            id: name.clone(),
            ty: output.ty.clone(),
            is_input: false,
        })
        .collect())
    .into()
}

async fn get_output(
    server: ExtractState,
    Path(output): Path<String>,
) -> ServerResponse<HashSet<StructuredValue>> {
    server
        .lock()
        .await
        .get_relation_values(&output, RelationIO::Output)
        .into()
}

async fn subscribe_to_output(
    server: ExtractState,
    Path(output): Path<String>,
) -> Sse<BoxStream<'static, std::result::Result<Event, Infallible>>> {
    server
        .lock()
        .await
        .subscribe_to_relation(&output, RelationIO::Output)
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
    FjallTransaction<Self>: HandleTx<T>,
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
        inner: impl FnOnce(&mut FjallTransaction<Server>) -> ServerResult<T>,
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

    pub fn get_relation_values(
        &mut self,
        name: &str,
        io: RelationIO,
    ) -> ServerResult<HashSet<StructuredValue>> {
        self.get_relation(name, io).map(|rel| rel.state.clone())
    }

    pub fn subscribe_to_relation(
        &mut self,
        name: &str,
        io: RelationIO,
    ) -> Sse<BoxStream<'static, std::result::Result<Event, Infallible>>> {
        match self.get_relation(name, io) {
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

    fn get_relation(&mut self, name: &str, io: RelationIO) -> ServerResult<&mut RelationBag> {
        self.relations
            .get_mut(name)
            .filter(|rel| rel.io == io)
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
    pub state: HashSet<T>,

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

impl<T: Clone + std::fmt::Debug + Hash + Eq> Bag<T> {
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
pub struct JsonRpcServer {
    /// A map of method names to their handlers.
    handlers: BTreeMap<String, DynHandler>,

    /// A sender of serialized JSON values to the outgoing transport.
    tx: flume::Sender<String>,
}

impl JsonRpcServer {
    /// Adds a handler for a request by its state.
    pub fn add_handler<T: Request>(&mut self, state: impl Handle<T>) {
        // initialize a dynamic-dispatch closure
        let handler = move |value, reply| {};

        // insert dynamic handler
        self.handlers
            .insert(T::name().to_string(), Arc::new(handler));
    }
}

/// A boxed function for dynamic dispatch in [JsonRpcServer].
pub type DynHandler =
    Arc<dyn Fn(serde_json::Value, flume::Sender<serde_json::Value>) + Send + 'static>;
