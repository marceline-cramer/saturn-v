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

use std::{
    collections::{BTreeMap, HashMap, HashSet},
    convert::Infallible,
    sync::Arc,
};

use axum::{
    Json, Router,
    extract::Path,
    response::{Sse, sse::Event},
    routing::{get, post},
};
use futures_util::{StreamExt, TryStreamExt, stream::BoxStream};
use parking_lot::Mutex as SyncMutex;
use saturn_v_client::*;
use saturn_v_eval::{
    DataflowInputs, InputEvent,
    solve::Solver,
    types::{Fact, Relation},
    utils::{Key, Update},
};
use saturn_v_ir::{self as ir};
use tokio::sync::{Mutex, broadcast};
use tokio_stream::wrappers::BroadcastStream;

use crate::db::*;

pub use axum;

#[cfg(test)]
pub mod tests;

pub fn route(server: State) -> Router {
    Router::new()
        .route("/program", get(get_program).post(post_program))
        .route("/inputs/list", get(inputs_list))
        .route("/input/{input}/update", post(input_update))
        .route("/outputs/list", get(outputs_list))
        .route("/output/{output}", get(get_output))
        .route("/output/{output}/subscribe", get(subscribe_to_output))
        .with_state(server)
}

async fn get_program(server: ExtractState) -> ServerResponse<Program> {
    server
        .lock()
        .await
        .make_transaction(|tx| tx.get_program())
        .into()
}

async fn post_program(server: ExtractState, Json(program): Json<Program>) -> ServerResponse<()> {
    server
        .lock()
        .await
        .make_transaction(|tx| tx.set_program(program))
        .into()
}

async fn inputs_list(server: ExtractState) -> ServerResponse<Vec<RelationInfo>> {
    server
        .lock()
        .await
        .make_transaction(|tx| tx.get_program_map())
        .map(|map| {
            map.input_relations
                .values()
                .map(InputRelation::to_info)
                .collect()
        })
        .into()
}

async fn input_update(
    server: ExtractState,
    input: Path<String>,
    Json(updates): Json<Vec<TupleUpdate>>,
) -> ServerResponse<()> {
    server
        .lock()
        .await
        .make_transaction(|tx| tx.update_input(input.as_str(), &updates))
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
        })
        .collect())
    .into()
}

async fn get_output(
    server: ExtractState,
    Path(output): Path<String>,
) -> ServerResponse<Option<HashSet<Value>>> {
    Ok(server
        .lock()
        .await
        .outputs
        .get(&output)
        .map(|output| output.state.clone()))
    .into()
}

async fn subscribe_to_output(
    server: ExtractState,
    Path(output): Path<String>,
) -> Sse<BoxStream<'static, std::result::Result<Event, Infallible>>> {
    let server = server.lock().await;

    let Some(output) = server.outputs.get(&output) else {
        let err: ServerResult<()> = Err(ServerError::NoSuchOutput(output.clone()));
        let ev = Ok(Event::default().json_data(err).unwrap());
        let fut = std::future::ready(ev);
        return Sse::new(futures_util::stream::once(fut).boxed());
    };

    let rx = output.watcher.subscribe();
    drop(server);

    let stream = BroadcastStream::new(rx)
        .map(|update| match update {
            Ok(tuple) => Ok(tuple),
            Err(_) => Err(ServerError::Lagged),
        })
        .map(|data| Event::default().json_data(data))
        .map_err(|_| unreachable!());

    Sse::new(stream.boxed())
}

/// Shared lock around [DataflowEntrypointInner].
#[derive(Clone)]
pub struct DataflowEntrypoint {
    inner: Arc<SyncMutex<DataflowEntrypointInner>>,
}

impl CommitDataflow for DataflowEntrypoint {
    fn commit(&mut self, events: Vec<InputEvent>) -> SequenceId {
        // acquire lock
        let mut inner = self.inner.lock();

        // allocate sequence
        let sequence = inner.sequence;
        inner.sequence += 1;

        // process events
        for event in events {
            use InputEvent::*;
            match event {
                Insert(ev) => inner.inputs.events.insert(ev),
                Remove(ev) => inner.inputs.events.remove(ev),
            };
        }

        // flush events to dataflow
        inner.inputs.events.flush();

        // return sequence
        SequenceId(sequence)
    }
}

impl DataflowEntrypoint {
    pub fn new(inputs: DataflowInputs) -> Self {
        Self {
            inner: Arc::new(SyncMutex::new(DataflowEntrypointInner {
                inputs,
                sequence: 0,
            })),
        }
    }
}

/// Coordinates input to the dataflow.
pub struct DataflowEntrypointInner {
    inputs: DataflowInputs,
    sequence: u64,
}

pub type ServerResponse<T> = Json<ServerResult<T>>;

pub fn start_server(database: Database) -> State {
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

    let server = Arc::new(Mutex::new(Server {
        database,
        dataflow: DataflowEntrypoint::new(inputs),
        program_map: Default::default(),
        outputs: HashMap::new(),
    }));

    tokio::spawn(Server::handle_dataflow(server.clone(), solver, output_rx));

    server
}

pub type ExtractState = axum::extract::State<State>;

pub type State = Arc<Mutex<Server>>;

pub struct Server {
    database: Database,
    dataflow: DataflowEntrypoint,
    program_map: ProgramMap,
    outputs: HashMap<String, Output>,
}

impl Server {
    pub fn make_transaction<T>(
        &mut self,
        inner: impl FnOnce(&mut FjallTransaction<DataflowEntrypoint>) -> ServerResult<T>,
    ) -> ServerResult<T> {
        let dataflow = self.dataflow.clone();
        let mut tx = self.database.transaction(dataflow)?;
        let result = inner(&mut tx)?;
        let program_map = tx.get_program_map()?;
        tx.commit()?;
        self.program_map = program_map;
        self.update_outputs();
        Ok(result)
    }

    pub fn update_outputs(&mut self) {
        // clear current outputs
        // TODO: reuse outputs that share IDs
        self.outputs.clear();

        // populate outputs
        for (name, output) in self.program_map.output_relations.iter() {
            // create output subscription channel
            let (watcher, watcher_rx) = broadcast::channel(1024);

            // create new output
            let output = Output {
                state: Default::default(),
                ty: output.ty.clone(),
                rel: output.key,
                watcher,
                watcher_rx,
            };

            // add output to server
            self.outputs.insert(name.clone(), output);
        }
    }

    pub async fn handle_dataflow(
        server: State,
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

            let mut server = server.lock().await;

            let mut relations: BTreeMap<_, _> = server
                .outputs
                .values_mut()
                .map(|output| (output.rel, output))
                .collect();

            for (output, state) in outputs {
                let relation = relations.get_mut(&output.relation).unwrap();

                let mut vals = output.values.iter();
                let value = structure_values(&relation.ty, &mut vals);

                match state {
                    false => relation.state.remove(&value),
                    true => relation.state.insert(value.clone()),
                };

                let _ = relation.watcher.send(TupleUpdate { state, value });
            }
        }
    }
}

pub fn structure_values<'a>(
    ty: &StructuredType,
    values: &mut impl Iterator<Item = &'a ir::Value>,
) -> Value {
    match ty {
        StructuredType::Tuple(els) => Value::Tuple(
            els.iter()
                .map(move |ty| structure_values(ty, values))
                .collect(),
        ),
        StructuredType::Primitive(ty) => {
            use {Value::*, ir::Type};
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

pub struct Output {
    state: HashSet<Value>,
    ty: StructuredType,
    rel: Key<Relation>,
    watcher: broadcast::Sender<TupleUpdate>,
    watcher_rx: broadcast::Receiver<TupleUpdate>,
}
