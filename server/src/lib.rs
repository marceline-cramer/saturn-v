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
    ops::DerefMut,
    sync::Arc,
};

use axum::{
    Json, Router,
    extract::Path,
    response::{Sse, sse::Event},
    routing::{get, post},
};
use futures_util::{StreamExt, TryStreamExt, stream::BoxStream};
use saturn_v_client::*;
use saturn_v_eval::{
    DataflowInputs,
    load::Loader,
    solve::Solver,
    types::{Fact, Relation},
    utils::{Key, Update},
};
use saturn_v_ir::{self as ir};
use tokio::sync::{Mutex, broadcast};
use tokio_stream::wrappers::BroadcastStream;

pub use axum;

pub mod db;
#[cfg(test)]
pub mod tests;

pub type ServerResponse<T> = Json<ServerResult<T>>;

pub fn start_server() -> State {
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
        program: None,
        dataflow: inputs,
        inputs: HashMap::new(),
        outputs: HashMap::new(),
    }));

    tokio::spawn(Server::handle_dataflow(server.clone(), solver, output_rx));

    server
}

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
        .program
        .clone()
        .ok_or(ServerError::NoProgramLoaded)
        .into()
}

async fn post_program(server: ExtractState, Json(program): Json<Program>) -> ServerResponse<()> {
    if let Err(err) = program.validate() {
        return Err(ServerError::InvalidProgram(err)).into();
    }

    server.lock().await.set_program(program);
    Ok(()).into()
}

async fn inputs_list(server: ExtractState) -> ServerResponse<Vec<RelationInfo>> {
    Ok(server
        .lock()
        .await
        .inputs
        .iter()
        .map(|(name, input)| RelationInfo {
            name: name.clone(),
            id: name.clone(),
            ty: input.ty.clone(),
        })
        .collect())
    .into()
}

async fn input_update(
    server: ExtractState,
    input: Path<String>,
    Json(updates): Json<Vec<TupleUpdate>>,
) -> ServerResponse<()> {
    let mut server = server.lock().await;

    // dereference server lock to split mutable borrow
    let server: &mut Server = server.deref_mut();
    let facts = &mut server.dataflow.facts;

    let Some(input) = server.inputs.get_mut(input.as_str()) else {
        return Err(ServerError::NoSuchInput(input.clone())).into();
    };

    for update in updates.into_iter() {
        if update.value.ty() != input.ty {
            return Err(ServerError::TypeMismatch {
                expected: input.ty.clone(),
                got: update.value.ty(),
            })
            .into();
        }

        let fact = Fact {
            relation: input.rel,
            values: value_to_fact(update.value.clone()).into(),
        };

        // use state to guide updating of dataflow
        // this avoids removal of program facts
        match update.state {
            true => {
                if input.state.insert(update.value) {
                    facts.insert(fact);
                }
            }
            false => {
                if input.state.remove(&update.value) {
                    facts.remove(fact);
                }
            }
        };
    }

    server.dataflow.facts.flush();

    Ok(()).into()
}

fn value_to_fact(val: Value) -> Vec<ir::Value> {
    match val {
        Value::Tuple(els) => els.into_iter().flat_map(value_to_fact).collect(),
        Value::Boolean(val) => vec![ir::Value::Boolean(val)],
        Value::String(val) => vec![ir::Value::String(val)],
        Value::Integer(val) => vec![ir::Value::Integer(val)],
        Value::Real(val) => vec![ir::Value::Real(val)],
        Value::Symbol(val) => vec![ir::Value::Symbol(val)],
    }
}

async fn outputs_list(server: ExtractState) -> ServerResponse<Vec<RelationInfo>> {
    Ok(server
        .lock()
        .await
        .outputs
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

pub type ExtractState = axum::extract::State<State>;

pub type State = Arc<Mutex<Server>>;

pub struct Server {
    program: Option<Program>,
    dataflow: DataflowInputs,
    inputs: HashMap<String, Input>,
    outputs: HashMap<String, Output>,
}

impl Server {
    /// Updates the currently-running program on the server.
    pub fn set_program(&mut self, program: Program) {
        // load the program
        let loader = Loader::load_program(&program);

        // update inputs
        self.inputs.clear();
        for rel in program.relations.values() {
            if rel.io != ir::RelationIO::Input {
                continue;
            }

            let input = Input {
                state: HashSet::new(),
                ty: rel.ty.clone(),
                rel: loader.relation_key(&rel.store).unwrap(),
            };

            self.inputs.insert(rel.store.clone(), input);
        }

        // update outputs
        self.outputs.clear();
        for rel in program.relations.values() {
            if rel.io != ir::RelationIO::Output {
                continue;
            }

            let (watcher, watcher_rx) = broadcast::channel(1024);

            let output = Output {
                state: HashSet::new(),
                ty: rel.ty.clone(),
                rel: loader.relation_key(&rel.store).unwrap(),
                watcher,
                watcher_rx,
            };

            self.outputs.insert(rel.store.clone(), output);
        }

        // remove the previous program from dataflow
        self.dataflow.clear();

        // add the new program
        loader.add_to_dataflow(&mut self.dataflow);

        // store the program for retrieval
        self.program = Some(program);
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

pub struct Input {
    state: HashSet<Value>,
    ty: StructuredType,
    rel: Key<Relation>,
}

pub struct Output {
    state: HashSet<Value>,
    ty: StructuredType,
    rel: Key<Relation>,
    watcher: broadcast::Sender<TupleUpdate>,
    watcher_rx: broadcast::Receiver<TupleUpdate>,
}
