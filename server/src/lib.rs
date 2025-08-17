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
    collections::{HashMap, HashSet},
    convert::Infallible,
    hash::Hash,
    sync::Arc,
};

use axum::{
    Json, Router,
    extract::Path,
    response::{Sse, sse::Event},
    routing::{get, post},
};
use futures_util::Stream;
use saturn_v_client::{Program, RelationInfo, StructuredType, Value};
use saturn_v_eval::{
    load::Loader, solve::Solver, types::{Fact, Relation}, utils::{Key, Update}, DataflowInputs
};
use saturn_v_ir::{self as ir};
use serde::Deserialize;
use tokio::sync::{Mutex, broadcast};

#[cfg(test)]
pub mod tests;

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
        program: Program::default(),
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

async fn get_program(server: ExtractState) -> Json<Program> {
    Json(server.lock().await.program.clone())
}

async fn post_program(server: ExtractState, Json(program): Json<Program>) {
    server.lock().await.set_program(program);
}

async fn inputs_list(server: ExtractState) -> Json<Vec<RelationInfo>> {
    Json(
        server
            .lock()
            .await
            .program
            .relations
            .values()
            .filter(|rel| rel.io == ir::RelationIO::Input)
            .map(|rel| RelationInfo {
                name: rel.store.clone(),
                id: rel.store.clone(),
                ty: rel.ty.clone(),
            })
            .collect(),
    )
}

async fn input_update(server: ExtractState, input: Path<String>, Json(updates): Json<Vec<TupleUpdate>>) {
    let mut server = server.lock().await;

    let Some(input) = server.inputs.get(input.as_str()) else {
        // TODO: return some error (and unit test it!)
        return;
    };

    // drop immutable reference to input
    let rel = input.rel.clone();

    for update in updates.into_iter() {
        // TODO: assert types match (and unit test it!)

        let fact = Fact {
            relation: rel,
            values: value_to_fact(update.value).into(),
        };

        // TODO: unit test to assert that you can't remove program facts
        // might require making a separate "inputs" dataflow input
        match update.state {
            true => server.dataflow.facts.insert(fact),
            false => server.dataflow.facts.remove(fact),
        };
    }
}

fn value_to_fact(val: Value) -> Vec<ir::Value> {
    match val {
        Value::Tuple(els) => els.into_iter().flat_map(value_to_fact).collect(),
        Value::Boolean(val) => vec![ir::Value::Boolean(val)],
        Value::String(val) => vec![ir::Value::String(val)],
        Value::Integer(val) => vec![ir::Value::Integer(val)],
        Value::Real(val) => vec![ir::Value::Real(val)],
    }
}

async fn outputs_list(server: ExtractState) -> Json<Vec<RelationInfo>> {
    Json(
        server
            .lock()
            .await
            .outputs
            .iter()
            .map(|(name, output)| RelationInfo {
                name: name.clone(),
                id: name.clone(),
                ty: output.ty.clone(),
            })
            .collect(),
    )
}

async fn get_output(
    server: ExtractState,
    Path(output): Path<String>,
) -> Json<Option<HashSet<Value>>> {
    Json(
        server
            .lock()
            .await
            .outputs
            .get(&output)
            .map(|output| output.state.clone()),
    )
}

async fn subscribe_to_output(
    _server: ExtractState,
    _output: Path<String>,
) -> Sse<impl Stream<Item = Result<Event, Infallible>>> {
    Sse::new(futures_util::stream::empty())
}

pub type ExtractState = axum::extract::State<State>;

pub type State = Arc<Mutex<Server>>;

pub struct Server {
    program: Program,
    dataflow: DataflowInputs,
    inputs: HashMap<String, Input>,
    outputs: HashMap<String, Output>,
}

impl Server {
    /// Updates the currently-running program on the server.
    pub fn set_program(&mut self, program: Program) {
        // load the program
        let loader = Loader::load_program(&program);

        // remove the previous program from dataflow
        self.dataflow.clear();

        // add the new program
        loader.add_to_dataflow(&mut self.dataflow);

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
                watcher,
                watcher_rx,
            };

            self.outputs.insert(rel.store.clone(), output);
        }

        // store the program for retrieval
        self.program = program;
    }

    pub async fn handle_dataflow(
        server: State,
        solver: Solver,
        output_rx: flume::Receiver<Update<Fact>>,
    ) {
    }
}

pub struct Input {
    ty: StructuredType,
    rel: Key<Relation>,
}

pub struct Output {
    state: HashSet<Value>,
    ty: StructuredType,
    watcher: broadcast::Sender<Value>,
    watcher_rx: broadcast::Receiver<Value>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Deserialize)]
pub struct TupleUpdate {
    pub state: bool,
    pub value: Value,
}
