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
    sync::Arc,
};

use axum::{
    Json, Router,
    extract::Path,
    response::{Sse, sse::Event},
    routing::{get, post},
};
use futures_util::Stream;
use ordered_float::OrderedFloat;
use saturn_v_eval::{DataflowInputs, load::Loader, solve::Solver};
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
        dataflow: inputs,
        outputs: HashMap::new(),
    }));

    tokio::spawn(Server::handle_dataflow(server.clone(), solver, output_rx));

    server
}

pub fn route(server: State) -> Router<State> {
    Router::new()
        .with_state(server)
        .route("/program", get(get_program).post(post_program))
        .route("/inputs/list", get(inputs_list))
        .route("/input/{input}/update", post(input_update))
        .route("/outputs/list", get(outputs_list))
        .route("/output/{output}", get(get_output))
        .route("/output/{output}/subscribe", get(subscribe_to_output))
}

async fn get_program(server: ExtractState) -> Json<Program> {}

async fn post_program(server: ExtractState, Json(program): Json<Program>) {}

async fn inputs_list(server: ExtractState) -> Json<Vec<String>> {
    todo!()
}

async fn input_update(server: ExtractState, input: Path<String>, updates: Json<Vec<TupleUpdate>>) {}

async fn outputs_list(server: ExtractState) -> Json<Vec<String>> {
    todo!()
}

async fn get_output(
    server: ExtractState,
    Path(output): Path<String>,
) -> Json<Option<HashSet<Value>>> {
    server
        .lock()
        .await
        .outputs
        .get(&output)
        .map(|output| output.state.clone())
        .into()
}

async fn subscribe_to_output(
    server: ExtractState,
    output: Path<String>,
) -> Sse<impl Stream<Item = Result<Event, Infallible>>> {
    Sse::new(futures_util::stream::empty())
}

pub type ExtractState = axum::extract::State<State>;

pub type State = Arc<Mutex<Server>>;

pub struct Server {
    dataflow: DataflowInputs,
    outputs: HashMap<String, Output>,
}

impl Server {
    /// Updates the currently-running program on the server.
    pub fn set_program(&mut self, loader: Loader<String>) {
        // remove the previous program from dataflow
        self.dataflow.clear();

        // add the new program
        loader.add_to_dataflow(&mut self.dataflow);
    }

    pub async fn handle_dataflow(
        server: State,
        solver: Solver,
        output_rx: flume::Receiver<Update<Fact>>,
    ) {
        let _ = solver.step();
    }
}

pub struct Output {
    state: HashSet<Value>,
    watcher: broadcast::Sender<Value>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Deserialize)]
pub struct TupleUpdate {
    pub state: bool,
    pub value: Value,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Deserialize)]
pub enum Value {
    Tuple(Vec<Value>),
    String(String),
    Boolean(bool),
    Integer(i64),
    Real(OrderedFloat<f64>),
}

impl Value {
    pub fn ty(&self) -> Type {
        use Value::*;
        match self {
            Tuple(els) => Type::Tuple(els.iter().map(Value::ty).collect()),
            String(_) => Type::String,
            Boolean(_) => Type::Boolean,
            Integer(_) => Type::Integer,
            Real(_) => Type::Real,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Deserialize)]
pub enum Type {
    Tuple(Vec<Type>),
    String,
    Boolean,
    Integer,
    Real,
}
