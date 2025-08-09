use std::{collections::HashMap, convert::Infallible, sync::Arc};

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

pub fn start_server() -> Server {
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
}

pub fn route(server: Server) -> Router<Arc<Mutex<Server>>> {
    Router::new()
        .with_state(Arc::new(Mutex::new(server)))
        .route("/program", get(get_program).post(post_program))
        .route("/inputs/list", get(inputs_list))
        .route("/input/{input}/update", post(input_update))
        .route("/outputs/list", get(outputs_list))
        .route("/output/{output}/subscribe", get(subscribe_to_output))
}

async fn get_program(server: State) -> Json<Program> {}

async fn post_program(server: State, Json(program): Json<Program>) {}

async fn inputs_list(server: State) -> Json<Vec<String>> {
    todo!()
}

async fn input_update(server: State, input: Path<String>, updates: Json<Vec<TupleUpdate>>) {}

async fn outputs_list(server: State) -> Json<Vec<String>> {
    todo!()
}

async fn subscribe_to_output(
    server: State,
    output: Path<String>,
) -> Sse<impl Stream<Item = Result<Event, Infallible>>> {
    Sse::new(futures_util::stream::empty())
}

pub type Program = saturn_v_ir::Program<String>;

pub type State = axum::extract::State<Arc<Mutex<Server>>>;

pub struct Server {
    inputs: DataflowInputs,
    outputs: HashMap<String, broadcast::Sender<Value>>,
}

impl Server {
    /// Updates the currently-running program on the server.
    pub fn set_program(&mut self, loader: Loader<String>) {
        // remove the previous program
        self.inputs.clear();

        // destroy all output subscriptions
        self.outputs.clear();

        // add the new program
        loader.add_to_dataflow(&mut self.inputs);
    }
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
