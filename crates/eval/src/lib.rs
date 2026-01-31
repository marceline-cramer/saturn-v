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

use std::{collections::HashMap, io::Write};

use flume::Receiver;
use load::Loader;
use saturn_v_ir::StructuredType;
use solve::Solver;
use types::*;
use utils::{run_pumps, InputRouter, InputSource, Key, OutputRouter, Update};

pub mod dataflow;
pub mod load;
pub mod solve;
pub mod types;
pub mod utils;

#[cfg(test)]
pub mod tests;

pub async fn run(loader: Loader<String>) {
    let config = timely::Config::thread();
    let routers = DataflowRouters::default();

    let workers = timely::execute(config, {
        let handle = tokio::runtime::Handle::current();
        let routers = routers.clone();
        move |worker| {
            let (input, output) = crate::dataflow::backend(worker, &routers);
            run_pumps(worker, handle.clone(), input, output);
        }
    })
    .expect("failed to start dataflows");

    std::thread::spawn(move || drop(workers));

    let formats: HashMap<_, _> = loader
        .relations
        .values()
        .map(|rel| (Key::new(rel), format_relation(&rel.name, &rel.ty)))
        .collect();

    let (mut inputs, mut solver, output_rx) = routers.split();

    loader.add_to_dataflow(&mut inputs);

    // TODO: why is forgetting necessary?
    inputs.events.forget();

    assert_eq!(solver.step().await, Some(true), "failed to run solver");

    let mut outputs = Vec::new();
    while let Ok(crate::utils::Update::Push(output, true)) = output_rx.recv() {
        outputs.push(output);
    }

    outputs.sort();

    let mut stdout = std::io::stdout();
    for output in outputs {
        let mut format = formats.get(&output.relation).unwrap().iter();

        // intersperse formatting segments with each value in the tuple
        write!(stdout, "{}", format.next().unwrap()).unwrap();
        for (format, val) in format.zip(output.values.iter()) {
            write!(stdout, "{val}{format}").unwrap();
        }

        writeln!(stdout).unwrap();
    }

    stdout.flush().unwrap();
}

/// Create formatting string segments for a relation.
pub fn format_relation(name: &str, ty: &StructuredType) -> Vec<String> {
    // create a string with '*' characters where each value goes
    let mut formatted = String::new();

    // push the name of the relation itself
    formatted.push_str(name);

    // format the root type based on its type
    if let StructuredType::Primitive(_) = ty {
        // for primitives, separate the value from the relation name
        formatted.push_str(" *");
    } else {
        // every other type is deeply structured and doesn't need a space
        formatted.push_str(&format_type(ty));
    }

    // append a period to the final formatting string
    formatted.push('.');

    // split the formatting string into segments
    formatted.split("*").map(str::to_string).collect()
}

/// Format a structured type.
pub fn format_type(ty: &StructuredType) -> String {
    use StructuredType::*;
    match ty {
        Primitive(_) => "*".to_string(),
        Tuple(els) => {
            let terms: Vec<_> = els.iter().map(format_type).collect();
            let inner = terms.join(", ");
            format!("({inner})")
        }
    }
}

#[derive(Clone, Default)]
pub struct DataflowRouters {
    pub events_in: InputRouter<InputEventKind>,
    pub conditional_out: OutputRouter<(Key<Fact>, ConditionalLink)>,
    pub gates_out: OutputRouter<Gate>,
    pub constraints_out: OutputRouter<ConstraintGroup>,
    pub outputs_out: OutputRouter<Fact>,
}

impl DataflowRouters {
    pub fn split(self) -> (DataflowInputs, Solver, Receiver<Update<Fact>>) {
        let inputs = DataflowInputs {
            events: self.events_in.into_source(),
        };

        let (output_tx, output_rx) = flume::unbounded();

        let solver = Solver::new(
            self.conditional_out.into_sink(),
            self.gates_out.into_sink(),
            self.constraints_out.into_sink(),
            self.outputs_out.into_sink(),
            output_tx,
        );

        (inputs, solver, output_rx)
    }
}

pub struct DataflowInputs {
    pub events: InputSource<InputEventKind>,
}

/// A single input event that modifies the contents of the dataflow.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum InputEvent {
    Insert(InputEventKind),
    Remove(InputEventKind),
}

impl InputEvent {
    pub fn insert(self) -> Option<InputEventKind> {
        match self {
            InputEvent::Insert(kind) => Some(kind),
            _ => None,
        }
    }

    pub fn remove(self) -> Option<InputEventKind> {
        match self {
            InputEvent::Remove(kind) => Some(kind),
            _ => None,
        }
    }
}

/// Underlying event contents for dataflow inputs that can be inserted and removed.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum InputEventKind {
    Relation(Relation),
    Fact(Fact),
    Node(Node),
}

impl InputEventKind {
    pub fn relation(self) -> Option<Relation> {
        match self {
            InputEventKind::Relation(rel) => Some(rel),
            _ => None,
        }
    }

    pub fn fact(self) -> Option<Fact> {
        match self {
            InputEventKind::Fact(fact) => Some(fact),
            _ => None,
        }
    }

    pub fn node(self) -> Option<Node> {
        match self {
            InputEventKind::Node(node) => Some(node),
            _ => None,
        }
    }
}
