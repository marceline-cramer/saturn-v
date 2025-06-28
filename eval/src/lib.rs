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

use std::collections::HashMap;

use flume::Receiver;
use load::Loader;
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

    let formatting: HashMap<_, _> = loader
        .relations
        .values()
        .map(|rel| (Key::new(rel), rel.formatting.clone()))
        .collect();

    let (mut inputs, mut solver, output_rx) = routers.split();

    loader.add_to_dataflow(&mut inputs);

    inputs.relations.forget();
    inputs.facts.forget();
    inputs.nodes.forget();

    assert_eq!(solver.step().await, Some(true), "failed to run solver");

    let mut outputs = Vec::new();
    while let Ok(crate::utils::Update::Push(output, true)) = output_rx.recv() {
        outputs.push(output);
    }

    outputs.sort();

    for output in outputs {
        let mut format = formatting.get(&output.relation).unwrap().iter();

        print!("{}", format.next().unwrap());

        for (format, val) in format.zip(output.values.iter()) {
            print!("{val}{format}");
        }

        println!();
    }
}

#[derive(Clone, Default)]
pub struct DataflowRouters {
    pub relations_in: InputRouter<Relation>,
    pub facts_in: InputRouter<Fact>,
    pub nodes_in: InputRouter<Node>,
    pub conditional_out: OutputRouter<(Key<Fact>, Option<Condition>)>,
    pub gates_out: OutputRouter<Gate>,
    pub constraints_out: OutputRouter<ConstraintGroup>,
    pub outputs_out: OutputRouter<Fact>,
}

impl DataflowRouters {
    pub fn split(self) -> (DataflowInputs, Solver, Receiver<Update<Fact>>) {
        let inputs = DataflowInputs {
            relations: self.relations_in.into_source(),
            facts: self.facts_in.into_source(),
            nodes: self.nodes_in.into_source(),
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
    pub relations: InputSource<Relation>,
    pub facts: InputSource<Fact>,
    pub nodes: InputSource<Node>,
}
