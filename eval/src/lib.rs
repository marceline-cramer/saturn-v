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

use dataflow::DataflowRouters;
use load::Loader;
use solve::Solver;
use utils::run_pumps;

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

    let mut relations = routers.relations_in.into_source();
    let mut facts = routers.facts_in.into_source();
    let mut nodes = routers.nodes_in.into_source();

    loader.add_to_dataflow(&mut relations, &mut facts, &mut nodes);

    relations.forget();
    facts.forget();
    nodes.forget();

    let (output_tx, output_rx) = flume::unbounded();

    let mut solver = Solver::new(
        routers.conditional_out.into_sink(),
        routers.gates_out.into_sink(),
        routers.constraints_out.into_sink(),
        routers.outputs_out.into_sink(),
        output_tx,
    );

    assert_eq!(solver.step().await, Some(true), "failed to run solver");

    let mut outputs = Vec::new();
    while let Ok(crate::utils::Update::Push(output, true)) = output_rx.recv() {
        outputs.push(output);
    }

    outputs.sort();

    for output in outputs {
        println!("{output:?}");
    }
}
