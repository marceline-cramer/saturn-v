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

use chumsky::prelude::*;
use datatest_stable::Utf8Path;
use saturn_v_eval::{
    load::Loader,
    utils::{run_pumps, Key},
    DataflowRouters,
};
use saturn_v_ir::{sexp::*, Program, StructuredType};

datatest_stable::harness! {
    { test = run_test, root = "tests/fixtures" },
}

fn run_test(_path: &Utf8Path, test: String) -> datatest_stable::Result<()> {
    // parse and load program from IR sexp
    let tokens = Token::lex_expect(&test);
    let parser = Program::parser().then_ignore(end());
    let program = parse_expect(&test, parser.parse(tokens).into_result());
    let loader = Loader::load_program(&program);

    // create formatting strings for relationship formatting
    let formats: HashMap<_, _> = loader
        .get_relations()
        .values()
        .map(|rel| (Key::new(rel), format_relation(&rel.name, &rel.ty)))
        .collect();

    // initialize Tokio runtime on current thread
    let rt = tokio::runtime::Builder::new_current_thread().build()?;
    let _guard = rt.enter();

    // spawn dataflow worker
    let config = timely::Config::thread();
    let routers = DataflowRouters::default();
    let workers = timely::execute(config, {
        let handle = tokio::runtime::Handle::current();
        let routers = routers.clone();
        move |worker| {
            let (input, output) = saturn_v_eval::dataflow::backend(worker, &routers);
            run_pumps(worker, handle.clone(), input, output);
        }
    });

    // drop (and join) workers on new thread to not block this function
    // TODO: reliably cancel dataflow by dropping channels
    std::thread::spawn(move || drop(workers));

    // feed loaded program into dataflow
    let (mut inputs, mut solver, output_rx) = routers.split();
    loader.add_to_dataflow(&mut inputs);
    inputs.events.forget(); // TODO: why is forgetting necessary?

    // assert that the program evaluates and solves successfully
    assert_eq!(
        rt.block_on(solver.step()),
        Some(true),
        "failed to run solver"
    );

    // drain the outputs from the solver run
    let mut outputs = Vec::new();
    while let Ok(saturn_v_eval::utils::Update::Push(output, true)) = output_rx.recv() {
        outputs.push(output);
    }

    // render formatted outputs
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

    // success
    Ok(())
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
