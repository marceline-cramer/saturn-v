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

use chumsky::prelude::*;
use datatest_stable::Utf8Path;
use saturn_v_eval::load::Loader;
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

    // initialize Tokio runtime on current thread
    let rt = tokio::runtime::Builder::new_current_thread().build()?;
    let _guard = rt.enter();

    // run dataflow to completion
    rt.block_on(saturn_v_eval::run(loader));

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
