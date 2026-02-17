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

#![no_main]

use chumsky::{
    span::{SimpleSpan, Span},
    Parser,
};
use libfuzzer_sys::fuzz_target;
use saturn_v_ir::{
    sexp::{Sexp, Token},
    Program,
};

fuzz_target!(|src: Vec<Token>| {
    let with_spans = src
        .clone()
        .into_iter()
        .enumerate()
        .map(|(idx, tok)| (tok, SimpleSpan::new((), idx..idx)));

    let input = chumsky::input::IterInput::new(with_spans, (src.len()..src.len()).into());

    let parser = Program::<String>::parser().then_ignore(chumsky::primitive::end());
    let Ok(ir) = parser.parse(input).into_result() else {
        return;
    };

    eprintln!("program:\n{ir:#?}");

    let mut output = String::new();
    ir.to_doc().render_fmt(80, &mut output).unwrap();
    let got = Token::lexer().parse(output.as_str()).unwrap();
    assert_eq!(src, got);
});
