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

#![no_main]

use chumsky::Parser;
use libfuzzer_sys::fuzz_target;
use saturn_v_ir::{
    sexp::{Sexp, Token},
    Instruction,
};

fuzz_target!(|src: Instruction| {
    let mut output = String::new();
    src.to_doc().render_fmt(80, &mut output).unwrap();

    let got = Token::lexer().parse(output.as_str()).unwrap();

    let stream = chumsky::Stream::from_iter(
        got.len()..got.len(),
        got.iter()
            .cloned()
            .enumerate()
            .map(|(idx, tok)| (tok, idx..idx)),
    );

    let parser = Instruction::parser().then_ignore(chumsky::primitive::end());
    let Ok(got) = parser.parse(stream) else {
        return;
    };

    assert_eq!(src, got);
});
