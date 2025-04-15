#![no_main]

use chumsky::Parser;
use libfuzzer_sys::fuzz_target;
use saturn_v_ir::{
    sexp::{Sexp, Token},
    Instruction,
};

fuzz_target!(|src: Vec<Token>| {
    let stream = chumsky::Stream::from_iter(
        src.len()..src.len(),
        src.iter()
            .cloned()
            .enumerate()
            .map(|(idx, tok)| (tok, idx..idx)),
    );

    let parser = Instruction::parser().then_ignore(chumsky::primitive::end());
    let Ok(ir) = parser.parse(stream) else {
        return;
    };

    let mut output = String::new();
    ir.to_doc().render_fmt(80, &mut output).unwrap();
    let got = Token::lexer().parse(output.as_str()).unwrap();
    assert_eq!(src, got);
});
