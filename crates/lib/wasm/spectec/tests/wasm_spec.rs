//! Smoke test: the pre-dumped WebAssembly 3.0 SpecTec AST loads and is non-empty.

use covalence_spectec::{ast, wasm};

#[test]
fn wasm_spec_loads() {
    let defs: Vec<ast::SpecTecDef> = wasm::get_wasm_spectec_ast();
    assert!(
        !defs.is_empty(),
        "WASM SpecTec AST must contain definitions"
    );
}

#[test]
fn parse_minimal_stream() {
    // The grammar accepts an empty stream.
    let defs = ast::parse_spectec_stream("").expect("empty stream parses");
    assert!(defs.is_empty());
}
