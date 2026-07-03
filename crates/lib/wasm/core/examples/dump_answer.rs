//! One-shot: dump a tiny `(u32) -> u32 { x + 1 }` core module as binary
//! wasm to stdout. Used to build the test fixture for the JS host
//! backend in `packages/covalence-wasm-js`. Stays around in case the
//! fixture needs to be regenerated.
//!
//! Usage:
//!     cargo run --quiet -p covalence-wasm --example dump_answer \
//!       > packages/covalence-wasm-js/src/__fixtures__/answer.wasm

use std::io::Write;

fn main() {
    let wat = r#"(module
        (func (export "answer") (param $x i32) (result i32)
            local.get $x
            i32.const 1
            i32.add))"#;
    let bytes = wat::parse_str(wat).expect("parse wat");
    eprintln!("answer.wasm: {} bytes", bytes.len());
    std::io::stdout().write_all(&bytes).expect("write wasm");
}
