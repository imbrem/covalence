//! Dump a tiny WASM **component** that exports an `answer: (u32) -> u32`
//! adding 1 to its argument. The component wraps a core module with the
//! standard component-model `(canon lift ...)` lift. Used by the JS host
//! test suite to exercise jco-based component support.
//!
//! Usage:
//!     cargo run --quiet -p covalence-wasm --example dump_answer_component \
//!       > packages/covalence-wasm-js/src/__fixtures__/answer_component.wasm

use std::io::Write;

fn main() {
    let wat = r#"
        (component
          (core module $m
            (func (export "answer") (param $x i32) (result i32)
              local.get $x
              i32.const 1
              i32.add))
          (core instance $i (instantiate $m))
          (func (export "answer") (param "x" u32) (result u32)
            (canon lift (core func $i "answer")))
        )
    "#;
    let bytes = wat::parse_str(wat).expect("parse component wat");
    eprintln!("answer_component.wasm: {} bytes", bytes.len());
    std::io::stdout().write_all(&bytes).expect("write wasm");
}
