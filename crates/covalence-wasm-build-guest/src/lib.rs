//! Wasm32 guest: build a `(x: i32) -> i32 { x + delta }` core module
//! using the **real** `covalence_wasm::build::ModuleBuilder`. Loaded by
//! `packages/covalence-wasm-js` as the canonical "WASM-builds-WASM"
//! demo — JS contributes only the low-level executor; the build logic
//! is this Rust crate.
//!
//! Calling convention (intentionally primitive — kept this side of the
//! component model for now):
//!
//! 1. JS calls `build_plus(delta: i32) -> i32`. The Rust code writes
//!    the produced wasm bytes into a static buffer; the return value
//!    is the byte length.
//! 2. JS calls `output_ptr() -> i32` to get the offset into linear
//!    memory where the bytes live. Reads `length` bytes from there.
//! 3. Bytes are a valid core wasm module exporting `answer: (i32) -> i32`.
//!
//! The buffer is reused across `build_plus` calls — read the bytes
//! before invoking again. No allocator import needed; `Vec`'s default
//! allocator is reused.

use std::cell::RefCell;

use covalence_wasm::build::{ModuleBuilder, ValType};

thread_local! {
    static OUTPUT: RefCell<Vec<u8>> = const { RefCell::new(Vec::new()) };
}

/// Build a `(x: i32) -> i32 { x + delta }` core module, stash bytes,
/// return their length. Exported as the WASM function `build_plus`.
#[unsafe(no_mangle)]
pub extern "C" fn build_plus(delta: i32) -> i32 {
    let mut m = ModuleBuilder::new();
    let mut f = m.func(&[ValType::I32], &[ValType::I32]);
    // `FuncBody::finish` emits the terminal `End` — don't add `.end()`.
    f.local_get(0).i32_const(delta).i32_add();
    let f_idx = f.finish(&mut m);
    m.export_func("answer", f_idx);
    let bytes = m.finish();
    let len = bytes.len() as i32;
    OUTPUT.with(|o| *o.borrow_mut() = bytes);
    len
}

/// Pointer to the start of the byte buffer produced by the most recent
/// `build_plus` call. Stable across reads as long as `build_plus` is
/// not invoked again.
#[unsafe(no_mangle)]
pub extern "C" fn output_ptr() -> i32 {
    OUTPUT.with(|o| o.borrow().as_ptr() as i32)
}
