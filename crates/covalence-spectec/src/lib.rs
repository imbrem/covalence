//! Wrapper crate for [SpecTec], the DSL the WebAssembly specification is written in.
//!
//! This crate is the single entry point for SpecTec consumption in Covalence.
//! All usage of `wasm_spec_ast`, `spectec_ast`, `spectec_ast_decode`, and
//! `spectec_ast_decode_derive` should go through here.
//!
//! # Layers
//!
//! - [`ast`] — generic SpecTec AST types and S-expression parser
//!   (re-exported [`spectec_ast`]).
//! - [`decode`] / [`decode_derive`] — trait + derive macro for decoding
//!   SpecTec S-expressions into Rust types.
//! - [`wasm`] — the WebAssembly 3.0 specification, pre-dumped as a SpecTec
//!   AST and exposed as Rust data structures (re-exported [`wasm_spec_ast`]).
//!
//! # Status
//!
//! v0 consumes the upstream OCaml SpecTec compiler's S-expression backend
//! via the `cyruscook/spectec_parse` workspace. A native Rust `.watsup`
//! parser is planned for later but not required to start lowering the
//! WebAssembly spec to HOL.
//!
//! This crate (and its inputs) is an **untrusted driver** to the kernel —
//! see [`../../../ARCHITECTURE.md`] §2.6 "derive, don't trust." The lowered
//! HOL artifacts produced from SpecTec output enter the trusted core
//! through the same ingestion paths as any other oracle-produced data.
//!
//! [SpecTec]: https://github.com/Wasm-DSL/spectec

pub use spectec_ast as ast;
pub use spectec_ast_decode as decode;
pub use spectec_ast_decode_derive as decode_derive;
pub use wasm_spec_ast as wasm;
