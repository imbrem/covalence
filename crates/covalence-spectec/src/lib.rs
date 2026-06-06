//! Wrapper crate for [SpecTec], the DSL the WebAssembly specification is written in.
//!
//! Layers:
//!
//! - [`ast`] / [`decode`] / [`decode_derive`] / [`wasm`] — upstream
//!   `cyruscook/spectec_parse` re-exports. These give us the WebAssembly 3.0
//!   spec already elaborated, plus the S-expression AST format the OCaml
//!   reference dumps.
//! - [`source`], [`token`], [`lex`], [`cst`], [`parse`] — native Rust
//!   lexer + parser, in progress. Phase 1 covers `syntax` and `def` forms.
//!
//! # Status
//!
//! v0 consumes the upstream OCaml SpecTec compiler's S-expression backend
//! via the `cyruscook/spectec_parse` workspace. A native Rust `.watsup`
//! frontend is being built incrementally; see
//! `docs/sketches/spectec-verification-plan.md`.
//!
//! This crate (and its inputs) is an **untrusted driver** to the kernel —
//! see `ARCHITECTURE.md` §2.6 "derive, don't trust." The lowered HOL
//! artifacts produced from SpecTec output enter the trusted core through
//! the same ingestion paths as any other oracle-produced data.
//!
//! Native passes here are designed for eventual lifting into kernel-verified
//! computations, so the code style is functional and total:
//! every pass is a `fn input -> Result<Output, Diagnostic>` with no global
//! mutable state, no interior mutability, no `unsafe`.
//!
//! [SpecTec]: https://github.com/Wasm-DSL/spectec

#![forbid(unsafe_code)]

pub use spectec_ast as ast;
pub use spectec_ast_decode as decode;
pub use spectec_ast_decode_derive as decode_derive;
pub use wasm_spec_ast as wasm;

pub mod ast_doc;
pub mod cst;
pub mod elab;
pub mod lex;
pub mod mixfix;
pub mod parse;
pub mod source;
pub mod token;
