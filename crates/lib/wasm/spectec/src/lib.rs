//! Wrapper crate for [SpecTec], the DSL the WebAssembly specification is
//! written in.
//!
//! This crate is **AST-first**: it consumes the elaborated SpecTec AST
//! produced by the upstream OCaml SpecTec compiler (the
//! `cyruscook/spectec_parse` workspace) and exposes it — plus the *grammars*
//! it carries — in a form Covalence's untrusted kernel frontend can lower
//! into byte predicates. The elaborated AST is the surface we
//! actually want to compile *from*.
//!
//! # Layers
//!
//! - [`ast`] / [`decode`] / [`decode_derive`] / [`wasm`] — upstream
//!   `cyruscook/spectec_parse` re-exports. [`wasm::get_wasm_spectec_ast`]
//!   gives the WebAssembly 3.0 spec already elaborated to
//!   [`ast::SpecTecDef`]s.
//! - [`grammar`] — typed access to the **grammar** definitions
//!   ([`ast::SpecTecDef::Gram`]): the WASM grammars plus a handful of small,
//!   self-contained grammars (the WASM preamble, LEB128 bytes, …) that are
//!   useful for bootstrapping the byte-parsing infrastructure.
//! - [`regex`] — the bridge between the elaborated SpecTec grammar AST
//!   ([`ast::SpecTecSym`]) and the [`covalence_grammar`] proper-regex AST,
//!   over both the `char` and `u8` (byte) alphabets. The byte path is what
//!   feeds `covalence-init`'s grammar → bytes-predicate compiler.
//!
//! # Trust
//!
//! This crate (and its inputs) is an **untrusted driver** to the kernel:
//! "derive, don't trust." Anything lowered from a SpecTec grammar into HOL
//! is re-checked by `covalence-core` through the normal ingestion paths;
//! nothing here grows the TCB.
//!
//! Like other surface-language crates that may be lifted into kernel-verified
//! computations, the code style is functional and total — every pass is a
//! `fn input -> Result<Output, _>` with no global mutable state, no interior
//! mutability, no `unsafe`.
//!
//! [SpecTec]: https://github.com/Wasm-DSL/spectec

#![forbid(unsafe_code)]

pub use spectec_ast as ast;
pub use spectec_ast_decode as decode;
pub use spectec_ast_decode_derive as decode_derive;
pub use wasm_spec_ast as wasm;

pub mod grammar;
pub mod parse;
pub mod regex;
