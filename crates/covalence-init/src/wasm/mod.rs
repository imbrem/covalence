//! **WebAssembly-spec front end** — lower [SpecTec] (the DSL the WebAssembly
//! specification is written in) into kernel objects, the "construct, don't
//! trust" way, with the long-term goal of *WASM acceleration*: run a real WASM
//! engine as an untrusted oracle and certify its trace against the spec's own
//! reduction relation.
//!
//! The **input is SpecTec AST S-expressions** — the textual AST the upstream
//! OCaml SpecTec compiler emits, parsed by [`covalence_spectec::parse`] /
//! [`covalence_spectec::ast::parse_spectec_stream`] into a `Vec<SpecTecDef>`.
//! There is no `.watsup` frontend here (and none is planned): we consume the
//! elaborated AST directly. `covalence-spectec` is an **untrusted driver**;
//! nothing in this module grows the TCB.
//!
//! ## How SpecTec maps onto the kernel
//!
//! SpecTec and Metamath ([`crate::metalogic`]) are dual: Metamath ships *proofs
//! to replay*, SpecTec ships *a specification to define*. So this module reuses
//! the same impredicative rule-induction substrate ([`crate::metalogic`]) — not
//! for replay, but to turn each SpecTec inductive relation into a `Derivable_R`
//! predicate:
//!
//! | `SpecTecDef` | WASM spec role | lowers to | via |
//! |---|---|---|---|
//! | `Rel` / `Rule` | judgements (`⊢ instr : ft`, `↪` reduction) | `Derivable_R` predicate, one clause per rule | [`relation`] over [`crate::metalogic`] |
//! | `Typ` | syntax (`valtype`, `instr`, …) | reified inductive datatype | `crate::init` engine *(todo)* |
//! | `Dec` (functions) | metafunctions | recursive `define` + computation rules | *(todo)* |
//! | `Gram` | binary/text format | byte-predicate / CFG recognizer | [`crate::grammar::spectec`] *(CFG stratum todo)* |
//!
//! ## What exists now (phase 1)
//!
//! - [`encode`] — the reified-syntax encoder: a SpecTec `SpecTecExp` → a term
//!   over the uninterpreted free term algebra `Φ = nat` (the shared foundation).
//! - [`relation`] — a `SpecTecDef::Rel` → a [`crate::metalogic::RuleSet`], with a
//!   [`relation::derive`] constructor that builds `⊢ Derivable_R ⌜J⌝` witnesses.
//!
//! See `notes/vibes/wasm-spec.md` for the phasing (syntax/functions, the CFG stratum,
//! trace certification, and the mirror-principle commutative-diagram check) and
//! `SKELETONS.md` for the open increments.
//!
//! [SpecTec]: https://github.com/Wasm-DSL/spectec

pub mod denote;
pub mod encode;
pub mod relation;
pub mod spec;
pub mod syntax;
