//! **SpecTec grammars → byte predicates** — the byte-parsing analogue of the
//! Metamath infrastructure ([`crate::metalogic`]), specialised to the DSL the
//! WebAssembly spec is written in.
//!
//! The north star is *verified* binary-format parsing: take a SpecTec grammar,
//! compile it into a HOL predicate on `bytes`, and prove — inside the kernel —
//! that a concrete bytestring satisfies it. That is the seed for a verified
//! WASM reader: WASM's binary format is a grammar, and "these bytes are a
//! well-formed module" is a `Matches` derivation.
//!
//! This module is the **grammar front end**; the regex engine it sits on top of
//! is the separate, general-purpose [`crate::grammar::regex`] module (regexes are the
//! regular base case of *every* grammar, not just SpecTec, so they live on their
//! own). Here we take a [`grammar::SpecTecSym`], route its regular fragment
//! through `covalence-spectec`'s byte bridge into a [`Regex<u8>`](covalence_grammar::regex::Regex),
//! and hand it to [`crate::grammar::regex`].
//!
//! # The pipeline
//!
//! ```text
//!   SpecTecSym ──sym_to_regex_u8──▶ Regex<u8> ──regex::desugar──▶ Core ──┬─ compile ─▶ ⌜r⌝ : regex u8
//!   (covalence-spectec)            (covalence-grammar)                    │
//!                                                                         └─ tactic ──▶ ⊢ Matches ⌜r⌝ w
//! ```
//!
//! [`compile_sym`] emits the reified term; [`crate::grammar::regex::tactic`] proves a
//! bytestring matches.
//!
//! # Regex is the base case — the CFG stratum comes next
//!
//! A SpecTec grammar is **strictly more than a regex**: regular languages are
//! only its base case. SpecTec symbols include non-terminal *references*
//! ([`grammar::SpecTecSym::Var`]) — one grammar invoking another — which is
//! exactly the step from regular to **context-free**. The byte bridge covers
//! only the regular fragment and returns a typed error on `Var`.
//!
//! The plan is to grow our **own primitive notion of CFG**, one stratum up, the
//! same way [`crate::init::regex`] is our own primitive notion of regular
//! expression: a reified grammar datatype with non-terminals, a `Derives`
//! judgement closed under the productions, and rule induction over derivation
//! trees (the same impredicative-encoding recipe [`crate::init::regex`] /
//! [`crate::init::prop`] use). Then a SpecTec `gram` definition lowers to
//! productions over reified non-terminals, and `Var` becomes a non-terminal
//! symbol rather than a bridge error.
//!
//! [`crate::grammar::regex::tactic::prove_word`] is the **first rung of that ladder**: a
//! variable token carrying a "parses as this category" assumption *is* a
//! non-terminal expansion, and discharging `Matches ⌜cᵢ⌝ Xᵢ` against an
//! assumption is exactly how a CFG derivation will compose sub-derivations.

pub mod cfg;
pub mod grammar;

pub use cfg::{spec_grammar_env, spec_grammar_env_recognition};
pub use grammar::{BridgeError, SpecTecSym, compile_sym, sym_to_core};
