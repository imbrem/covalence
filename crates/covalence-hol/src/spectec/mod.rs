//! **Grammars → byte predicates, and a matching tactic** — the byte-parsing
//! analogue of the Metamath infrastructure ([`crate::metalogic`]).
//!
//! The north star is *verified* binary-format parsing: compile a grammar (a
//! SpecTec grammar, or any [`covalence_grammar::regex::Regex`]) into a HOL
//! predicate on `bytes`, and prove — inside the kernel — that a concrete
//! bytestring satisfies it. That is the seed for a verified WASM reader: WASM's
//! binary format is a grammar, and "these bytes are a well-formed module" is a
//! `Matches` derivation.
//!
//! # Layout
//!
//! - [`regex`] — the **regular base case**: compile a
//!   [`covalence_grammar::regex::Regex<u8>`] to the reified `regex u8` term and
//!   its byte predicate, plus [`regex::tactic`], the backtracking matcher that
//!   proves `Matches ⌜r⌝ w`. Regexes are used pervasively here, so they get
//!   their own first-class module.
//! - [`grammar`] — the **SpecTec grammar** layer on top: take a
//!   [`grammar::SpecTecSym`] and route its regular fragment through the byte
//!   bridge into [`regex`].
//!
//! # The pipeline
//!
//! ```text
//!   SpecTecSym ──sym_to_regex_u8──▶ Regex<u8> ──desugar──▶ Core ──┬─ core_to_term ─▶ ⌜r⌝ : regex u8
//!   (covalence-spectec)            (covalence-grammar)             │
//!                                                                  └─ derive ───────▶ ⊢ Matches ⌜r⌝ w
//! ```
//!
//! - [`regex::Core`] is the six-constructor regex the reified HOL `regex u8`
//!   datatype ([`crate::init::regex`]) actually has. [`regex::desugar`] folds a
//!   full `Regex<u8>` down to it.
//! - [`regex::compile`] emits the reified regex term; [`regex::predicate`]
//!   emits the language `⟦⌜r⌝⟧ : set (list u8)` — the byte predicate.
//! - [`regex::tactic::prove_matches`] backtracks the seven matching rules to
//!   build `⊢ Matches ⌜r⌝ w`, the word `w` an expression of byte literals,
//!   `cat`, single-byte `cons`, and `nil`. [`regex::tactic::prove_member`]
//!   chains regex *soundness* to land `⊢ mem w ⟦⌜r⌝⟧`.
//!
//! # Regex is the base case — the CFG stratum comes next
//!
//! A SpecTec grammar is **strictly more than a regex**: regular languages are
//! only its base case. SpecTec symbols include non-terminal *references*
//! ([`grammar::SpecTecSym::Var`]) — one grammar invoking another — which is
//! exactly the step from regular to **context-free**. The byte bridge
//! deliberately covers only the regular fragment and returns a typed error on
//! `Var`; the reified target ([`crate::init::regex`]) is likewise a *regular*
//! object logic.
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
//! [`regex::tactic::prove_word`] is the **first rung of that ladder**: a
//! variable token carrying a "parses as this category" assumption *is* a
//! non-terminal expansion, and discharging `Matches ⌜cᵢ⌝ Xᵢ` against an
//! assumption is exactly how a CFG derivation will compose sub-derivations.
//!
//! # Trust
//!
//! Everything here is **untrusted driver code**: the backtracking matcher is a
//! search, and whatever it finds is re-checked by the kernel as it assembles
//! the `Thm` from [`crate::init::regex`]'s rule constructors. A buggy matcher
//! can only fail to find a derivation, never forge one — exactly the Metamath
//! "derive, don't trust" discipline.

pub mod grammar;
pub mod regex;

// Convenience re-exports of the most-reached-for entry points.
pub use grammar::{BridgeError, SpecTecSym, compile_sym, sym_to_core};
pub use regex::{Core, compile, core_to_term, desugar, predicate};
