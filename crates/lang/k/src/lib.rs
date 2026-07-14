//! **`covalence-k`** — the first slice of the K-framework frontend: an
//! **untrusted, kernel-free driver** that consumes **KORE**, the elaborated
//! matching-logic IR that K's `kompile` emits (`definition.kore`), as the
//! frontend's input surface.
//!
//! ```text
//! textual KORE ==(parse)==> AST ==(one canonical rendering)==> S-expression IR
//!                            |
//!                            +==(classify)==> fragment ladder (rewrite / function / …)
//! ```
//!
//! This is exactly the `covalence-spectec` move replayed for K: just as that
//! crate consumes the **elaborated SpecTec AST** rather than re-implementing a
//! `.watsup` frontend, this crate consumes kompile's elaborated KORE rather
//! than K surface syntax — the K toolchain has already done name mangling,
//! configuration concretization, and rule elaboration for us. Design:
//! `notes/design/k-frontend.md`; working notes: `notes/vibes/k/`.
//!
//! **Trust posture:** this crate is pure untrusted data plumbing. It has *no*
//! kernel dependencies; the lowering of the classified fragments into
//! `covalence-init` (impredicative `Derivable_R` relations, as in the SpecTec
//! frontend) is a later slice. See `SKELETONS.md` for what is deferred.
//!
//! # The pieces
//!
//! - [`ast`] — plain-data KORE: [`ast::Definition`] / [`ast::Module`] /
//!   [`ast::Sentence`] / [`ast::Sort`] / [`ast::Pattern`].
//! - [`parse`] — a hand-written recursive-descent parser
//!   ([`parse::parse_definition`], [`parse::parse_pattern`]) with byte-offset
//!   [`parse::ParseError`]s; handles K's mangled identifiers
//!   (`Lbl'-LT-'k'-GT-`, `'Unds'`, …) and both the binary and the post-2025-01
//!   multiary `\and`/`\or`.
//! - [`sexpr`] — THE canonical, deterministic S-expression rendering of the
//!   AST over [`covalence_sexp`] (`(kore …)` / `(module …)` / `(axiom …)` /
//!   `(\and …)`; grammar in the module docs). `to_sexp` direction only.
//! - [`fragment`] — the fragment classifier ([`fragment::classify`],
//!   [`fragment::rewrite_rules`]): sorts kompiled axioms into
//!   [`fragment::AxiomClass`]es and extracts [`fragment::RewriteRule`]s
//!   (lhs/rhs/requires/ensures/priority/label/unique-id), feeding the
//!   F0 → F1 → F2 → claims consumption ladder documented there.
//!
//! # The `.k`-source frontend ([`kdef`])
//!
//! [`kdef`] is a **separate** frontend over K's *surface* language (`.k`
//! files), consuming the `syntax` (grammar) declarations directly — not KORE.
//! It parses a simple tutorial language's grammar (LAMBDA, IMP) with
//! [`winnow`](covalence_parse::winnow), renders it to an S-expression IR, and
//! lowers it to a [`covalence_grammar::Cfg`] for the kernel CFG stratum.

#![forbid(unsafe_code)]

pub mod ast;
pub mod fragment;
pub mod kdef;
pub mod parse;
pub mod sexpr;
