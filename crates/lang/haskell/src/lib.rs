//! **`covalence-haskell`** — a kernel-agnostic surface for a small Haskell
//! dialect, organized around an **S-expression interchange IR**:
//!
//! ```text
//! Haskell dialect ==(one canonical lowering)==> S-expressions ==(pluggable)==> backend
//! ```
//!
//! Third-party producers and consumers use the S-expression layer directly —
//! text in via [`sexpr::parse_sexpr`], canonical text out via
//! [`sexpr::SExpr::to_text`] — without ever touching Haskell syntax; the
//! Haskell front end is just one producer of the IR. This is the on-ramp
//! toward eventually writing `init/` in a Haskell dialect (see
//! `tests/init_dialect.rs` for the flagship demo module).
//!
//! # The pieces
//!
//! - [`ast`] — a tiny Haskell expression subset ([`ast::Expr`]/[`ast::Lit`])
//!   plus top-level function definitions ([`ast::Decl`]/[`ast::Module`]) and a
//!   minimal **type surface** ([`ast::Ty`]: type variables, base/applied
//!   constructors, function arrows) carried by signatures and annotated lambda
//!   binders — the input a *typed* backend consumes (there is no inference).
//!   **A Haskell `Nat` literal is a covalence `Nat`** (arbitrary precision,
//!   from `covalence-types`), never a machine integer.
//! - [`parse`] — a hand-written recursive-descent parser
//!   ([`parse::parse_expr`], [`parse::parse_module`], [`parse::parse_ty`]) with
//!   positioned errors. The module docs list the exact supported grammar.
//! - [`sexpr`] — the interchange IR ([`sexpr::SExpr`]: symbol / nat / string
//!   atoms + lists) with a canonical text printer and a text parser
//!   (grammar in the module docs).
//! - [`lower`] — THE canonical Haskell ⇒ SExpr lowering (the fixed
//!   desugaring: `\x -> b` ⇝ `(lambda x b)`, `let n = v in b` ⇝
//!   `(let n v b)`, `l + r` ⇝ `(+ l r)`, decls ⇝ nested lambdas /
//!   `(define …)` forms) — the only consumer of Haskell syntax — plus the
//!   [`lower::lower`] / [`lower::lower_decl`] whole-pipeline drivers.
//! - [`realize`] — the pluggable [`realize::Realize`] seam (the centerpiece):
//!   backends interpret the IR, overriding only the subset they realize
//!   (most visibly how a natural-number atom is realised).
//! - [`backends`] — demo backends (`TextBackend`, `PeanoBackend`,
//!   `NoLitBackend`, `DesugarBackend`) showing that numeric-atom realization,
//!   subset coverage, and structural rewriting are all pluggable.
//!
//! # Example
//!
//! ```
//! use covalence_haskell::{backends::PeanoBackend, lower::lower, parse::parse_expr};
//!
//! // Haskell ⇒ SExpr ⇒ backend: Peano realizes nat atoms as (S … Z).
//! let e = parse_expr("f 2").unwrap();
//! let out = lower(&e, &mut PeanoBackend).unwrap();
//! assert_eq!(out.to_text(), "(f (S (S Z)))");
//! ```
//!
//! The `hol` backend (behind the `hol` feature) realizes the IR into real
//! kernel `Term`s — the carved `sexpr` datatype from `covalence-init` — while
//! the default build stays kernel-agnostic (`covalence-types` is
//! kernel-independent).

#![forbid(unsafe_code)]

pub mod ast;
pub mod backends;
/// The optional HOL backend: realizes the IR into carved `sexpr` kernel
/// `Term`s. Enabled by the `hol` feature; pulls in `covalence-init`.
#[cfg(feature = "hol")]
pub mod hol;
pub mod lower;
pub mod parse;
pub mod realize;
pub mod sexpr;
