//! **`covalence-haskell`** — a kernel-agnostic surface for a small Haskell
//! dialect, plus a **pluggable lowering** through which different backends
//! realize different subsets of that dialect.
//!
//! This is the on-ramp toward eventually writing `init/` in a Haskell dialect:
//! it commits to no logic and no lowering. It depends on no external crate —
//! the parser is hand-written.
//!
//! # The pieces
//!
//! - [`ast`] — a tiny Haskell expression subset ([`ast::Expr`]/[`ast::Lit`])
//!   plus top-level function definitions ([`ast::Decl`]/[`ast::Module`]).
//! - [`parse`] — a hand-written recursive-descent parser
//!   ([`parse::parse_expr`], [`parse::parse_module`]) with positioned errors.
//!   The module docs list the exact supported grammar.
//! - [`lower`] — the [`lower::Lower`] trait (the centerpiece) and the generic
//!   [`lower::lower`] / [`lower::lower_decl`] drivers.
//! - [`backends`] — demo backends (`SExprLower`, `PeanoLower`, `NoLitLower`)
//!   showing that numeric-literal lowering (and subset coverage) is pluggable.
//!
//! # Example
//!
//! ```
//! use covalence_haskell::{backends::PeanoLower, lower::lower, parse::parse_expr};
//!
//! let e = parse_expr("f 2").unwrap();
//! let mut backend = PeanoLower;
//! assert_eq!(lower(&e, &mut backend).unwrap(), "(f (S (S Z)))");
//! ```
//!
//! The `hol` backend (behind the `hol` feature) lowers this AST into real
//! kernel `Term`s — the carved `sexpr` datatype from `covalence-init` — while
//! the default build stays kernel-agnostic and zero-dep.

#![forbid(unsafe_code)]

pub mod ast;
pub mod backends;
/// The optional HOL backend: lowers the dialect into carved `sexpr` kernel
/// `Term`s. Enabled by the `hol` feature; pulls in `covalence-init`.
#[cfg(feature = "hol")]
pub mod hol;
pub mod lower;
pub mod parse;
pub mod sexpr;
