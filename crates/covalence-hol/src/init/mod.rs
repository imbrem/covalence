//! `init` — the high-level, run-once bootstrap layer.
//!
//! This module re-exports the whole `covalence_core::defs` catalogue
//! (the type / term definitions) and pairs it with the **proofs** the
//! kernel deliberately omits — the connective properties, the equality
//! / rewriting toolkit — expressed through a deliberately high-level
//! API so that churn in `covalence-core` is absorbed *here* rather than
//! scattered across the rest of the shell.
//!
//! The pieces:
//!
//! - [`ext`] — the [`TermExt`] / [`ThmExt`] extension traits: the
//!   insulation layer of convenience constructors and derived proof
//!   steps over the kernel's `Term` / `Thm`.
//! - [`logic`] — the connectives re-exported, plus their proved
//!   properties ([`truth`], commutativity, …) and the classical clause /
//!   simplification procedures ([`logic::resolve`], [`logic::simp`], …).
//! - [`eq`] — equality reasoning and the canonical rewriting
//!   conversion ([`eq::rewrite`]) that proof code should use everywhere.
//! - [`nat`] / [`int`] — the arithmetic catalogues re-exported, paired
//!   with their Peano / ordered-ring theorems (some proved, some
//!   postulated pending the downstream derivations; see each module).
//! - [`set`] — the `TypeSpec`-backed set membership / extensionality API.
//!
//! Efficiency is explicitly *not* a goal: `init` runs once at startup.
//! The point is for the rest of `covalence-hol` to depend on this
//! stable surface; once `covalence-core` is settled, faster paths can
//! land behind the same API.

pub mod eq;
pub mod ext;
pub mod int;
pub mod logic;
pub mod nat;
pub mod set;

/// The full `covalence-core` definition catalogue (types, term
/// constructors, the `TypeSpec` / `TermSpec` handles, `Canonical`, …).
pub use covalence_core::defs::*;

pub use ext::{TermExt, ThmExt};
pub use logic::truth;
