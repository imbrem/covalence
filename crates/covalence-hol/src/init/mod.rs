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
//! plus the per-theory theorem catalogues — [`cond`] (the boolean
//! conditional's reduction clauses), [`nat`], [`int`], [`coprod`],
//! [`option`], [`prod`] (the pair projections, surjective pairing, and
//! injectivity), [`list`] (the `nil`-side element computations),
//! [`stream`], [`recursion`], [`rel`], and [`set`].
//!
//! Efficiency is explicitly *not* a goal: `init` runs once at startup.
//! The point is for the rest of `covalence-hol` to depend on this
//! stable surface; once `covalence-core` is settled, faster paths can
//! land behind the same API.

/// Define a nullary `-> Thm` function whose proof is built **once** and
/// cached in a `LazyLock`. The `init` proofs run at startup and many are
/// sizeable (inductions, the recursion theorem), so recomputing one per
/// call is pure waste. Doc comments and visibility pass through.
///
/// Two body forms are accepted:
///
/// ```ignore
/// cached_thm! {
///     /// `⊢ T` — build a `Thm` directly.
///     pub fn truth() -> Thm { /* build it */ }
/// }
/// cached_thm! {
///     /// `⊢ ∀m. 0 + m = m` — a fallible derivation. The `Result<Thm>`
///     /// body may use `?`; the macro `.expect`s it, so a separate
///     /// `*_impl` wrapper is no longer needed.
///     pub fn add_base() -> Result<Thm> { /* build it, may use `?` */ }
/// }
/// ```
macro_rules! cached_thm {
    ($(#[$attr:meta])* $vis:vis fn $name:ident() -> Thm $body:block) => {
        $(#[$attr])*
        $vis fn $name() -> ::covalence_core::Thm {
            static CACHE: ::std::sync::LazyLock<::covalence_core::Thm> =
                ::std::sync::LazyLock::new(|| $body);
            CACHE.clone()
        }
    };
    ($(#[$attr:meta])* $vis:vis fn $name:ident() -> Result<Thm> $body:block) => {
        $(#[$attr])*
        $vis fn $name() -> ::covalence_core::Thm {
            static CACHE: ::std::sync::LazyLock<::covalence_core::Thm> =
                ::std::sync::LazyLock::new(|| {
                    (|| -> ::covalence_core::Result<::covalence_core::Thm> { $body })()
                        .expect(concat!("init: ", stringify!($name), " derivation"))
                });
            CACHE.clone()
        }
    };
}

pub mod cat;
pub mod cond;
pub mod coprod;
pub mod eq;
pub mod ext;
pub mod inductive;
pub mod int;
pub mod list;
pub mod logic;
pub mod nat;
pub mod option;
pub mod prod;
pub mod quotient;
pub mod recursion;
pub mod rel;
pub mod set;
pub mod stream;

/// The full `covalence-core` definition catalogue (types, term
/// constructors, the `TypeSpec` / `TermSpec` handles, `Canonical`, …).
pub use covalence_core::defs::*;

pub use ext::{TermExt, ThmExt};
pub use logic::truth;
