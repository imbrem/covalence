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
//! conditional's reduction clauses), [`nat`], [`int`], [`rat`], [`real`],
//! [`coprod`], [`option`], [`prod`] (the pair projections, surjective
//! pairing, and injectivity), [`list`] (the `nil`-side element
//! computations), [`stream`], [`recursion`], [`rel`], and [`set`].
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
pub mod monoid;
pub mod nat;
pub mod option;
pub mod prod;
pub mod prop;
pub mod quotient;
pub mod rat;
pub mod real;
pub mod recursion;
pub mod rel;
pub mod set;
pub mod sexpr;
pub mod sexp;
pub mod stream;
pub mod tree;

/// The full `covalence-core` definition catalogue (types, term
/// constructors, the `TypeSpec` / `TermSpec` handles, `Canonical`, …).
pub use covalence_core::defs::*;

pub use ext::{TermExt, ThmExt};
pub use logic::truth;

// ============================================================================
// Standard-library prelude for `.cov` proof scripts
// ============================================================================

use std::sync::Arc;

use crate::script::{Env, NamedThm, ScriptError, Tactic};

/// Resolve a standard-library theory environment by name — the `resolver`
/// argument to [`crate::script::run`]. Knows the public catalogue of ported
/// theories that a `.cov` proof may `(#import …)`:
///
/// - `core` — the kernel prelude (the logical primitives + rule registry)
/// - `logic` — propositional connectives + their proved properties
/// - `nat` — Peano arithmetic theorems
/// - `set` — set algebra / order theorems
///
/// Each environment is built — and its theorems proved — lazily, only when a
/// script actually imports it.
pub fn library_env(name: &str) -> Option<Env> {
    match name {
        "core" => Some(Env::core()),
        "logic" => Some(logic::cov::env()),
        "nat" => Some(nat::cov::env()),
        "set" => Some(set::cov::env()),
        _ => None,
    }
}

/// Resolve a standard-library FFI tactic by name — the `tactics` argument to
/// [`crate::script::run`]. Currently provides `tauto`, the propositional
/// decision procedure used by the `logic` theory.
pub fn library_tactic(name: &str) -> Option<Arc<dyn Tactic>> {
    match name {
        "tauto" => Some(Arc::new(logic::Tauto)),
        _ => None,
    }
}

/// Parse and check a `.cov` proof script against the standard-library prelude
/// ([`library_env`] / [`library_tactic`]), returning the theorems it proves.
///
/// This is the entry point a host (e.g. the REPL) uses to verify a
/// user-authored proof: nothing in the text is trusted — every theorem is
/// re-derived by the kernel.
pub fn check_script(src: &str) -> Result<Vec<NamedThm>, ScriptError> {
    // Build each imported standard-library theory up front, on *this* thread.
    // A `cov_theory!` env's `LazyLock` drives its own proof through
    // `crate::script::run` → `block_on`, which panics if forced from inside
    // another runtime — and the proof resolver runs inside exactly such a
    // runtime. The REPL/host calls `check_script` from outside any runtime, so
    // priming here means the resolver only ever clones an already-built env.
    //
    // This is portable (no OS threads — browser WASM has none) but a
    // stop-gap: once `script::block_on` becomes a nestable synchronous
    // executor (`futures::executor::block_on`), forcing nests safely and this
    // pre-pass can go.
    prime_library_imports(src);
    Ok(crate::script::run(src, library_env, library_tactic)?.thms)
}

/// Eagerly build every standard-library theory the script `(#import …)`s, so it
/// is cached before the proof runtime starts (see [`check_script`]). Scanning
/// the top-level `(#import NAME)` forms matches exactly the set of names the
/// resolver will be asked for. Best-effort: a malformed source is left for
/// [`crate::script::run`] to report.
fn prime_library_imports(src: &str) {
    let Ok(forms) = covalence_sexp::parse(src) else {
        return;
    };
    for form in &forms {
        if let Some(items) = form.as_list()
            && items.first().and_then(|s| s.as_symbol()) == Some("#import")
            && let Some(name) = items.get(1).and_then(|s| s.as_symbol())
        {
            // `core` needs no priming; the `cov_theory!` envs do.
            let _ = library_env(name);
        }
    }
}
