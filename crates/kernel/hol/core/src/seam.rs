//! The **core-on-pure seam** — ONE module to audit (everything here is a
//! re-export; nothing new is defined).
//!
//! `covalence-core`'s [`Thm`](crate::Thm) is a newtype over
//! `pure::Thm<L, IsThm(Γ, φ)>` at a [`HolTier`] `L` (default [`CoreLang`]).
//! This module makes that seam usable by the downstream tier crate
//! (`covalence-hol-eval`, which owns the `CoreEval` tier and hosts the
//! computation-certificate rules) and by untrusted drivers:
//!
//! - [`CoreLang`] / [`IsThm`] / [`CoreProp`] / [`IsThmProp`] / [`HolTier`] —
//!   the pure-HOL tier language, the judgement op, the concrete
//!   sequent-proposition shape, its **conclusion-operand-generic** form
//!   ([`IsThmProp<C>`] — the literal-endgame mechanism, so a downstream tier
//!   can name the type of a symbolic-conclusion certificate it lands via
//!   [`Thm::from_pure_sym`](crate::Thm::from_pure_sym)), and the tier marker
//!   trait. Publishing them mints nothing: every mint is gated on the minting
//!   language's `admits`, and `pure::Thm` remains unforgeable.
//! - [`CORE_MANIFEST`] / [`core_admits`] — the static TCB manifest of the
//!   pure-HOL tier and its admits predicate, so a downstream tier that
//!   `extends` [`CoreLang`] can embed the manifest as its parent and
//!   delegate its inherited-rule gate. Reading them mints nothing; a tier
//!   admitting these rules mints *only* what the sound rule catalogue
//!   derives.
//! - [`Lit`] — the native-value ↔ literal-leaf currency (TRANSITIONAL,
//!   dies with the kernel literal leaves; see `thm/lit.rs`).
//! - The landing constructor is [`Thm::from_pure`](crate::Thm::from_pure)
//!   (re-checks the sequent floor), and the tier coercion is
//!   [`Thm::lift`](crate::Thm::lift).
//!
//! The other half of the seam is `CoreLang`'s `extends` opening to
//! [`covalence_pure_eval::Builtins`] (see `thm::lang`): canon-minted
//! `Thm<Builtins, _>` facts lift into `CoreLang` via
//! [`covalence_pure::Thm::lift`]. Both halves ship under maintainer review —
//! they change the TCB shape (`docs/deps/tcb.json`).
//!
//! (The toHOL vocabulary and the per-family computation certificates that
//! used to be re-exported here moved to `covalence-hol-eval` — they are
//! `Rule<CoreEval>`s of the eval tier now, so `Thm<CoreLang>` carries no
//! computation TCB.)

pub use crate::thm::lang::{CoreLang, CoreProp, HolTier, IsThm, IsThmProp};
pub use crate::thm::lit::Lit;
pub use crate::thm::rules::{CORE_MANIFEST, core_admits};
