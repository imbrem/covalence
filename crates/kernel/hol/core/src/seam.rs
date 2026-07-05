//! The **core-on-pure seam**, deliberately widened for the toHOL tier — ONE
//! module to audit (everything here is a re-export; nothing new is defined).
//!
//! `covalence-core`'s [`Thm`](crate::Thm) is a newtype over
//! `pure::Thm<CoreLang, IsThm(Γ, φ)>`. This module makes that seam usable by
//! *untrusted* drivers (the reify drivers headed to `covalence-hol-eval`):
//!
//! - [`CoreLang`] / [`IsThm`] / [`CoreProp`] — the admitting language, the
//!   judgement op, and the concrete sequent-proposition shape. Publishing
//!   them mints nothing: every mint is gated on `CoreLang::admits`, and
//!   `pure::Thm` remains unforgeable.
//! - The toHOL vocabulary ([`ToHolNat`] / [`ToHolInt`] / [`ToHolBytes`] /
//!   [`HolApp`] and the slice's expression aliases) — uninterpreted ops plus
//!   the admitted `HolApp` evaluation.
//! - The admitted toHOL rules ([`ToHolNatVal`] / [`PairVal`] /
//!   [`NatAddCert`]) — appliable from outside via [`covalence_pure::apply`]
//!   (still gated on their `TypeId`s being admitted).
//! - The landing constructor is [`Thm::from_pure`](crate::Thm::from_pure).
//!
//! The other half of the seam is `CoreLang`'s `extends` opening to
//! [`covalence_pure_eval::Builtins`] (see `thm::lang`): canon-minted
//! `Thm<Builtins, _>` facts lift into `CoreLang` via
//! [`covalence_pure::Thm::lift`]. Both halves ship under maintainer review —
//! they change the TCB shape (`docs/deps/tcb.json` gains
//! `covalence-pure-eval`).

pub use crate::thm::lang::{CoreLang, CoreProp, IsThm};
pub use crate::thm::rules::{NatAddCert, PairVal, ToHolNatVal};
pub use crate::tohol::{
    HolApp, HolAppE, NatAddEqE, NatAddLhsE, ToHolBytes, ToHolInt, ToHolNat, ToHolNatE,
};
