//! # `HolOmega` — the reflected HOL-ω **type** layer as a consumer trait
//!
//! An EXTENSION trait, companion to [`Hol`](crate::Hol), that exposes the base
//! TCB's reflected HOL-ω machinery — kinds ([`kind`](covalence_pure::kind)),
//! the de-Bruijn type representation ([`tyrep`](covalence_pure::tyrep)), and the
//! kind/rank synthesis oracle ([`kindcheck`](covalence_pure::kindcheck), the
//! `KindOf`/`RankOf`/`RankLe` [`CanonRule`](covalence_pure::CanonRule)s) — as a
//! first-class consumer API. It closes the gap [`Hol`] leaves open: `Hol::tvar`
//! is a single kind-`⋆` carrier (standard HOL has no type-*operator* variables),
//! so a *properly* polymorphic `Monad m` with `m : ⋆ ⇒ ⋆` could not be stated.
//! [`HolOmega`] can: [`tyop_var`](HolOmega::tyop_var) mints a higher-kinded type
//! variable and [`ty_app`](HolOmega::ty_app) applies it (`m a`), and the base
//! oracle kind-checks the result.
//!
//! ## The reflected-vs-trusted-type split (READ THIS)
//!
//! [`HolOmega::TyRep`] is the base's **reflected/demo** flat rep
//! ([`TyC`](covalence_pure::TyC)) — a de-Bruijn, binder-explicit encoding the
//! `CanonRule` oracle evaluates over. It is **deliberately distinct** from
//! [`Hol::Type`], the *trusted kernel* HOL type. This layer proves that
//! type-operator variables and rank-N quantification are expressible and
//! *kind-checkable* through a trait; it does **not** yet bridge a reflected
//! HOL-ω type into a trusted `Hol::Type` term. That bridge (`C = core::Type`
//! wired into the base's App-spine syntax, and the trusted middle `TyInst` rule)
//! is the **gated future step** — it needs the Homeier-aligned rank-stratification
//! consistency proof before any higher-rank rule may enter `CORE_MANIFEST`. See
//! `notes/vibes/tcb-holomega-roadmap.md` and this crate's the generated open-work index.
//!
//! ## Trust — ZERO TCB delta
//!
//! Every checking method delegates to the already-audited base
//! [`canon`](covalence_pure::canon)`(KindOf | RankOf | RankLe)`. This crate
//! declares its own [`Language`](covalence_pure::Language) ([`OmegaLang`]) whose
//! `MANIFEST` is `None` (it is **not** a `CoreLang`/manifest language) — it
//! admits *exactly* those three base rules and mints nothing new. The rank-gated
//! instantiation [`ty_inst`](HolOmega::ty_inst) reuses the
//! `holomega_proto` discipline (Girard-blocking `rankof(σ) ≤ r`); the
//! substitution it performs afterwards is untrusted app-code (it produces a
//! `TyRep`, never a `Thm`). The golden manifests stay byte-identical.

use std::any::TypeId;
use std::hash::{Hash, Hasher};

use covalence_pure::{Error, KindC, KindOf, Language, Manifest, RankLe, RankOf, TyC, canon};

// ============================================================================
// The untrusted consumer language: admits only the three base kind/rank oracle
// rules. `MANIFEST = None` ⇒ this is NOT a golden/CoreLang language; it cannot
// mint a `Thm` of its own, only consume the base certs. (Mirrors the `HoLang`
// in the base's `holomega_proto`, but lives here — untrusted, in the API crate.)
// ============================================================================

/// The consumer language for [`HolOmega`] kind/rank checking: admits exactly the
/// base `KindOf`/`RankOf`/`RankLe` [`CanonRule`](covalence_pure::CanonRule)s and
/// nothing else. `MANIFEST` is `None` — untrusted, not a golden language.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OmegaLang;

impl Language for OmegaLang {
    fn admits(&self, r: TypeId) -> bool {
        r == TypeId::of::<KindOf>() || r == TypeId::of::<RankOf>() || r == TypeId::of::<RankLe>()
    }
    fn extends(&self, p: TypeId) -> bool {
        p == TypeId::of::<()>()
    }
    fn union(self, _: Self) -> Option<Self> {
        Some(OmegaLang)
    }
    const MANIFEST: Option<&'static Manifest> = None;
}

/// Why a [`HolOmega::ty_inst`] was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InstError {
    /// The head was not a `∀` ([`TyC::All`]).
    NotForall,
    /// `kindof(σ) ≠ κ` (the bound variable's declared kind).
    KindMismatch {
        /// The bound variable's kind `κ`.
        want: KindC,
        /// The argument's actual kind `kindof(σ)`.
        got: KindC,
    },
    /// `rankof(σ) > r` — the stratification rejects this (Girard-blocking).
    RankTooHigh {
        /// The argument's rank `rankof(σ)`.
        rank_sigma: u32,
        /// The binder's rank bound `r`.
        bound: u32,
    },
    /// The base oracle refused (e.g. ill-kinded σ).
    Oracle(Error),
}

// ============================================================================
// Untrusted de-Bruijn substitution over the demo rep (produces a `TyRep`, never
// a `Thm`). Same discipline as the base `holomega_proto` (which is `#[cfg(test)]`
// and so not reusable from here); reimplemented untrusted to keep the base TCB
// completely untouched — the manifests are then byte-identical by construction.
// ============================================================================

/// Shift free de-Bruijn indices `≥ cutoff` of `t` by `d` (TAPL `↑`).
fn shift(t: &TyC, d: i64, cutoff: u32) -> TyC {
    match t {
        TyC::Bound(k) => {
            if *k >= cutoff {
                TyC::Bound((*k as i64 + d) as u32)
            } else {
                TyC::Bound(*k)
            }
        }
        TyC::Con(id, kc) => TyC::Con(*id, kc.clone()),
        TyC::Fn(a, b) => TyC::Fn(Box::new(shift(a, d, cutoff)), Box::new(shift(b, d, cutoff))),
        TyC::App(f, x) => TyC::App(Box::new(shift(f, d, cutoff)), Box::new(shift(x, d, cutoff))),
        TyC::All(kc, r, body) => TyC::All(kc.clone(), *r, Box::new(shift(body, d, cutoff + 1))),
        TyC::Abs(kc, r, body) => TyC::Abs(kc.clone(), *r, Box::new(shift(body, d, cutoff + 1))),
    }
}

/// Substitute `s` for the de-Bruijn variable `j` in `t` (TAPL `[j ↦ s]`).
fn subst(t: &TyC, j: u32, s: &TyC) -> TyC {
    match t {
        TyC::Bound(k) => {
            if *k == j {
                s.clone()
            } else {
                TyC::Bound(*k)
            }
        }
        TyC::Con(id, kc) => TyC::Con(*id, kc.clone()),
        TyC::Fn(a, b) => TyC::Fn(Box::new(subst(a, j, s)), Box::new(subst(b, j, s))),
        TyC::App(f, x) => TyC::App(Box::new(subst(f, j, s)), Box::new(subst(x, j, s))),
        TyC::All(kc, r, body) => TyC::All(
            kc.clone(),
            *r,
            Box::new(subst(body, j + 1, &shift(s, 1, 0))),
        ),
        TyC::Abs(kc, r, body) => TyC::Abs(
            kc.clone(),
            *r,
            Box::new(subst(body, j + 1, &shift(s, 1, 0))),
        ),
    }
}

/// β-instantiate a `∀`/`λ` body by its argument (`↑⁻¹ ([0 ↦ ↑¹ arg] body)`).
fn inst_body(body: &TyC, arg: &TyC) -> TyC {
    shift(&subst(body, 0, &shift(arg, 1, 0)), -1, 0)
}

/// Stable tag for a *named* free type variable. The flat demo rep [`TyC`] has no
/// named free tyvar — only [`TyC::Con`]`(id, κ)`, a constant tagged by a `u32`
/// id and carrying its declared kind. A free tyvar `name : κ` is reflected as a
/// distinctly-tagged constant of that kind: equal names ⇒ equal tag ⇒ equal
/// reflected type; distinct names ⇒ (almost surely) distinct tags. Kind checking
/// only reads the carried `κ`, so this faithfully models a free variable of a
/// given kind for the purpose of kind/rank synthesis.
fn name_tag(name: &str) -> u32 {
    let mut h = std::collections::hash_map::DefaultHasher::new();
    name.hash(&mut h);
    // Fold to u32; collisions are a naming clash (two distinct names sharing a
    // reflected constant), never a soundness issue — the oracle is untrusted here.
    (h.finish() as u32) ^ ((h.finish() >> 32) as u32)
}

// ============================================================================
// The trait.
// ============================================================================

/// The reflected HOL-ω **type** layer, exposed as a consumer trait companion to
/// [`Hol`](crate::Hol). Builds reflected kinds and types (including
/// **type-operator variables**, `m : ⋆ ⇒ ⋆`), and kind/rank-checks them via the
/// base oracle. See the module docs for the reflected-vs-trusted split and the
/// zero-TCB trust story.
pub trait HolOmega {
    /// A reflected HOL-ω **type** (the flat de-Bruijn demo rep, [`TyC`]).
    type TyRep: Clone + PartialEq + std::fmt::Debug;
    /// A reflected HOL-ω **kind** `κ ::= ⋆ | κ ⇒ κ` ([`KindC`]).
    type Kind: Clone + PartialEq + std::fmt::Debug;

    // -- Kind builders --

    /// The base kind `⋆` of proper types.
    fn star(&self) -> Self::Kind;
    /// The function kind `κ₁ ⇒ κ₂` of a type operator.
    fn arrow(&self, k1: Self::Kind, k2: Self::Kind) -> Self::Kind;

    // -- Type builders --

    /// A **higher-kinded type variable** `name : κ` — e.g. a monad's carrier
    /// operator `m : ⋆ ⇒ ⋆`. This is the gap over [`Hol::tvar`](crate::Hol),
    /// which only offers a kind-`⋆` variable.
    fn tyop_var(&self, name: &str, kind: Self::Kind) -> Self::TyRep;
    /// A kind-`⋆` type variable `name : ⋆` (the ordinary HOL polymorphic tyvar).
    fn ty_var(&self, name: &str) -> Self::TyRep;
    /// A type constant `name : κ`, tagged distinctly by name and carrying its
    /// declared kind (like [`tyop_var`](HolOmega::tyop_var) — the demo rep does
    /// not distinguish a declared constant from a free variable).
    fn ty_con(&self, name: &str, kind: Self::Kind) -> Self::TyRep;
    /// **Type-operator application** `op arg` (e.g. `m a`). Kind-checks only
    /// under [`kind_of`](HolOmega::kind_of): building the spine is inert.
    fn ty_app(&self, op: Self::TyRep, arg: Self::TyRep) -> Self::TyRep;
    /// The function type `a ⇒ b` (both sides must be `⋆` to kind-check).
    fn ty_fun(&self, a: Self::TyRep, b: Self::TyRep) -> Self::TyRep;
    /// The **rank-N universal** `∀(α : κ : rank). body`, binding the innermost
    /// de-Bruijn tyvar. `body` refers to the bound variable via
    /// [`bound`](HolOmega::bound)`(0)`.
    fn ty_all(&self, kind: Self::Kind, rank: u32, body: Self::TyRep) -> Self::TyRep;
    /// **Type-level abstraction** `λ(α : κ : rank). body` (a type operator).
    fn ty_abs(&self, kind: Self::Kind, rank: u32, body: Self::TyRep) -> Self::TyRep;
    /// The de-Bruijn bound tyvar at index `i` (0 = innermost binder), for use in
    /// [`ty_all`](HolOmega::ty_all)/[`ty_abs`](HolOmega::ty_abs) bodies.
    fn bound(&self, i: u32) -> Self::TyRep;

    // -- Kind / rank checking (delegates to the base oracle) --

    /// The kind of `ty` via the base `KindOf` cert — `Some(κ)` iff `ty` is
    /// well-kinded, else `None` (never a *wrong* kind).
    fn kind_of(&self, ty: &Self::TyRep) -> Option<Self::Kind>;
    /// The rank of a **well-kinded** `ty` via the base `RankOf` cert (`None` on
    /// ill-kinded input). `rank(∀α:κ:r.τ) = max(r+1, rank τ)`.
    fn rank_of(&self, ty: &Self::TyRep) -> Option<u32>;
    /// Whether `ty` is well-kinded (i.e. [`kind_of`](HolOmega::kind_of) is `Some`).
    fn well_kinded(&self, ty: &Self::TyRep) -> bool {
        self.kind_of(ty).is_some()
    }
    /// Decide `a ≤ b` via the base `RankLe` cert.
    fn rank_le(&self, a: u32, b: u32) -> bool;

    // -- Rank-stratified instantiation (the Girard-blocking gate) --

    /// Instantiate `∀(α:κ:r). τ` at `arg = σ`, returning the instantiated type —
    /// but ONLY after the base oracle certifies `kindof(σ) = κ` **and**
    /// `rankof(σ) ≤ r` (the rank stratification that blocks impredicative
    /// self-instantiation à la Girard). The subsequent substitution is untrusted.
    fn ty_inst(&self, all: &Self::TyRep, arg: &Self::TyRep) -> Result<Self::TyRep, InstError>;
}

// ============================================================================
// The native backend — delegates every check to the base `canon(..)` certs.
// ============================================================================

/// The native [`HolOmega`] backend: [`TyRep`](HolOmega::TyRep) = the base's flat
/// demo rep [`TyC`], [`Kind`](HolOmega::Kind) = [`KindC`]; all kind/rank checking
/// goes through [`canon`](covalence_pure::canon)`(KindOf | RankOf | RankLe)` in
/// the untrusted [`OmegaLang`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct NativeHolOmega;

impl HolOmega for NativeHolOmega {
    type TyRep = TyC;
    type Kind = KindC;

    fn star(&self) -> KindC {
        KindC::Star
    }
    fn arrow(&self, k1: KindC, k2: KindC) -> KindC {
        KindC::Arrow(Box::new(k1), Box::new(k2))
    }

    fn tyop_var(&self, name: &str, kind: KindC) -> TyC {
        TyC::Con(name_tag(name), kind)
    }
    fn ty_var(&self, name: &str) -> TyC {
        TyC::Con(name_tag(name), KindC::Star)
    }
    fn ty_con(&self, name: &str, kind: KindC) -> TyC {
        TyC::Con(name_tag(name), kind)
    }
    fn ty_app(&self, op: TyC, arg: TyC) -> TyC {
        TyC::App(Box::new(op), Box::new(arg))
    }
    fn ty_fun(&self, a: TyC, b: TyC) -> TyC {
        TyC::Fn(Box::new(a), Box::new(b))
    }
    fn ty_all(&self, kind: KindC, rank: u32, body: TyC) -> TyC {
        TyC::All(kind, rank, Box::new(body))
    }
    fn ty_abs(&self, kind: KindC, rank: u32, body: TyC) -> TyC {
        TyC::Abs(kind, rank, Box::new(body))
    }
    fn bound(&self, i: u32) -> TyC {
        TyC::Bound(i)
    }

    fn kind_of(&self, ty: &TyC) -> Option<KindC> {
        // The base `KindOf` cert: `⊢ kindof(ty) = κ`. `NoMatch` ⇒ ill-kinded.
        canon(KindOf, ty.clone(), OmegaLang)
            .ok()
            .map(|cert| cert.rhs().0.clone())
    }
    fn rank_of(&self, ty: &TyC) -> Option<u32> {
        canon(RankOf, ty.clone(), OmegaLang)
            .ok()
            .map(|cert| cert.rhs().0)
    }
    fn rank_le(&self, a: u32, b: u32) -> bool {
        // Total: `canon(RankLe, ..)` never `NoMatch`s.
        canon(RankLe, (a, b), OmegaLang)
            .map(|cert| cert.rhs().0)
            .unwrap_or(false)
    }

    fn ty_inst(&self, all: &TyC, arg: &TyC) -> Result<TyC, InstError> {
        let (kappa, r, body) = match all {
            TyC::All(kc, r, body) => (kc.clone(), *r, body.as_ref()),
            _ => return Err(InstError::NotForall),
        };

        // kindof(σ) = κ ?  (base cert)
        let got = canon(KindOf, arg.clone(), OmegaLang)
            .map_err(InstError::Oracle)?
            .rhs()
            .0
            .clone();
        if got != kappa {
            return Err(InstError::KindMismatch { want: kappa, got });
        }

        // rankof(σ) = rσ  (base cert), then rσ ≤ r ?  (base cert — the stratification)
        let rank_sigma = canon(RankOf, arg.clone(), OmegaLang)
            .map_err(InstError::Oracle)?
            .rhs()
            .0;
        if !self.rank_le(rank_sigma, r) {
            return Err(InstError::RankTooHigh {
                rank_sigma,
                bound: r,
            });
        }

        // Side-conditions certified — perform the (untrusted) substitution.
        Ok(inst_body(body, arg))
    }
}
