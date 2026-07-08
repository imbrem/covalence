//! **End-to-end HOL-ω prototype** — rank-stratified polymorphic type
//! instantiation driven by the base kind/rank oracle (B-K3).
//!
//! This is the working demonstration that the HOL-ω base machinery composes: a
//! polymorphic type `∀(α:κ:r). τ` is kind-checked and instantiated at a type `σ`
//! *only when the base oracle certifies the side-conditions* — `kindof(σ) = κ` and
//! the **rank stratification** `rankof(σ) ≤ r` (the discipline that blocks
//! impredicative self-instantiation à la Girard). The instantiation itself is
//! untrusted de-Bruijn substitution (`inst_body`); the trust is exactly the three
//! base-minted `CanonRule` certs ([`KindOf`]/[`RankOf`]/[`RankLe`], audited SOUND).
//!
//! **Scope:** this is an UNTRUSTED demo layer (a `#[cfg(test)]` prototype over the
//! demo rep [`TyC`]). Promoting it to a *trusted* `CoreLang` rule (`TyInst`) is the
//! gated next step — it requires the full Homeier-aligned rank-stratification
//! consistency proof (vs `SelectAx`/`bool`) before any higher-rank rule may enter
//! `CORE_MANIFEST` (the `manifest_matches_golden` tripwire). Here we demonstrate the
//! MECHANISM: the middle consumes the base oracle; the rank check genuinely rejects
//! an impredicative instantiation.

use std::any::TypeId;

use crate::eqn::{Error, canon};
use crate::kindcheck::{KindC, KindOf, RankLe, RankOf, TyC};
use crate::lang::{Language, Manifest};

// ---- de-Bruijn substitution (untrusted computation over the demo rep) ----

/// Shift the free de-Bruijn indices `≥ cutoff` of `t` by `d` (TAPL `↑`).
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

/// Substitute `s` for the de-Bruijn variable `j` in `t` (TAPL `[j ↦ s]`, shifting
/// `s` as it crosses binders).
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

/// β-instantiate a `∀`/`λ` body by its argument: remove binder 0 and substitute
/// `arg` for it (`↑⁻¹ ([0 ↦ ↑¹ arg] body)`).
fn inst_body(body: &TyC, arg: &TyC) -> TyC {
    shift(&subst(body, 0, &shift(arg, 1, 0)), -1, 0)
}

// ---- the demo language + the certified instantiation ----

/// Demo language admitting the three kind/rank synthesis rules.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct HoLang;
impl Language for HoLang {
    fn admits(&self, r: TypeId) -> bool {
        r == TypeId::of::<KindOf>() || r == TypeId::of::<RankOf>() || r == TypeId::of::<RankLe>()
    }
    fn extends(&self, p: TypeId) -> bool {
        p == TypeId::of::<()>()
    }
    fn union(self, _: Self) -> Option<Self> {
        Some(HoLang)
    }
    const MANIFEST: Option<&'static Manifest> = None;
}

/// Why an instantiation was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Refused {
    /// The head was not a `∀`.
    NotForall,
    /// `kindof(σ) ≠ κ` (the bound variable's kind).
    KindMismatch { want: KindC, got: KindC },
    /// `rankof(σ) > r` — the stratification rejects this (Girard-blocking).
    RankTooHigh { rank_sigma: u32, bound: u32 },
    /// The oracle refused (ill-kinded σ, etc.).
    Oracle(Error),
}

/// Instantiate `∀(α:κ:r). τ` at `arg = σ`, returning the instantiated type — but
/// ONLY after the base oracle certifies `kindof(σ)=κ` and `rankof(σ)≤r`. The
/// returned certs are the trust; the substitution is untrusted.
fn ty_inst(all: &TyC, arg: &TyC) -> Result<TyC, Refused> {
    let (kappa, r, body) = match all {
        TyC::All(kc, r, body) => (kc.clone(), *r, body.as_ref()),
        _ => return Err(Refused::NotForall),
    };

    // kindof(σ) = κ ?  (base cert)
    let kind_cert = canon(KindOf, arg.clone(), HoLang).map_err(Refused::Oracle)?;
    let got = kind_cert.rhs().0.clone();
    if got != kappa {
        return Err(Refused::KindMismatch { want: kappa, got });
    }

    // rankof(σ) = rσ  (base cert), then rσ ≤ r ?  (base cert — the stratification)
    let rank_cert = canon(RankOf, arg.clone(), HoLang).map_err(Refused::Oracle)?;
    let rank_sigma = rank_cert.rhs().0;
    let le_cert = canon(RankLe, (rank_sigma, r), HoLang).map_err(Refused::Oracle)?;
    if !le_cert.rhs().0 {
        return Err(Refused::RankTooHigh {
            rank_sigma,
            bound: r,
        });
    }

    // Side-conditions certified — perform the (untrusted) substitution.
    Ok(inst_body(body, arg))
}

#[cfg(test)]
mod tests {
    use super::*;

    // ⋆ and ⋆⇒⋆ shorthands.
    fn star() -> KindC {
        KindC::Star
    }
    fn arr() -> KindC {
        KindC::Arrow(Box::new(KindC::Star), Box::new(KindC::Star))
    }

    /// End-to-end: instantiating `∀α:⋆:0. (α ⇒ α)` at a proper type `c : ⋆`
    /// (rank 0) succeeds — kind and rank side-conditions discharged by the base
    /// oracle — and yields `c ⇒ c`.
    #[test]
    fn instantiate_identity_type_at_a_proper_type() {
        // ∀α:⋆:0. (α ⇒ α)
        let all = TyC::All(
            star(),
            0,
            Box::new(TyC::Fn(Box::new(TyC::Bound(0)), Box::new(TyC::Bound(0)))),
        );
        let sigma = TyC::Con(7, star()); // c : ⋆, rank 0

        let out = ty_inst(&all, &sigma).expect("kind ⋆ = ⋆, rank 0 ≤ 0");
        // c ⇒ c
        assert_eq!(
            out,
            TyC::Fn(Box::new(TyC::Con(7, star())), Box::new(TyC::Con(7, star())))
        );
    }

    /// The **rank stratification bites**: instantiating a rank-0 `∀` at a
    /// *polymorphic* type `σ = ∀β:⋆:0.β` (which has rank 1) is REJECTED — the base
    /// `RankLe` cert is `1 ≤ 0 = F`. This is the Girard-blocking discipline working
    /// end-to-end: you cannot impredicatively instantiate at a higher-rank type.
    #[test]
    fn rank_stratification_rejects_impredicative_instantiation() {
        let all = TyC::All(star(), 0, Box::new(TyC::Bound(0))); // ∀α:⋆:0. α
        let sigma = TyC::All(star(), 0, Box::new(TyC::Bound(0))); // ∀β:⋆:0. β  (rank 1)
        assert_eq!(
            ty_inst(&all, &sigma),
            Err(Refused::RankTooHigh {
                rank_sigma: 1,
                bound: 0
            })
        );
    }

    /// Raising the binder's rank to 1 admits the same polymorphic `σ` (rank 1 ≤ 1):
    /// stratification permits predicative instantiation at the higher rank.
    #[test]
    fn higher_rank_binder_admits_the_polymorphic_type() {
        // ∀α:⋆:1. (α ⇒ α)
        let all = TyC::All(
            star(),
            1,
            Box::new(TyC::Fn(Box::new(TyC::Bound(0)), Box::new(TyC::Bound(0)))),
        );
        let sigma = TyC::All(star(), 0, Box::new(TyC::Bound(0))); // rank 1
        let out = ty_inst(&all, &sigma).expect("rank 1 ≤ 1");
        // σ ⇒ σ
        assert_eq!(out, TyC::Fn(Box::new(sigma.clone()), Box::new(sigma)));
    }

    /// A kind mismatch is rejected by the base `KindOf` cert (∀ expects `⋆`, σ has
    /// kind `⋆⇒⋆`).
    #[test]
    fn kind_mismatch_is_rejected() {
        let all = TyC::All(star(), 0, Box::new(TyC::Bound(0)));
        let sigma = TyC::Con(1, arr()); // kind ⋆⇒⋆, not ⋆
        assert_eq!(
            ty_inst(&all, &sigma),
            Err(Refused::KindMismatch {
                want: star(),
                got: arr()
            })
        );
    }

    /// Instantiating a non-`∀` is refused.
    #[test]
    fn non_forall_is_refused() {
        assert_eq!(
            ty_inst(&TyC::Con(0, star()), &TyC::Con(1, star())),
            Err(Refused::NotForall)
        );
    }
}
