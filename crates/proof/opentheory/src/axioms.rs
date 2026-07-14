//! Native proofs of OpenTheory's three HOL **axioms**, so imported articles are
//! checked against covalence's own theory rather than *assuming* them.
//!
//! OpenTheory's `base` rests on three axioms; each is a theorem of covalence's
//! HOL, so each can be discharged:
//!
//! - **infinity** — `∃f:ind→ind. injective f ∧ ¬surjective f`. Mapping
//!   `ind → nat` and taking the witness `f := succ` makes it a theorem: `succ`
//!   is injective ([`Nat::succ_inj`]) and not surjective (`0` is not a
//!   successor, [`Nat::zero_ne_succ`]). [`prove_infinity`].
//! - **extensionality** — `∀f. (λx. f x) = f`, the η axiom. [`prove_extensionality`]
//!   (via [`EvalThm::eta_conv`]).
//! - **choice** — `∀P x. P x ⟹ P (ε P)`, the Hilbert-choice property of `ε`.
//!   [`prove_choice`] (via [`Hol::select_ax`]).
//!
//! Two concerns are kept deliberately separate:
//!
//! - the pure `prove_*` functions — each stated in **SPEC form** (built with
//!   `covalence-hol-api`'s `Hol`/`Nat` builders, so the connectives are
//!   `TermSpec` leaves), knowing nothing about OpenTheory, and working in the
//!   native `covalence_core::Result` so they compose with the kernel rules;
//! - the **transport** to the article's δ-inlined form, delegated to the
//!   reusable [`crate::matching`] framework ([`UpToDelta`]): it δ-unfolds every
//!   connective spec (no β-reduction) on both sides and, if α-equal, carries
//!   `⊢ native` to `⊢ target`.
//!
//! [`standard_axioms`] bundles all three into one [`NativeOverrides`], so
//! `NativeOt::new().with_overrides(standard_axioms())` verifies `base` with
//! **zero** assumptions.
//!
//! [`NativeOverrides`]: crate::native::NativeOverrides

use covalence_core::{Result, Term, defs};
use covalence_hol::types::HolError;
use covalence_hol_api::{Hol, Nat, NativeHol, beta_expand};
use covalence_hol_eval::EvalThm;
use covalence_hol_eval::derived::DerivedRules;

use crate::matching::{UpToDelta, transport_hol};
use crate::native::OverrideMap;

type HolType = <NativeHol as Hol>::Type;

// ===========================================================================
// The pure proof (SPEC form)
// ===========================================================================

/// Prove `⊢ ∃f:nat→nat. injective f ∧ ¬surjective f` in **SPEC form**.
///
/// Built with `Hol`/`Nat` builders, so the connectives (`∃ ∀ ∧ ¬ ⟹ =`)
/// appear as `TermSpec` leaves rather than their Church-encoded λ-bodies.
/// The predicate and conjunct order match OpenTheory's:
///
/// - `injective f = ∀x y. f x = f y ⟹ x = y`   (first conjunct),
/// - `surjective f = ∀y. ∃x. y = f x`, negated  (second conjunct).
///
/// The witness is `succ`: injectivity is [`Nat::succ_inj`], and non-surjectivity
/// follows from [`Nat::zero_ne_succ`] (`0` is not in `succ`'s range).
pub fn prove_infinity() -> Result<EvalThm> {
    let h = NativeHol;
    let nat = h.nat_ty();
    let nn = h.fun_ty(nat.clone(), nat.clone()); // nat → nat

    // The successor function `succ : nat → nat`, as a term.
    let succ_fn = succ_fun(&h);

    // ---- predicate `pred = λf. injective f ∧ ¬surjective f` ---------------
    let f = h.var("f", nn.clone());
    let inj_f = injective_of(&h, &nat, f.clone())?;
    let surj_f = surjective_of(&h, &nat, f)?;
    let not_surj_f = not_of(&h, surj_f)?;
    let body = h.and(inj_f, not_surj_f)?;
    let pred = h.lam("f", nn, body);

    // ---- prove `⊢ pred succ` ---------------------------------------------
    // injective succ: ⊢ ∀x y. succ x = succ y ⟹ x = y  (== succ_inj).
    let inj_succ = h.succ_inj()?;
    // ¬surjective succ, from zero_ne_succ.
    let not_surj_succ = prove_not_surjective_succ(&h, &nat, &succ_fn)?;
    let both = h.and_intro(inj_succ, not_surj_succ)?; // ⊢ injective succ ∧ ¬surjective succ

    // `exists_intro` wants `⊢ pred succ`; β-expand `both` to it.
    let pred_succ = beta_expand(&h, &pred, succ_fn.clone(), both)?;

    // ⊢ ∃f. pred f.
    h.exists_intro(pred, succ_fn, pred_succ)
}

/// Prove `⊢ ∀f:'A→'B. (λx. f x) = f` — OpenTheory's **axiom of
/// extensionality** (the η axiom), via [`EvalThm::eta_conv`].
pub fn prove_extensionality() -> Result<EvalThm> {
    let h = NativeHol;
    let a = h.tvar("A");
    let b = h.tvar("B");
    let fun = h.fun_ty(a.clone(), b); // 'A → 'B
    let f = h.var("f", fun.clone());
    let fx = h.app(f.clone(), h.var("x", a.clone()))?;
    let lam = h.lam("x", a, fx); // λx. f x
    let eta = h.eta_conv(lam)?; // ⊢ (λx. f x) = f
    h.all_intro(eta, "f", fun) // ⊢ ∀f. (λx. f x) = f
}

/// Prove `⊢ ∀P:'A→bool. ∀x. P x ⟹ P (ε P)` — OpenTheory's **axiom of choice**
/// (the defining property of Hilbert's `ε`), via [`Hol::select_ax`].
pub fn prove_choice() -> Result<EvalThm> {
    let h = NativeHol;
    let a = h.tvar("A");
    let pred_ty = h.fun_ty(a.clone(), h.bool_ty()); // 'A → bool
    let p = h.var("P", pred_ty.clone());
    let x = h.var("x", a.clone());
    let ax = h.select_ax(p, x)?; // ⊢ P x ⟹ P (ε P)
    let all_x = h.all_intro(ax, "x", a)?; // ⊢ ∀x. P x ⟹ P (ε P)
    h.all_intro(all_x, "P", pred_ty) // ⊢ ∀P x. …
}

/// The bare successor function `succ : nat → nat` as a term. `Nat::succ`
/// *applies* it, so recover the function from `succ 0`.
fn succ_fun(h: &NativeHol) -> Term {
    let applied = h.succ(h.zero()).expect("succ 0 is well-typed");
    let (succ_fn, _z) = h.dest_app(&applied).expect("succ 0 is an application");
    succ_fn
}

/// `injective f = ∀x y. f x = f y ⟹ x = y`, over element type `nat`.
fn injective_of(h: &NativeHol, nat: &HolType, f: Term) -> Result<Term> {
    let x = h.var("x", nat.clone());
    let y = h.var("y", nat.clone());
    let fx = h.app(f.clone(), x.clone())?;
    let fy = h.app(f, y.clone())?;
    let fx_eq_fy = h.eq(fx, fy)?;
    let x_eq_y = h.eq(x, y)?;
    let imp = h.imp(fx_eq_fy, x_eq_y)?;
    let inner = h.forall("y", nat.clone(), imp)?;
    h.forall("x", nat.clone(), inner)
}

/// `surjective f = ∀y. ∃x. y = f x`, over element type `nat`.
fn surjective_of(h: &NativeHol, nat: &HolType, f: Term) -> Result<Term> {
    let y = h.var("y", nat.clone());
    let x = h.var("x", nat.clone());
    let fx = h.app(f, x)?;
    let y_eq_fx = h.eq(y, fx)?;
    let exists_x = h.exists("x", nat.clone(), y_eq_fx)?;
    h.forall("y", nat.clone(), exists_x)
}

/// `¬p` via the `not` *connective* ([`Hol::not`]) — matching how the article
/// negates `surjective` (`Data.Bool.~`), so the δ-normal forms agree. (Building
/// `imp(p, F)` directly would δ-unfold to a different, `not`-wrapper-free shape.)
fn not_of(h: &NativeHol, p: Term) -> Result<Term> {
    h.not(p)
}

/// `⊢ ¬(surjective succ)` (the `not` connective form).
///
/// Assume `surjective succ = ∀y. ∃x. y = succ x`, specialise at `0` to get
/// `∃x. 0 = succ x`, `exists_elim` to `F` via the step `∀x. (0 = succ x) ⟹ F`
/// (from `zero_ne_succ`), discharge to `⊢ surj ⟹ F`, then `not_intro` to `¬surj`.
fn prove_not_surjective_succ(h: &NativeHol, nat: &HolType, succ_fn: &Term) -> Result<EvalThm> {
    let surj = surjective_of(h, nat, succ_fn.clone())?; // ∀y. ∃x. y = succ x
    let assumed = h.assume(surj.clone())?; // {surj} ⊢ surj
    let zero = h.zero();
    let ex0 = h.all_elim(assumed, zero.clone())?; // {surj} ⊢ ∃x. 0 = succ x

    // `exists_elim` wants a step `⊢ ∀x. pred x ⟹ c` whose antecedent is the
    // existential's predicate *applied* (`(λx. 0 = succ x) x`, a β-redex) — not
    // the β-reduced `0 = succ x`. Recover that predicate from `ex0`.
    let (_ex, pred) = h
        .dest_app(&h.concl(&ex0))
        .expect("∃-conclusion is `exists pred`");
    let step = zero_ne_succ_step(h, nat, &pred, &zero, succ_fn, h.zero_ne_succ()?)?;

    // exists_elim: {surj} ⊢ F; discharge to ⊢ surj ⟹ F, then fold to ⊢ ¬surj
    // (the `not` connective, matching the conjunct built by `not_of`).
    let contradiction = h.exists_elim(ex0, defs::fal(), step)?; // {surj} ⊢ F
    let imp = h.imp_intro(contradiction, &surj)?; // ⊢ surj ⟹ F
    imp.not_intro() // ⊢ ¬surj
}

/// Build the `exists_elim` step `⊢ ∀x. (pred x) ⟹ F` where `pred = λx. 0 = succ
/// x` is the existential's predicate (kept *applied*), discharging `F` from
/// `zero_ne_succ`. We assume the applied `pred x`, β-reduce it to `0 = succ x`,
/// and contradict `⊢ ¬(0 = succ x)` via `not_elim`.
fn zero_ne_succ_step(
    h: &NativeHol,
    nat: &HolType,
    pred: &Term,
    zero: &Term,
    succ_fn: &Term,
    zns: EvalThm,
) -> Result<EvalThm> {
    let x = h.var("x", nat.clone());
    let pred_x = h.app(pred.clone(), x.clone())?; // (λx. 0 = succ x) x
    let assume_px = h.assume(pred_x.clone())?; // {pred x} ⊢ pred x
    let beta = h.beta_conv(pred_x.clone())?; // ⊢ (pred x) = (0 = succ x)
    let eq_thm = h.eq_mp(beta, assume_px)?; // {pred x} ⊢ 0 = succ x
    let _ = (zero, succ_fn); // (the equation is recovered by β above)
    let neg = h.all_elim(zns, x)?; // ⊢ ¬(0 = succ x)
    let f_thm = neg.not_elim(eq_thm)?; // {pred x} ⊢ F
    let imp = h.imp_intro(f_thm, &pred_x)?; // ⊢ (pred x) ⟹ F
    h.all_intro(imp, "x", nat.clone()) // ⊢ ∀x. (pred x) ⟹ F
}

// ===========================================================================
// The override
// ===========================================================================

/// Map a `covalence-core` error into `HolError` at the crate boundary.
fn ce(e: covalence_core::Error) -> HolError {
    HolError::TypeMismatch(e.to_string())
}

/// An [`OverrideMap`] discharging **all three** OpenTheory HOL axioms
/// natively, so `NativeOt::new().with_overrides(standard_axioms())` verifies
/// `base` with **zero** assumptions.
///
/// It maps `ind → nat` (for infinity) and installs one axiom prover per axiom.
/// When an `axiom` fires, each pre-built native proof is δ-matched (via
/// [`UpToDelta`]) against the article's inlined statement; the one that matches
/// discharges it, and anything else stays hypothesis-tracked. Proofs are built
/// once, up front.
pub fn standard_axioms() -> OverrideMap {
    // Build the native proofs once; each incoming axiom just tries to δ-match.
    let proofs: Vec<std::result::Result<EvalThm, String>> =
        [prove_infinity(), prove_extensionality(), prove_choice()]
            .into_iter()
            .map(|r| r.map_err(|e| e.to_string()))
            .collect();
    OverrideMap::new()
        .type_("ind", NativeHol.nat_ty())
        .axiom(move |stmt: &Term| {
            // `flatten` skips any proof that failed to build; an axiom whose
            // proof is missing simply stays hypothesis-tracked.
            for native in proofs.iter().flatten() {
                if let Some(r) = transport_hol(&UpToDelta, native.clone(), stmt) {
                    return Some(r.map_err(ce));
                }
            }
            None // no native proof matches → hypothesis-track as usual
        })
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(all(test, feature = "native"))]
mod tests {
    use std::path::PathBuf;

    use super::*;
    use crate::{FileResolver, NameTable, NativeOt, TheoryCache, check_theory, register_select};

    fn gilith_dirs() -> Vec<PathBuf> {
        let base =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../../assets/opentheory/gilith");
        vec![base.join("std"), base]
    }

    #[test]
    fn all_three_axioms_prove_hypothesis_free() {
        for (name, th) in [
            ("infinity", prove_infinity()),
            ("extensionality", prove_extensionality()),
            ("choice", prove_choice()),
        ] {
            let th = th.unwrap_or_else(|e| panic!("prove_{name}: {e}"));
            assert!(th.hyps().is_empty(), "{name} proof must be hypothesis-free");
        }
    }

    /// Check each `axiom-*` package discharges to 0 assumptions under
    /// [`standard_axioms`].
    fn discharges(package: &str) -> usize {
        let mut kernel = NativeOt::new().with_overrides(standard_axioms());
        let mut names = NameTable::new();
        register_select(&mut kernel, &mut names);
        let resolver = FileResolver::with_dirs(gilith_dirs());
        let mut cache: TheoryCache<NativeOt> = TheoryCache::new();
        check_theory(&mut kernel, &mut names, &resolver, package, &mut cache)
            .unwrap_or_else(|e| panic!("check {package}: {e}"))
            .assumptions
            .len()
    }

    #[test]
    fn axiom_infinity_discharges() {
        assert_eq!(discharges("axiom-infinity"), 0);
    }

    #[test]
    fn axiom_extensionality_discharges() {
        assert_eq!(discharges("axiom-extensionality"), 0);
    }

    #[test]
    fn axiom_choice_discharges() {
        assert_eq!(discharges("axiom-choice"), 0);
    }
}
