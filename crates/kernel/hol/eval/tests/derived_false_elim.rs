//! Contract tests for the **derived** ex falso (stage EG3b) and the
//! defined-`T`/`F` ↔ literal bridge.
//!
//! The kernel `FalseElim` primitive was deleted in EG3b: with `F` the
//! ordinary defined constant `defs::fal ≡ ∀p:bool. p`, ex falso is the
//! derivation "unfold + `∀`-elim at the target"
//! ([`DerivedRules::false_elim`]). This suite ports the old
//! `audit_induct.rs` contract block onto the derivation (same shape /
//! side-condition / rejection coverage, restated over the defined `F`),
//! and pins the coexistence bridge (`boolean.rs`): the transitional
//! literal `⌜F⌝` converts through [`fal_from_lit`] / [`fal_eq_lit`],
//! and `⊢ T = ⌜T⌝` through [`tru_eq_lit`].
//!
//! It also pins the EG3b **tier drop**: the ex-falso derivation (and the
//! bootstrap `⊢ T` it sits on) works at the pure `Thm<CoreLang>` tier —
//! no certificate, no computation TCB.

use covalence_core::hol::hol_imp;
use covalence_core::{Term, Type};
use covalence_hol_eval::derived::{DerivedRules, truth};
use covalence_hol_eval::{EvalThm, defs, fal_eq_lit, fal_from_lit, mk_nat, tru_eq_lit};

/// The pure-HOL tier (`covalence_core::Thm` defaults to `Thm<CoreLang>`).
type PureThm = covalence_core::Thm;

fn fal() -> Term {
    defs::fal()
}

// ============================================================================
// false_elim over the defined F — the old kernel-rule contract
// ============================================================================

#[test]
fn false_elim_happy_path_yields_target() {
    let f = EvalThm::assume(fal()).unwrap(); // {F} ⊢ F
    let p = Term::free("p", Type::bool());
    let got = f.false_elim(p.clone()).unwrap();
    assert_eq!(got.concl(), &p, "conclusion is the requested target");
}

#[test]
fn false_elim_propagates_hyps() {
    // {F} ⊢ F → the self-hyp F must survive into the derived theorem.
    let f = EvalThm::assume(fal()).unwrap();
    let got = f.false_elim(Term::free("q", Type::bool())).unwrap();
    let hyps: Vec<_> = got.hyps().iter().cloned().collect();
    assert_eq!(hyps, vec![fal()], "F hyp propagated");
}

#[test]
fn false_elim_target_can_be_any_bool_term() {
    let f = EvalThm::assume(fal()).unwrap();
    // A compound bool target.
    let target = hol_imp(defs::tru(), fal());
    let got = f.false_elim(target.clone()).unwrap();
    assert_eq!(got.concl(), &target);
}

#[test]
fn false_elim_rejects_premise_true() {
    let t = truth::<covalence_hol_eval::CoreEval>().unwrap(); // ⊢ T, not F
    assert!(t.false_elim(Term::free("p", Type::bool())).is_err());
}

#[test]
fn false_elim_accepts_literal_premise_at_eval_tier() {
    // Drop-in compatibility with the deleted kernel rule: a literal-⌜F⌝
    // premise crosses the EG3b bridge automatically AT THE EVAL TIER
    // (`fal_from_lit` is a cert-backed derivation). Hyps propagate.
    let f = EvalThm::assume(Term::bool_lit(false)).unwrap();
    let p = Term::free("p", Type::bool());
    let got = f.false_elim(p.clone()).unwrap();
    assert_eq!(got.concl(), &p);
    let hyps: Vec<_> = got.hyps().iter().cloned().collect();
    assert_eq!(hyps, vec![Term::bool_lit(false)]);
}

#[test]
fn false_elim_rejects_literal_premise_at_pure_tier() {
    // At Thm<CoreLang> the literal carries NO commitments (no cert
    // rules) — the literal premise must be rejected, not bridged.
    let f = PureThm::assume(Term::bool_lit(false)).unwrap();
    assert!(f.false_elim(Term::free("p", Type::bool())).is_err());
}

#[test]
fn false_elim_rejects_premise_arbitrary_prop() {
    // A premise whose conclusion is a free bool var (not F).
    let pp = EvalThm::assume(Term::free("r", Type::bool())).unwrap();
    assert!(pp.false_elim(Term::free("p", Type::bool())).is_err());
}

#[test]
fn false_elim_rejects_non_bool_target() {
    // Target is a nat-typed term → not a proposition.
    let f = EvalThm::assume(fal()).unwrap();
    assert!(f.false_elim(mk_nat(0u32)).is_err(), "nat target rejected");
}

#[test]
fn false_elim_rejects_ill_typed_target() {
    let f = EvalThm::assume(fal()).unwrap();
    let bad = Term::app(defs::tru(), defs::tru()); // bool applied — ill-typed
    assert!(f.false_elim(bad).is_err());
}

// ============================================================================
// The EG3b tier drop: ex falso (and ⊢ T) at the pure CoreLang tier
// ============================================================================

#[test]
fn false_elim_derives_at_pure_tier() {
    // The whole derivation — unfold F, ∀-elim — is pure-HOL: it works at
    // `Thm<CoreLang>` (no cert rule involved).
    let f = PureThm::assume(fal()).unwrap();
    let p = Term::free("p", Type::bool());
    let got = f.false_elim(p.clone()).unwrap();
    assert_eq!(got.concl(), &p);
}

#[test]
fn truth_derives_at_pure_tier_axiom_free() {
    let t = truth::<covalence_core::seam::CoreLang>().unwrap();
    assert!(t.hyps().is_empty());
    assert_eq!(t.concl(), &defs::tru());
}

#[test]
fn connective_calculus_works_at_pure_tier() {
    // A round trip through the derived rules entirely at Thm<CoreLang>:
    // {p, q} ⊢ p ∧ q, project back, discharge, LEM.
    let p = Term::free("p", Type::bool());
    let q = Term::free("q", Type::bool());
    let conj = PureThm::assume(p.clone())
        .unwrap()
        .and_intro(PureThm::assume(q.clone()).unwrap())
        .unwrap();
    assert_eq!(conj.hyps().len(), 2);
    let left = conj.clone().and_elim_l().unwrap();
    assert_eq!(left.concl(), &p);
    let disch = left.imp_intro(&p).unwrap(); // {q} ⊢ p ⟹ p (hyp p discharged)
    let hyps: Vec<_> = disch.hyps().iter().cloned().collect();
    assert_eq!(hyps, vec![q.clone()]);
    let lem = PureThm::lem(p.clone()).unwrap(); // ⊢ p ∨ ¬p — classical, from ε
    assert!(lem.hyps().is_empty());
}

// ============================================================================
// The coexistence bridge (defined T/F vs the transitional literals)
// ============================================================================

#[test]
fn tru_eq_lit_bridge_shape() {
    let eq = tru_eq_lit().unwrap(); // ⊢ T = ⌜T⌝
    assert!(eq.hyps().is_empty());
    let (lhs, rhs) = eq.concl().as_eq().unwrap();
    assert_eq!(lhs, &defs::tru());
    assert_eq!(rhs, &Term::bool_lit(true));
}

#[test]
fn fal_eq_lit_bridge_shape() {
    let eq = fal_eq_lit().unwrap(); // ⊢ F = ⌜F⌝
    assert!(eq.hyps().is_empty());
    let (lhs, rhs) = eq.concl().as_eq().unwrap();
    assert_eq!(lhs, &fal());
    assert_eq!(rhs, &Term::bool_lit(false));
}

#[test]
fn literal_false_premise_crosses_the_bridge() {
    // {⌜F⌝} ⊢ p — the literal ex falso: bridge, then derived false_elim.
    let f_lit = EvalThm::assume(Term::bool_lit(false)).unwrap();
    let f_def = fal_from_lit(f_lit).unwrap(); // {⌜F⌝} ⊢ F
    assert_eq!(f_def.concl(), &fal());
    let hyps: Vec<_> = f_def.hyps().iter().cloned().collect();
    assert_eq!(hyps, vec![Term::bool_lit(false)]);
    let p = Term::free("p", Type::bool());
    let got = f_def.false_elim(p.clone()).unwrap();
    assert_eq!(got.concl(), &p);
    let hyps: Vec<_> = got.hyps().iter().cloned().collect();
    assert_eq!(hyps, vec![Term::bool_lit(false)], "literal hyp propagated");
}

#[test]
fn fal_from_lit_rejects_non_literal_premise() {
    // The defined F is not the literal; the bridge must reject it (use
    // false_elim directly instead).
    let f_def = EvalThm::assume(fal()).unwrap();
    assert!(fal_from_lit(f_def).is_err());
}
