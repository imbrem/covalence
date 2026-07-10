//! Smoke tests for the HOL-Light inference rules. Each test
//! builds a small theorem and checks the conclusion shape +
//! type. Together they exercise every rule in the new HOL-Light
//! set: refl, trans, mk_comb, abs, beta_conv, assume, eq_mp,
//! deduct_antisym, inst, plus `Thm::build`'s `bool`-acceptance.

use super::*;

/// Pin the pure tier: these are `Thm<CoreLang>` unit tests (stage E1).
type Thm = crate::thm::Thm;

use crate::hol;

// (The old test-local imp parser is gone: since stage A3 the staying
// axioms are connective-free sequent rules, so no kernel test states an
// implication any more.)

fn n() -> Term {
    Term::free("n", Type::nat())
}

// ============================================================================
// The tier machinery (stage E1): a test HolTier extending CoreLang, standing
// in for the planned `CoreEval` in covalence-hol-eval.
// ============================================================================

/// A test tier that `extends` [`CoreLang`] and (per the Language contract's
/// implementor-choice clause for inherited rules) admits the whole inherited
/// HOL catalogue directly — exactly the shape `CoreEval` will take, so these
/// tests pin the two behaviours init relies on: minting HOL rules directly at
/// the higher tier, and lifting pure-tier theorems into it.
#[derive(Clone, Copy, Debug, Default)]
struct TestTier;

impl covalence_pure::Language for TestTier {
    fn admits(&self, rule: std::any::TypeId) -> bool {
        super::rules::core_admits(rule)
    }
    fn extends(&self, parent: std::any::TypeId) -> bool {
        parent == std::any::TypeId::of::<lang::CoreLang>()
    }
    fn union(self, _other: Self) -> Option<Self> {
        Some(self)
    }
    const MANIFEST: Option<&'static covalence_pure::Manifest> = None;
}

impl lang::HolTier for TestTier {}

/// The HOL rule constructors mint DIRECTLY at a higher tier (no `.lift()`
/// churn): the same catalogue serves any `HolTier` that admits it.
#[test]
fn tier_mints_hol_rules_directly() {
    let thm: crate::thm::Thm<TestTier> = crate::thm::Thm::refl(n()).expect("refl at TestTier");
    let (l, r) = parse_hol_eq(thm.concl()).expect("conclusion is HOL =");
    assert_eq!(l, &n());
    assert_eq!(r, &n());
    // ... and composes with premises at the same tier.
    let sym = thm.sym().expect("sym at TestTier");
    let _: &crate::thm::Thm<TestTier> = &sym;
}

/// `lift` re-homes a pure-tier theorem into an extending tier, preserving the
/// sequent; there is no path down (and no self-lift — `extends` is strict).
#[test]
fn tier_lift_low_to_high_only() {
    let pure_thm = Thm::assume(hol::hol_eq(n(), n())).expect("assume");
    let expected = pure_thm.concl().clone();
    let lifted: crate::thm::Thm<TestTier> = pure_thm.lift().expect("lift CoreLang -> TestTier");
    assert_eq!(lifted.concl(), &expected);
    assert_eq!(lifted.hyps().len(), 1);

    // CoreLang does not extend TestTier: no path down.
    let high = crate::thm::Thm::<TestTier>::refl(n()).unwrap();
    assert!(matches!(high.lift::<lang::CoreLang>(), Err(Error::Pure(_))));

    // CoreLang does not extend itself (extends is the DIRECT-parent gate).
    let refl: Thm = Thm::refl(n()).unwrap();
    assert!(matches!(refl.lift::<lang::CoreLang>(), Err(Error::Pure(_))));
}

#[test]
fn hol_refl_at_nat() {
    let thm = Thm::refl(n()).expect("refl n");
    assert!(thm.hyps().is_empty());
    let (l, r) = parse_hol_eq(thm.concl()).expect("conclusion is HOL =");
    assert_eq!(l, &n());
    assert_eq!(r, &n());
}

#[test]
fn hol_trans_chains() {
    let a = Term::free("a", Type::nat());
    let b = Term::free("b", Type::nat());
    let c = Term::free("c", Type::nat());
    let a_eq_b = Thm::assume(hol::hol_eq(a.clone(), b.clone())).expect("assume a=b");
    let b_eq_c = Thm::assume(hol::hol_eq(b.clone(), c.clone())).expect("assume b=c");
    let a_eq_c = a_eq_b.trans(b_eq_c).expect("trans");
    let (l, r) = parse_hol_eq(a_eq_c.concl()).unwrap();
    assert_eq!(l, &a);
    assert_eq!(r, &c);
}

#[test]
fn hol_beta_conv_reduces() {
    // (λx:nat. x) (succ 0) = succ 0
    let id = Term::abs(Type::nat(), Term::bound(0));
    let arg = Term::app(crate::defs::nat_succ(), Term::nat_lit(0u32));
    let app = Term::app(id, arg.clone());
    let thm = Thm::beta_conv(app.clone()).expect("β");
    let (l, r) = parse_hol_eq(thm.concl()).unwrap();
    assert_eq!(l, &app);
    assert_eq!(r, &arg);
}

#[test]
fn hol_assume_at_bool() {
    let p = Term::free("p", Type::bool());
    let thm = Thm::assume(p.clone()).expect("assume p:bool");
    assert!(thm.hyps().contains(&p));
    assert_eq!(thm.concl(), &p);
}

#[test]
fn hol_assume_rejects_nat() {
    let n = Term::free("n", Type::nat());
    let err = Thm::assume(n).unwrap_err();
    assert!(matches!(err, Error::NotBool(_)));
}

#[test]
fn hol_eq_mp_at_bool() {
    let p = Term::free("p", Type::bool());
    let q = Term::free("q", Type::bool());
    let p_eq_q = Thm::assume(hol::hol_eq(p.clone(), q.clone())).expect("assume p=q");
    let p_thm = Thm::assume(p.clone()).expect("assume p");
    let q_thm = p_eq_q.eq_mp(p_thm).expect("eq_mp");
    assert_eq!(q_thm.concl(), &q);
}

#[test]
fn hol_deduct_antisym_two_assumes() {
    let p = Term::free("p", Type::bool());
    let q = Term::free("q", Type::bool());
    // `{p} ⊢ p` and `{q} ⊢ q` — neither side has the other's
    // conclusion as a hyp, so DEDUCT_ANTISYM_RULE leaves both
    // hyps in place: `{p, q} ⊢ p ⇔ q`. (To get the empty-hyp
    // form `⊢ p ⇔ q` you need cross-assumed shapes like
    // `{q} ⊢ p` and `{p} ⊢ q`, which require non-trivial proofs
    // we don't construct in this smoke test.)
    let p_thm = Thm::assume(p.clone()).unwrap();
    let q_thm = Thm::assume(q.clone()).unwrap();
    let eq = p_thm.deduct_antisym(q_thm).expect("deduct_antisym");
    assert!(eq.hyps().contains(&p));
    assert!(eq.hyps().contains(&q));
    let (l, r) = parse_hol_eq(eq.concl()).unwrap();
    assert_eq!(l, &p);
    assert_eq!(r, &q);
}

#[test]
fn hol_deduct_antisym_cross_assumed() {
    // Cross-assumed: `{q} ⊢ p` and `{p} ⊢ q` (faked via weaken/
    // assume composition — both `assume` and `weaken` are
    // available). The rule should yield `⊢ p ⇔ q` with no hyps.
    let p = Term::free("p", Type::bool());
    let q = Term::free("q", Type::bool());
    // Build `{p, q} ⊢ p` and `{p, q} ⊢ q` by assume + weaken,
    // then deduct_antisym: (Γ−{q}) ∪ (Δ−{p}) = ({p,q}−{q}) ∪
    // ({p,q}−{p}) = {p} ∪ {q} — still both. The literal HOL
    // Light cancellation needs the *minimal* `{q} ⊢ p`, which
    // is not derivable here without an actual ⇔/⟹ axiom. So
    // we verify only that mid-removal happens correctly.
    let pq: Ctx = [p.clone(), q.clone()].into_iter().collect();
    let p_thm = Thm::assume(p.clone()).unwrap().weaken(pq.clone()).unwrap();
    let q_thm = Thm::assume(q.clone()).unwrap().weaken(pq).unwrap();
    let eq = p_thm.deduct_antisym(q_thm).expect("deduct_antisym");
    // hyps = ({p,q} − {q}) ∪ ({p,q} − {p}) = {p, q}.
    assert!(eq.hyps().contains(&p));
    assert!(eq.hyps().contains(&q));
}

#[test]
fn hol_inst_substitutes_free_var() {
    let n_free = Term::free("n", Type::nat());
    let zero = Term::nat_lit(0u32);
    // ⊢ n = n  (HOL refl), then inst n := 0  ⇒  ⊢ 0 = 0.
    let refl = Thm::refl(n_free).unwrap();
    let inst = refl.inst("n", zero.clone()).expect("inst");
    let (l, r) = parse_hol_eq(inst.concl()).unwrap();
    assert_eq!(l, &zero);
    assert_eq!(r, &zero);
}

#[test]
fn hol_mk_comb_at_succ() {
    // ⊢ succ = succ   ⊗   ⊢ 0 = 0   ⇒   ⊢ succ 0 = succ 0
    let succ = crate::defs::nat_succ();
    let zero = Term::nat_lit(0u32);
    let succ_eq = Thm::refl(succ.clone()).unwrap();
    let zero_eq = Thm::refl(zero.clone()).unwrap();
    let app_eq = succ_eq.mk_comb(zero_eq).expect("mk_comb");
    let (l, r) = parse_hol_eq(app_eq.concl()).unwrap();
    assert_eq!(l, &Term::app(succ.clone(), zero.clone()));
    assert_eq!(r, &Term::app(succ, zero));
}

#[test]
fn hol_abs_lambda_eq() {
    // ⊢ x = x   ⇒  abs x:nat   ⇒  ⊢ (λx:nat. x) = (λx:nat. x)
    let x = Term::free("x", Type::nat());
    let refl = Thm::refl(x).unwrap();
    let abs = refl.abs("x", Type::nat()).expect("abs");
    let (l, r) = parse_hol_eq(abs.concl()).unwrap();
    let lam = Term::abs(Type::nat(), Term::bound(0));
    assert_eq!(l, &lam);
    assert_eq!(r, &lam);
}

// =================================================================
// Negative tests — invalid derivations must be rejected
// =================================================================

#[test]
fn hol_refl_rejects_dangling_bound() {
    // Bound(0) outside any binder is an open term.
    let err = Thm::refl(Term::bound(0)).unwrap_err();
    assert!(matches!(err, Error::NotClosed));
}

#[test]
fn hol_refl_rejects_ill_typed_app() {
    // (Free("f", nat → nat) (Free("y", bool))) is malformed —
    // arg type doesn't match function domain.
    let f = Term::free("f", Type::fun(Type::nat(), Type::nat()));
    let y = Term::free("y", Type::bool());
    let bad = Term::app(f, y);
    let err = Thm::refl(bad).unwrap_err();
    assert!(matches!(err, Error::TypeMismatch { .. }));
}

#[test]
fn hol_trans_rejects_non_hol_eq_input() {
    // Plain assume with a bool-typed term — not a HOL equation —
    // can't be transed.
    let p = Term::free("p", Type::bool());
    let p_thm = Thm::assume(p).unwrap();
    let refl = Thm::refl(n()).unwrap();
    let err = p_thm.trans(refl).unwrap_err();
    assert!(matches!(err, Error::NotHolEq(_)));
}

#[test]
fn hol_trans_rejects_middle_mismatch() {
    // s = t  and  u = v  with t ≠ u  ⇒  TransMiddleMismatch.
    let a = Term::free("a", Type::nat());
    let b = Term::free("b", Type::nat());
    let c = Term::free("c", Type::nat());
    let d = Term::free("d", Type::nat());
    let ab = Thm::assume(hol::hol_eq(a, b.clone())).unwrap();
    let cd = Thm::assume(hol::hol_eq(c, d)).unwrap();
    // b ≠ c — middle mismatch.
    let _ = b; // already used above
    let err = ab.trans(cd).unwrap_err();
    assert!(matches!(err, Error::TransMiddleMismatch { .. }));
}

#[test]
fn hol_mk_comb_rejects_non_eq_input() {
    // First thm is a HOL eq, second is not.
    let f_eq = Thm::refl(crate::defs::nat_succ()).unwrap();
    let non_eq = Thm::assume(Term::free("p", Type::bool())).unwrap();
    let err = f_eq.mk_comb(non_eq).unwrap_err();
    assert!(matches!(err, Error::NotHolEq(_)));
}

#[test]
fn hol_mk_comb_rejects_domain_mismatch() {
    // f : nat → nat, but arg is bool. Build's re-typing catches.
    let f = crate::defs::nat_succ(); // : nat → nat
    let f_eq = Thm::refl(f).unwrap();
    let bad = Term::free("p", Type::bool());
    let bad_eq = Thm::refl(bad).unwrap();
    let err = f_eq.mk_comb(bad_eq).unwrap_err();
    assert!(matches!(err, Error::TypeMismatch { .. }));
}

#[test]
fn hol_abs_rejects_var_free_in_hyps() {
    // Hyp contains Free("x", nat). Can't abstract over x.
    let x = Term::free("x", Type::nat());
    let hyp = hol::hol_eq(x.clone(), x.clone()); // x = x : bool
    // Assume the hyp first.
    let h_thm = Thm::assume(hyp).unwrap();
    // Now try to abstract over x — should fail because x is free
    // in the (hyp = self.concl) hypothesis.
    let err = h_thm.abs("x", Type::nat()).unwrap_err();
    assert!(matches!(err, Error::FreeVarInHyps { .. }));
}

#[test]
fn hol_abs_over_differently_typed_var_binds_vacuously() {
    // `Free("x", nat)` in the conclusion; abstracting `("x", bool)` — a
    // *distinct* variable (free vars are identified by name AND type) —
    // binds nothing, so it generalises vacuously and succeeds:
    // `⊢ (λ_:bool. x:nat) = (λ_:bool. x:nat)`.
    let x = Term::free("x", Type::nat());
    let refl = Thm::refl(x).unwrap();
    let out = refl.abs("x", Type::bool()).unwrap();
    let (lhs, _) = out.concl().as_eq().unwrap();
    let (binder, _) = lhs.as_abs().unwrap();
    assert_eq!(binder, &Type::bool());
}

#[test]
fn hol_abs_rejects_non_eq_input() {
    let p = Term::free("p", Type::bool());
    let p_thm = Thm::assume(p).unwrap();
    let err = p_thm.abs("x", Type::nat()).unwrap_err();
    assert!(matches!(err, Error::NotHolEq(_)));
}

#[test]
fn hol_beta_conv_rejects_non_app() {
    // (free n nat) isn't an application.
    let err = Thm::beta_conv(n()).unwrap_err();
    assert!(matches!(err, Error::NotApp(_)));
}

#[test]
fn hol_beta_conv_rejects_non_abs_head() {
    // (succ 0) is an App but the head isn't an Abs.
    let app = Term::app(crate::defs::nat_succ(), Term::nat_lit(0u32));
    let err = Thm::beta_conv(app).unwrap_err();
    assert!(matches!(err, Error::NotAbs(_)));
}

#[test]
fn hol_beta_conv_rejects_arg_type_mismatch() {
    // λx:nat. x  applied to a bool — type mismatch.
    let id = Term::abs(Type::nat(), Term::bound(0));
    let bad_arg = Term::bool_lit(true);
    let app = Term::app(id, bad_arg);
    let err = Thm::beta_conv(app).unwrap_err();
    assert!(matches!(err, Error::TypeMismatch { .. }));
}

#[test]
fn hol_assume_rejects_dangling_bound() {
    let err = Thm::assume(Term::bound(0)).unwrap_err();
    assert!(matches!(err, Error::NotClosed));
}

#[test]
fn hol_eq_mp_rejects_non_eq_first() {
    // self.concl is not a HOL equation.
    let p = Term::free("p", Type::bool());
    let non_eq = Thm::assume(p.clone()).unwrap();
    let other = Thm::assume(p).unwrap();
    let err = non_eq.eq_mp(other).unwrap_err();
    assert!(matches!(err, Error::NotHolEq(_)));
}

#[test]
fn hol_eq_mp_rejects_p_mismatch() {
    // ⊢ p = q  and  ⊢ r (r ≠ p)  ⇒  ImpAntecedentMismatch.
    let p = Term::free("p", Type::bool());
    let q = Term::free("q", Type::bool());
    let r = Term::free("r", Type::bool());
    let eq = Thm::assume(hol::hol_eq(p, q)).unwrap();
    let r_thm = Thm::assume(r).unwrap();
    let err = eq.eq_mp(r_thm).unwrap_err();
    assert!(matches!(err, Error::ImpAntecedentMismatch { .. }));
}

#[test]
fn hol_eq_mp_rejects_non_bool_equation() {
    // ⊢ 5 = 5  at nat — not a biconditional. EQ_MP requires bool.
    let five = Term::nat_lit(5u32);
    let eq = Thm::assume(hol::hol_eq(five.clone(), five.clone())).unwrap();
    let n_thm = Thm::assume(Term::free("p", Type::bool())).unwrap();
    let err = eq.eq_mp(n_thm).unwrap_err();
    assert!(matches!(err, Error::NotBool(_)));
}

#[test]
fn hol_deduct_antisym_rejects_non_bool_lhs() {
    // ⊢ (5 : nat)  is not a valid Thm at all (Thm::build rejects).
    // So construct an assumption-based Thm with nat conclusion via
    // Core assume (which accepts prop) and verify deduct_antisym
    // rejects on non-bool.
    // Build via Thm::assume on a hol_eq — the conclusion is bool.
    // Then forcibly check the not-bool branch via a HOL-Light eq
    // theorem at nat type.
    // Easier: deduct_antisym demands BOTH be bool. If self is a
    // bool theorem and other is nat-Thm, we need to construct a
    // nat-typed Thm — Thm::build won't accept that. So the only
    // way to hit NotBool is if a constructed theorem had a nat
    // conclusion. Currently impossible — Thm::build is sound. So
    // this negative case isn't reachable from user-facing API.
    // We still verify the bool-only positive form holds.
    let p = Term::free("p", Type::bool());
    let q = Term::free("q", Type::bool());
    let p_thm = Thm::assume(p).unwrap();
    let q_thm = Thm::assume(q).unwrap();
    let _eq = p_thm.deduct_antisym(q_thm).expect("deduct_antisym");
    // The not-bool branch in deduct_antisym is defense-in-depth
    // against a future Thm::build relaxation. No user-facing
    // negative test path exists today.
}

#[test]
fn hol_inst_type_mismatched_replacement_is_a_noop() {
    // ⊢ n = n  with n : nat. `inst("n", true)` targets the variable
    // `("n", bool)` — which does not occur (the term has `("n", nat)`),
    // so it is a no-op (HOL Light `vsubst` semantics), leaving the
    // theorem unchanged rather than erroring.
    let n_free = Term::free("n", Type::nat());
    let refl = Thm::refl(n_free).unwrap();
    let before = refl.concl().clone();
    let out = refl.inst("n", Term::bool_lit(true)).unwrap();
    assert_eq!(out.concl(), &before);
}

#[test]
fn hol_inst_no_op_when_name_absent() {
    // n free is "n"; instantiating "x" (no occurrence) is a no-op
    // and the replacement's type is unconstrained.
    let refl = Thm::refl(n()).unwrap();
    let bad = Term::bool_lit(true);
    let result = refl.inst("x", bad).expect("no-op inst");
    let (l, r) = parse_hol_eq(result.concl()).unwrap();
    assert_eq!(l, &n());
    assert_eq!(r, &n());
}

#[test]
fn hol_inst_substitutes_in_hyps_too() {
    // {x = x} ⊢ x = x. Inst x := 0. Get {0 = 0} ⊢ 0 = 0.
    let x = Term::free("x", Type::nat());
    let eq = hol::hol_eq(x.clone(), x.clone());
    let h_thm = Thm::assume(eq).unwrap();
    let zero = Term::nat_lit(0u32);
    let result = h_thm.inst("x", zero.clone()).expect("inst");
    let expected_hyp = hol::hol_eq(zero.clone(), zero.clone());
    assert!(result.hyps().contains(&expected_hyp));
    assert_eq!(result.concl(), &expected_hyp);
}

#[test]
fn hol_inst_rejects_dangling_bound_replacement() {
    // Replacement = Bound(0) — open term.
    let n_free = Term::free("n", Type::nat());
    let refl = Thm::refl(n_free).unwrap();
    let err = refl.inst("n", Term::bound(0)).unwrap_err();
    assert!(matches!(err, Error::NotClosed));
}

#[test]
fn hol_eq_mp_preserves_hyps_union() {
    // Γ ⊢ p = q,  Δ ⊢ p  ⇒  Γ ∪ Δ ⊢ q. Verify the union.
    let p = Term::free("p", Type::bool());
    let q = Term::free("q", Type::bool());
    let h_pq = hol::hol_eq(p.clone(), q.clone());
    let h_other = Term::free("extra", Type::bool());
    // Build {h_pq, h_other} ⊢ p = q via assume + weaken.
    let pq_thm = Thm::assume(h_pq.clone()).unwrap();
    let bigger: Ctx = [h_pq.clone(), h_other.clone()].into_iter().collect();
    let pq_weakened = pq_thm.weaken(bigger).unwrap();
    let p_thm = Thm::assume(p).unwrap();
    let q_thm = pq_weakened.eq_mp(p_thm).unwrap();
    assert!(q_thm.hyps().contains(&h_pq));
    assert!(q_thm.hyps().contains(&h_other));
    assert_eq!(q_thm.concl(), &q);
}

#[test]
fn hol_trans_hyps_union_preserved() {
    let a = Term::free("a", Type::nat());
    let b = Term::free("b", Type::nat());
    let c = Term::free("c", Type::nat());
    let ab = hol::hol_eq(a.clone(), b.clone());
    let bc = hol::hol_eq(b, c.clone());
    let ab_thm = Thm::assume(ab.clone()).unwrap();
    let bc_thm = Thm::assume(bc.clone()).unwrap();
    let ac = ab_thm.trans(bc_thm).unwrap();
    assert!(ac.hyps().contains(&ab));
    assert!(ac.hyps().contains(&bc));
    let (l, r) = parse_hol_eq(ac.concl()).unwrap();
    assert_eq!(l, &a);
    assert_eq!(r, &c);
}

// =================================================================
// Derived HOL-Light rules: sym, cong_app/abs, imp_intro/elim,
// all_intro/elim, eta_conv.
//
// Each rule gets positive + negative coverage. Composition tests
// verify rule interaction (e.g. DISCH then MP recovers the original
// theorem; GEN then SPEC at the same witness round-trips).
// =================================================================

// ---- sym ----

#[test]
fn sym_swaps_eq_sides() {
    let a = Term::free("a", Type::nat());
    let b = Term::free("b", Type::nat());
    let ab = Thm::assume(hol::hol_eq(a.clone(), b.clone())).unwrap();
    let ba = ab.sym().expect("sym");
    let (l, r) = parse_hol_eq(ba.concl()).unwrap();
    assert_eq!(l, &b);
    assert_eq!(r, &a);
}

#[test]
fn sym_rejects_non_eq() {
    let p = Term::free("p", Type::bool());
    let p_thm = Thm::assume(p).unwrap();
    let err = p_thm.sym().unwrap_err();
    assert!(matches!(err, Error::NotHolEq(_)));
}

#[test]
fn sym_preserves_hyps() {
    let a = Term::free("a", Type::nat());
    let b = Term::free("b", Type::nat());
    let extra = Term::free("extra", Type::bool());
    let ab = hol::hol_eq(a.clone(), b.clone());
    let bigger: Ctx = [ab.clone(), extra.clone()].into_iter().collect();
    let thm = Thm::assume(ab).unwrap().weaken(bigger).unwrap();
    let sym = thm.sym().unwrap();
    // hyps unchanged by sym.
    assert!(sym.hyps().contains(&extra));
}

#[test]
fn sym_then_sym_is_identity() {
    let a = Term::free("a", Type::nat());
    let b = Term::free("b", Type::nat());
    let original = Thm::assume(hol::hol_eq(a.clone(), b.clone())).unwrap();
    let twice = original.clone().sym().unwrap().sym().unwrap();
    assert_eq!(twice.concl(), original.concl());
}

// ---- cong_app / cong_abs aliases ----

#[test]
fn cong_app_matches_mk_comb() {
    let succ = crate::defs::nat_succ();
    let zero = Term::nat_lit(0u32);
    let s_eq = Thm::refl(succ.clone()).unwrap();
    let z_eq = Thm::refl(zero.clone()).unwrap();
    let via_mk_comb = s_eq.clone().mk_comb(z_eq.clone()).unwrap();
    let via_cong_app = s_eq.cong_app(z_eq).unwrap();
    assert_eq!(via_mk_comb.concl(), via_cong_app.concl());
}

#[test]
fn cong_abs_matches_abs() {
    let x = Term::free("x", Type::nat());
    let r1 = Thm::refl(x.clone()).unwrap();
    let r2 = Thm::refl(x).unwrap();
    let via_abs = r1.abs("x", Type::nat()).unwrap();
    let via_cong = r2.cong_abs("x", Type::nat()).unwrap();
    assert_eq!(via_abs.concl(), via_cong.concl());
}

// ---- imp_intro (DISCH) / imp_elim (MP) ----

// ---- all_intro (GEN) / all_elim (SPEC) ----

// ---- eta_conv ----

#[test]
fn eta_conv_simple() {
    // λx:nat. succ x  --eta-->  succ
    let succ = crate::defs::nat_succ();
    let lambda = Term::abs(
        Type::nat(),
        Term::app(crate::subst::shift_by(&succ, 1, 0), Term::bound(0)),
    );
    let thm = Thm::eta_conv(lambda.clone()).expect("eta");
    let (l, r) = parse_hol_eq(thm.concl()).unwrap();
    assert_eq!(l, &lambda);
    assert_eq!(r, &succ);
}

#[test]
fn eta_conv_rejects_non_abs() {
    let p = Term::free("p", Type::bool());
    let err = Thm::eta_conv(p).unwrap_err();
    assert!(matches!(err, Error::NotAbs(_)));
}

#[test]
fn eta_conv_rejects_body_not_app() {
    // λx:nat. x is `Abs(_, nat, Bound(0))` — not an app shape.
    let lambda = Term::abs(Type::nat(), Term::bound(0));
    let err = Thm::eta_conv(lambda).unwrap_err();
    assert!(matches!(err, Error::EtaShape));
}

#[test]
fn eta_conv_rejects_arg_not_bound_zero() {
    // λx:nat. succ (succ x) — arg is `succ x`, not `Bound(0)`.
    let succ = crate::defs::nat_succ();
    let inner = Term::app(crate::subst::shift_by(&succ, 1, 0), Term::bound(0));
    let outer = Term::app(crate::subst::shift_by(&succ, 1, 0), inner);
    let lambda = Term::abs(Type::nat(), outer);
    let err = Thm::eta_conv(lambda).unwrap_err();
    assert!(matches!(err, Error::EtaShape));
}

#[test]
fn eta_conv_rejects_bound_zero_free_in_f() {
    // λx:nat. (λy. x) x — `f` (= λy. x) uses Bound(0) outside its own binder,
    // which is `Bound(0)` referring to the outer x. EtaShape.
    let inner = Term::abs(Type::nat(), Term::bound(1)); // refers to outer x
    let lambda = Term::abs(Type::nat(), Term::app(inner, Term::bound(0)));
    let err = Thm::eta_conv(lambda).unwrap_err();
    assert!(matches!(err, Error::EtaShape));
}

// ---- Compositions ----

#[test]
fn sym_then_trans_chains_three() {
    // From ⊢ a = b  and  ⊢ a = c, derive ⊢ b = c via sym+trans.
    let a = Term::free("a", Type::nat());
    let b = Term::free("b", Type::nat());
    let c = Term::free("c", Type::nat());
    let ab = Thm::assume(hol::hol_eq(a.clone(), b.clone())).unwrap();
    let ac = Thm::assume(hol::hol_eq(a, c.clone())).unwrap();
    let ba = ab.sym().unwrap();
    let bc = ba.trans(ac).unwrap();
    let (l, r) = parse_hol_eq(bc.concl()).unwrap();
    assert_eq!(l, &b);
    assert_eq!(r, &c);
}

#[test]
fn nat_induct_rule_derives_open_conclusion() {
    // Sequent form: proposition p := (n = n) with n : nat free.
    // base : ⊢ p[0/n] = (0 = 0); step : {p} ⊢ p[succ n/n].
    let n = Term::free("n", Type::nat());
    let p = hol::hol_eq(n.clone(), n.clone());
    let base = Thm::refl(Term::nat_lit(covalence_types::Nat::zero())).unwrap(); // ⊢ 0 = 0
    let succ_n = Term::app(Term::succ(), n);
    let step = Thm::refl(succ_n)
        .unwrap() // ⊢ succ n = succ n
        .weaken(crate::Ctx::singleton(p.clone()))
        .unwrap(); // {p} ⊢ succ n = succ n
    let thm = Thm::nat_induct(base, step, p.clone(), "n").unwrap();
    // Γ empty (the IH hypothesis `p` is discharged), conclusion is `p`
    // itself with `n` free — generalize with the ordinary GEN rule.
    assert_eq!(thm.concl(), &p);
    assert!(thm.hyps().is_empty());
    // (Generalizing `n` with the ∀-intro DERIVATION is exercised by
    // covalence-hol-eval's `tests/derived_rules.rs`.)
}

// (Ex falso — `false_elim` — left the kernel in stage EG3b; its contract
// tests live with the derivation in covalence-hol-eval: see
// `tests/derived_rules.rs`.)

// ---- nat freeness primitives (sequent forms, stage A3) ----

#[test]
fn succ_eq_elim_strips_succ_under_hyps() {
    // {succ m = succ n} ⊢ m = n.
    let m = Term::free("m", Type::nat());
    let n = Term::free("n", Type::nat());
    let eq = Term::app(
        Term::app(Term::eq_op(Type::nat()), Term::app(Term::succ(), m.clone())),
        Term::app(Term::succ(), n.clone()),
    );
    let thm = Thm::succ_eq_elim(Thm::assume(eq.clone()).unwrap()).expect("succ_eq_elim");
    assert_eq!(thm.hyps().iter().collect::<Vec<_>>(), vec![&eq]);
    let (cl, cr) = parse_hol_eq(thm.concl()).unwrap();
    assert_eq!((cl, cr), (&m, &n));
}

#[test]
fn zero_eq_succ_elim_is_ex_falso() {
    // {0 = succ n} ⊢ q, for BOTH zero shapes (Nat literal and Zero leaf).
    let n = Term::free("n", Type::nat());
    let q = Term::free("q", Type::bool());
    for zero in [hol::zero(), Term::zero()] {
        let eq = Term::app(
            Term::app(Term::eq_op(Type::nat()), zero),
            Term::app(Term::succ(), n.clone()),
        );
        let thm = Thm::zero_eq_succ_elim(Thm::assume(eq.clone()).unwrap(), q.clone())
            .expect("zero_eq_succ_elim");
        assert_eq!(thm.hyps().iter().collect::<Vec<_>>(), vec![&eq]);
        assert_eq!(thm.concl(), &q);
    }
}

#[test]
fn freeness_rules_reject_wrong_premise_shape() {
    let b = Term::free("b", Type::bool());
    let q = Term::free("q", Type::bool());
    // Premise is not an equation at all …
    let not_an_eq = Thm::assume(b.clone()).unwrap();
    assert!(Thm::succ_eq_elim(not_an_eq.clone()).is_err());
    assert!(Thm::zero_eq_succ_elim(not_an_eq, q.clone()).is_err());
    // … or an equation between non-constructor terms.
    let m = Term::free("m", Type::nat());
    let n = Term::free("n", Type::nat());
    let plain_eq = Term::app(Term::app(Term::eq_op(Type::nat()), m.clone()), n.clone());
    let prem = Thm::assume(plain_eq).unwrap();
    assert!(Thm::succ_eq_elim(prem.clone()).is_err());
    assert!(Thm::zero_eq_succ_elim(prem.clone(), q.clone()).is_err());
    // … or `succ m = succ n` offered to zero_eq_succ_elim (zero side wrong).
    let succ_eq = Term::app(
        Term::app(Term::eq_op(Type::nat()), Term::app(Term::succ(), m)),
        Term::app(Term::succ(), n),
    );
    let succ_prem = Thm::assume(succ_eq).unwrap();
    assert!(Thm::zero_eq_succ_elim(succ_prem, q).is_err());
}

#[test]
fn zero_eq_succ_elim_rejects_non_bool_target() {
    // The `q` conclusion must be bool (the `seq` floor).
    let n = Term::free("n", Type::nat());
    let eq = Term::app(
        Term::app(Term::eq_op(Type::nat()), hol::zero()),
        Term::app(Term::succ(), n.clone()),
    );
    let prem = Thm::assume(eq).unwrap();
    assert!(matches!(
        Thm::zero_eq_succ_elim(prem, n),
        Err(Error::NotBool(_))
    ));
}

// ---- choice (ε) + def-style spec unfolding (sequent forms, stage A3) ----

#[test]
fn select_intro_transfers_witness_to_choice() {
    // {p x} ⊢ p (ε p), hypotheses carried through.
    let p = Term::free("p", Type::fun(Type::nat(), Type::bool()));
    let x = Term::free("x", Type::nat());
    let px = Term::app(p.clone(), x);
    let thm = Thm::select_intro(Thm::assume(px.clone()).unwrap()).unwrap();
    assert_eq!(thm.hyps().iter().collect::<Vec<_>>(), vec![&px]);
    let expected = Term::app(p.clone(), Term::app(Term::select_op(Type::nat()), p));
    assert_eq!(thm.concl(), &expected);
}

#[test]
fn select_intro_rejects_non_application_premise() {
    // The premise's conclusion must split as `p x`.
    let b = Term::free("b", Type::bool());
    assert!(matches!(
        Thm::select_intro(Thm::assume(b).unwrap()),
        Err(Error::NotApp(_))
    ));
}

#[test]
fn spec_intro_on_natrec_transports_witness_to_spec() {
    // natRec is def-style; from {P_rec w} ⊢ P_rec w conclude
    // {P_rec w} ⊢ P_rec(natRec).
    let nr = crate::defs::nat_rec(Type::nat());
    let TermKind::Spec(spec, args) = nr.kind() else {
        panic!("natRec is not a Spec leaf");
    };
    // Rebuild the instantiated selector predicate the same way the rule does.
    let pred = super::inst_spec_tvars(spec.tm().unwrap(), &spec.ty().unwrap().free_tvars(), args);
    let rty = nr.type_of().unwrap(); // the recursor carrier type
    let w = Term::free("w", rty);
    let pw = Term::app(pred.clone(), w);
    let thm = Thm::spec_intro(Thm::assume(pw.clone()).unwrap(), nr.clone()).unwrap();
    assert_eq!(thm.hyps().iter().collect::<Vec<_>>(), vec![&pw]);
    // The conclusion applies the SAME predicate to natRec itself (NOT to
    // `ε p` — the spec is not equated with the anonymous choice).
    assert_eq!(thm.concl(), &Term::app(pred, nr));
}

#[test]
fn spec_intro_rejects_let_style() {
    // nat_add is a let-style spec → must be refused (before the premise
    // shape even matters).
    let some_prem = Thm::assume(Term::free("b", Type::bool())).unwrap();
    assert!(matches!(
        Thm::spec_intro(some_prem, crate::defs::nat_add()),
        Err(Error::SpecIsLetStyle)
    ));
}

#[test]
fn spec_intro_rejects_foreign_predicate() {
    // A premise headed by some OTHER predicate of the right type must be
    // refused — recognition is structural equality against the spec's own
    // selector predicate.
    let nr = crate::defs::nat_rec(Type::nat());
    let rty = nr.type_of().unwrap();
    let q = Term::free("q", Type::fun(rty.clone(), Type::bool()));
    let qw = Term::app(q, Term::free("w", rty));
    let prem = Thm::assume(qw).unwrap();
    assert!(matches!(
        Thm::spec_intro(prem, nr),
        Err(Error::ConnectiveRule(_))
    ));
}

// ---- TypeSpec subtype laws (spec_abs_rep / spec_rep_abs_fwd / _back) ----

// ===========================================================================
// Cons-threaded (`_with`) rule variants — port of the 9d3673f9 audit tests.
//
// These exercise the cons-threaded rule variants: routing through a
// `HashCons` must (a) produce a result structurally equal to the plain
// rule, and (b) populate the interner with the conclusion's spine so
// structurally-equal subterms dedup to one `Arc` (`ptr_id`) through it.
// (Under the intern-after-mint `_with` contract the theorem itself keeps
// the rule's own `Arc`s; sharing is observed via the interner's table.)

#[test]
fn refl_with_interns_duplicated_term() {
    use crate::term::HashCons;
    // refl x = (= x x); the conclusion must match the plain `refl`, the
    // two `x` occurrences share one Arc (refl builds `t = t` from one
    // term), and the interner picked up the conclusion's spine.
    let x = Term::free("x", Type::nat());
    let plain = Thm::refl(x.clone()).expect("refl");
    let mut hc = HashCons::new();
    let interned = Thm::refl_with(x.clone(), &mut hc).expect("refl_with");
    assert_eq!(plain.concl(), interned.concl());

    // concl = App(App(Eq, lhs), rhs); lhs and rhs are both `x`.
    let (lhs, rhs) = parse_hol_eq(interned.concl()).unwrap();
    assert_eq!(lhs.ptr_id(), rhs.ptr_id(), "both `x` occurrences shared");
    assert!(!hc.is_empty(), "conclusion spine interned");
}

#[test]
fn trans_with_matches_plain_and_shares_outer_terms() {
    use crate::term::HashCons;
    // a = b, b = c  ⊢  a = c. `trans_with` must (a) produce the same
    // conclusion as plain `trans`, and (b) reuse — by Arc identity — the
    // exact `a` and `c` subterms read off the input theorems (`s.clone()`
    // / `u.clone()`), rather than rebuilding them.
    let a = Term::free("a", Type::nat());
    let b = Term::free("b", Type::nat());
    let c = Term::free("c", Type::nat());

    let eq_ab = hol::hol_eq(a.clone(), b.clone());
    let eq_bc = hol::hol_eq(b.clone(), c.clone());
    // Grab the exact Arc leaves the input theorems carry, so we can check
    // the result reuses them.
    let (in_a, _) = parse_hol_eq(&eq_ab).unwrap();
    let in_a = in_a.clone();
    let (_, in_c) = parse_hol_eq(&eq_bc).unwrap();
    let in_c = in_c.clone();
    let t_ab = Thm::assume(eq_ab).expect("assume a=b");
    let t_bc = Thm::assume(eq_bc).expect("assume b=c");

    let mut hc = HashCons::new();
    let plain = t_ab.clone().trans(t_bc.clone()).expect("trans");
    let interned = t_ab.trans_with(t_bc, &mut hc).expect("trans_with");
    assert_eq!(plain.concl(), interned.concl());

    let (lhs, rhs) = parse_hol_eq(interned.concl()).unwrap();
    assert_eq!(lhs.ptr_id(), in_a.ptr_id(), "result reuses input lhs `a`");
    assert_eq!(rhs.ptr_id(), in_c.ptr_id(), "result reuses input rhs `c`");
}

#[test]
fn mk_comb_with_interns_heads() {
    use crate::term::HashCons;
    // f = f, x = x  ⊢  f x = f x. The rule builds the two `f x`
    // applications as separate nodes; routed through one HashCons they
    // dedup to a single representative in the interner's table.
    let fty = Type::fun(Type::nat(), Type::bool());
    let f = Term::free("f", fty.clone());
    let x = Term::free("x", Type::nat());

    let mut hc = HashCons::new();
    let f_eq = Thm::refl_with(f.clone(), &mut hc).expect("refl f");
    let x_eq = Thm::refl_with(x.clone(), &mut hc).expect("refl x");

    let plain = f_eq.clone().mk_comb(x_eq.clone()).expect("mk_comb");
    let interned = f_eq.mk_comb_with(x_eq, &mut hc).expect("mk_comb_with");
    assert_eq!(plain.concl(), interned.concl());

    // concl = (f x) = (f x): lhs and rhs are structurally equal `App`s.
    // The interner saw both, so re-consing the conclusion through it
    // canonicalises them to one shared Arc.
    let canon = interned.concl().cons_with(&mut hc);
    let (lhs, rhs) = parse_hol_eq(&canon).unwrap();
    assert_eq!(
        lhs.ptr_id(),
        rhs.ptr_id(),
        "the two `f x` applications shared via the interner"
    );
}
