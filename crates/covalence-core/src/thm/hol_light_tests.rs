//! Smoke tests for the HOL-Light inference rules. Each test
//! builds a small theorem and checks the conclusion shape +
//! type. Together they exercise every rule in the new HOL-Light
//! set: refl, trans, mk_comb, abs, beta_conv, assume, eq_mp,
//! deduct_antisym, inst, plus `Thm::build`'s `bool`-acceptance.

use super::*;

fn n() -> Term {
    Term::free("n", Type::nat())
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
fn hol_abs_rejects_binder_type_mismatch() {
    // Free("x", nat) in concl, but user supplies ty = bool.
    let x = Term::free("x", Type::nat());
    let refl = Thm::refl(x).unwrap();
    let err = refl.abs("x", Type::bool()).unwrap_err();
    assert!(matches!(err, Error::BinderTypeMismatch { .. }));
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
fn hol_inst_rejects_replacement_type_mismatch() {
    // ⊢ n = n  with n : nat. Try to inst n := (bool literal).
    let n_free = Term::free("n", Type::nat());
    let refl = Thm::refl(n_free).unwrap();
    let bad = Term::bool_lit(true);
    let err = refl.inst("n", bad).unwrap_err();
    assert!(matches!(err, Error::TypeMismatch { .. }));
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

#[test]
fn imp_intro_discharges_hyp() {
    // {p} ⊢ p   --imp_intro p->   ⊢ p ⟹ p
    let p = Term::free("p", Type::bool());
    let p_thm = Thm::assume(p.clone()).unwrap();
    let imp = p_thm.imp_intro(&p).expect("imp_intro");
    assert!(imp.hyps().is_empty(), "p discharged from hyps");
    let (lhs, rhs) = parse_hol_imp(imp.concl()).unwrap();
    assert_eq!(lhs, &p);
    assert_eq!(rhs, &p);
}

#[test]
fn imp_intro_leaves_other_hyps() {
    let p = Term::free("p", Type::bool());
    let q = Term::free("q", Type::bool());
    // Build {p, q} ⊢ q via assume+weaken.
    let pq: Ctx = [p.clone(), q.clone()].into_iter().collect();
    let q_thm = Thm::assume(q.clone()).unwrap().weaken(pq).unwrap();
    let imp = q_thm.imp_intro(&p).unwrap();
    // p removed, q still in hyps.
    assert!(!imp.hyps().contains(&p));
    assert!(imp.hyps().contains(&q));
}

#[test]
fn imp_intro_with_absent_phi_is_weakening() {
    // ⊢ p  with no occurrence of `q` as a hyp → ⊢ q ⟹ p
    let p = Term::free("p", Type::bool());
    let q = Term::free("q", Type::bool());
    let p_thm = Thm::assume(p.clone()).unwrap();
    let imp = p_thm.imp_intro(&q).expect("imp_intro");
    // p still hyp because q ≠ p.
    assert!(imp.hyps().contains(&p));
    let (lhs, rhs) = parse_hol_imp(imp.concl()).unwrap();
    assert_eq!(lhs, &q);
    assert_eq!(rhs, &p);
}

#[test]
fn imp_intro_rejects_non_bool_phi() {
    let p = Term::free("p", Type::bool());
    let p_thm = Thm::assume(p).unwrap();
    let bad = Term::free("n", Type::nat());
    let err = p_thm.imp_intro(&bad).unwrap_err();
    assert!(matches!(err, Error::NotBool(_)));
}

#[test]
fn imp_elim_modus_ponens() {
    // ⊢ p ⟹ q  and  ⊢ p   ⇒   ⊢ q
    let p = Term::free("p", Type::bool());
    let q = Term::free("q", Type::bool());
    let imp = Thm::assume(hol::hol_imp(p.clone(), q.clone())).unwrap();
    let p_thm = Thm::assume(p.clone()).unwrap();
    let result = imp.imp_elim(p_thm).expect("imp_elim");
    assert_eq!(result.concl(), &q);
}

#[test]
fn imp_elim_unions_hyps() {
    let p = Term::free("p", Type::bool());
    let q = Term::free("q", Type::bool());
    let extra = Term::free("extra", Type::bool());
    let imp_body = hol::hol_imp(p.clone(), q.clone());
    let bigger: Ctx = [imp_body.clone(), extra.clone()].into_iter().collect();
    let imp = Thm::assume(imp_body).unwrap().weaken(bigger).unwrap();
    let p_thm = Thm::assume(p).unwrap();
    let q_thm = imp.imp_elim(p_thm).unwrap();
    assert!(q_thm.hyps().contains(&extra));
}

#[test]
fn imp_elim_rejects_non_imp() {
    let p = Term::free("p", Type::bool());
    let p_thm = Thm::assume(p.clone()).unwrap();
    let q_thm = Thm::assume(Term::free("q", Type::bool())).unwrap();
    let err = p_thm.imp_elim(q_thm).unwrap_err();
    assert!(matches!(err, Error::NotHolImp(_)));
}

#[test]
fn imp_elim_rejects_antecedent_mismatch() {
    let p = Term::free("p", Type::bool());
    let q = Term::free("q", Type::bool());
    let r = Term::free("r", Type::bool());
    let imp = Thm::assume(hol::hol_imp(p, q)).unwrap();
    let r_thm = Thm::assume(r).unwrap();
    let err = imp.imp_elim(r_thm).unwrap_err();
    assert!(matches!(err, Error::ImpAntecedentMismatch { .. }));
}

#[test]
fn disch_mp_round_trips() {
    // From {p} ⊢ p, DISCH then MP back with ⊢ p should recover ⊢ p.
    let p = Term::free("p", Type::bool());
    let assumed = Thm::assume(p.clone()).unwrap();
    let imp = assumed.imp_intro(&p).unwrap();   // ⊢ p ⟹ p
    let p_thm = Thm::assume(p.clone()).unwrap();
    let recovered = imp.imp_elim(p_thm).unwrap(); // ⊢ p
    assert_eq!(recovered.concl(), &p);
}

// ---- all_intro (GEN) / all_elim (SPEC) ----

#[test]
fn all_intro_generalises_free_var() {
    // ⊢ p[x]   --all_intro x:nat-->   ⊢ ∀x:nat. p[x]
    // Construct ⊢ x = x : bool by refl, then generalise.
    let x = Term::free("x", Type::nat());
    let refl = Thm::refl(x).unwrap();   // ⊢ x = x : bool
    let univ = refl.all_intro("x", Type::nat()).expect("all_intro");
    let (ty, _body) = parse_hol_forall(univ.concl()).unwrap();
    assert_eq!(ty, &Type::nat());
}

#[test]
fn all_intro_rejects_var_free_in_hyps() {
    // {x = x} ⊢ x = x — generalising over x must fail.
    let x = Term::free("x", Type::nat());
    let eq = hol::hol_eq(x.clone(), x.clone());
    let thm = Thm::assume(eq).unwrap();
    let err = thm.all_intro("x", Type::nat()).unwrap_err();
    assert!(matches!(err, Error::FreeVarInHyps { .. }));
}

#[test]
fn all_intro_rejects_binder_type_mismatch() {
    // x : nat in concl, but generalise at bool — caught at the
    // declared-type check.
    let x = Term::free("x", Type::nat());
    let refl = Thm::refl(x).unwrap();
    let err = refl.all_intro("x", Type::bool()).unwrap_err();
    assert!(matches!(err, Error::BinderTypeMismatch { .. }));
}

#[test]
fn all_intro_with_vacuous_var_succeeds() {
    // If the named var doesn't appear free, generalisation is
    // vacuous but still well-formed.
    let p = Term::free("p", Type::bool());
    let refl = Thm::refl(p).unwrap();
    let univ = refl.all_intro("x", Type::nat()).expect("vacuous gen");
    let (ty, _) = parse_hol_forall(univ.concl()).unwrap();
    assert_eq!(ty, &Type::nat());
}

#[test]
fn all_elim_instantiates_witness() {
    // ⊢ ∀x:nat. x = x   ⇒[x := 5]⇒   ⊢ 5 = 5
    let x = Term::free("x", Type::nat());
    let refl = Thm::refl(x).unwrap();
    let univ = refl.all_intro("x", Type::nat()).unwrap();
    let five = Term::nat_lit(5u32);
    let inst = univ.all_elim(five.clone()).expect("all_elim");
    let (l, r) = parse_hol_eq(inst.concl()).unwrap();
    assert_eq!(l, &five);
    assert_eq!(r, &five);
}

#[test]
fn all_elim_rejects_non_forall() {
    let p = Term::free("p", Type::bool());
    let p_thm = Thm::assume(p).unwrap();
    let err = p_thm.all_elim(Term::nat_lit(0u32)).unwrap_err();
    assert!(matches!(err, Error::NotHolForall(_)));
}

#[test]
fn all_elim_rejects_witness_type_mismatch() {
    let x = Term::free("x", Type::nat());
    let univ = Thm::refl(x).unwrap().all_intro("x", Type::nat()).unwrap();
    let bad = Term::bool_lit(true); // bool, not nat
    let err = univ.all_elim(bad).unwrap_err();
    assert!(matches!(err, Error::TypeMismatch { .. }));
}

#[test]
fn gen_spec_round_trips_at_concrete_witness() {
    // From ⊢ p (where p has free `x`), GEN then SPEC at `x` itself
    // recovers ⊢ p (the witness is the var being substituted in).
    let x = Term::free("x", Type::nat());
    let refl = Thm::refl(x.clone()).unwrap();
    let univ = refl.clone().all_intro("x", Type::nat()).unwrap();
    let recovered = univ.all_elim(x).unwrap();
    assert_eq!(recovered.concl(), refl.concl());
}

// ---- eta_conv ----

#[test]
fn eta_conv_simple() {
    // λx:nat. succ x  --eta-->  succ
    let succ = crate::defs::nat_succ();
    let lambda = Term::abs(Type::nat(),
        Term::app(crate::subst::shift_by(&succ, 1, 0), Term::bound(0)));
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
fn mp_after_disch_chain_with_two_hyps() {
    // From {p, q} ⊢ q, DISCH both then MP both back.
    let p = Term::free("p", Type::bool());
    let q = Term::free("q", Type::bool());
    let pq: Ctx = [p.clone(), q.clone()].into_iter().collect();
    let q_thm = Thm::assume(q.clone()).unwrap().weaken(pq).unwrap();
    // ⊢ q ⟹ q   (after discharging q)
    let imp_q = q_thm.imp_intro(&q).unwrap();
    // ⊢ p ⟹ q ⟹ q   (after discharging p — only `q` remains)
    let imp_p = imp_q.imp_intro(&p).unwrap();
    assert!(imp_p.hyps().is_empty());

    // Apply MP with ⊢ p, then with ⊢ q.
    let p_thm = Thm::assume(p).unwrap();
    let q_thm = Thm::assume(q.clone()).unwrap();
    let step1 = imp_p.imp_elim(p_thm).unwrap();
    let final_ = step1.imp_elim(q_thm).unwrap();
    assert_eq!(final_.concl(), &q);
}

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
fn gen_spec_at_different_witness_substitutes() {
    // GEN over x, SPEC at `y` substitutes correctly.
    let x = Term::free("x", Type::nat());
    let refl = Thm::refl(x).unwrap();
    let univ = refl.all_intro("x", Type::nat()).unwrap();
    let y = Term::free("y", Type::nat());
    let inst = univ.all_elim(y.clone()).unwrap();
    let (l, r) = parse_hol_eq(inst.concl()).unwrap();
    assert_eq!(l, &y);
    assert_eq!(r, &y);
}

#[test]
fn nat_induct_rule_builds_forall() {
    // Motive p := λn. (n = n). base ⊢ p 0; step ⊢ p n ⟹ p (succ n).
    let p = {
        let nf = Term::free("n", Type::nat());
        hol::pub_abs("n", Type::nat(), hol::hol_eq(nf.clone(), nf))
    };
    let zero = Term::nat_lit(covalence_types::Nat::zero());
    // base : ⊢ p 0  (build `p 0` then β-reduce, then refl gives p 0).
    let base = {
        let redex = Term::app(p.clone(), zero);
        let beta = Thm::beta_conv(redex).unwrap(); // ⊢ p 0 = (0 = 0)
        let refl00 =
            Thm::refl(Term::nat_lit(covalence_types::Nat::zero())).unwrap();
        beta.sym().unwrap().eq_mp(refl00).unwrap() // ⊢ p 0
    };
    // step : ⊢ p n ⟹ p (succ n) — assume `p n`, prove `p (succ n)`.
    let n = Term::free("n", Type::nat());
    let p_n = Term::app(p.clone(), n.clone());
    let succ_n = Term::app(hol::succ_fn(), n);
    let p_succ_n = Term::app(p.clone(), succ_n.clone());
    // ⊢ p (succ n) : beta-reduce to (succ n = succ n), refl, fold back.
    let psucc = {
        let beta = Thm::beta_conv(p_succ_n).unwrap(); // ⊢ p(succ n) = (succ n = succ n)
        let refl_s = Thm::refl(succ_n).unwrap();
        beta.sym().unwrap().eq_mp(refl_s).unwrap()
    };
    let step = psucc.imp_intro(&p_n).unwrap(); // ⊢ p n ⟹ p (succ n)

    let thm = Thm::nat_induct(base, step).unwrap();
    // ⊢ ∀n:nat. p n
    let (ty, _) = parse_hol_forall(thm.concl()).unwrap();
    assert_eq!(ty, &Type::nat());
    assert!(thm.hyps().is_empty());
}

#[test]
fn false_elim_yields_anything() {
    let f = Thm::assume(Term::bool_lit(false)).unwrap(); // {F} ⊢ F
    let p = Term::free("p", Type::bool());
    let got = f.false_elim(p.clone()).unwrap();
    assert_eq!(got.concl(), &p);
}

#[test]
fn false_elim_rejects_non_false() {
    // A proof of `T` is not a proof of `F`; ex falso must reject it.
    let t = Thm::assume(Term::bool_lit(true)).unwrap();
    assert!(t.false_elim(Term::free("p", Type::bool())).is_err());
}

// ---- nat freeness primitives ----

#[test]
fn succ_reduces_on_literals() {
    // The primitive `succ` evaluates on a closed literal.
    let app = Term::app(Term::succ(), Term::nat_lit(7u32));
    let thm = Thm::reduce_prim(app.clone()).expect("reduce succ 7");
    let (lhs, rhs) = parse_hol_eq(thm.concl()).unwrap();
    assert_eq!(lhs, &app);
    assert_eq!(rhs, &Term::nat_lit(8u32));
}

#[test]
fn succ_inj_shape_and_hyp_free() {
    // ⊢ (succ m = succ n) ⟹ (m = n), no hypotheses.
    let m = Term::free("m", Type::nat());
    let n = Term::free("n", Type::nat());
    let thm = Thm::succ_inj(m.clone(), n.clone()).expect("succ_inj");
    assert!(thm.hyps().is_empty());
    let (prem, concl) = parse_hol_imp(thm.concl()).unwrap();
    assert_eq!(
        prem,
        &Term::app(
            Term::app(Term::eq_op(Type::nat()), Term::app(Term::succ(), m.clone())),
            Term::app(Term::succ(), n.clone()),
        )
    );
    let (cl, cr) = parse_hol_eq(concl).unwrap();
    assert_eq!((cl, cr), (&m, &n));
}

#[test]
fn zero_ne_succ_shape_and_hyp_free() {
    // ⊢ ¬(0 = succ n).
    let n = Term::free("n", Type::nat());
    let thm = Thm::zero_ne_succ(n).expect("zero_ne_succ");
    assert!(thm.hyps().is_empty());
    assert!(thm.concl().type_of().unwrap().is_bool());
}

#[test]
fn freeness_rules_reject_non_nat() {
    let b = Term::free("b", Type::bool());
    assert!(Thm::succ_inj(b.clone(), b.clone()).is_err());
    assert!(Thm::zero_ne_succ(b).is_err());
}

// ---- choice (ε) + def-style spec unfolding ----

#[test]
fn select_ax_shape_and_hyp_free() {
    // p : nat → bool, x : nat  ⊢  (p x) ⟹ (p (ε p))
    let p = Term::free("p", Type::fun(Type::nat(), Type::bool()));
    let x = Term::free("x", Type::nat());
    let thm = Thm::select_ax(p.clone(), x.clone()).unwrap();
    assert!(thm.hyps().is_empty());
    let (prem, concl) = parse_hol_imp(thm.concl()).unwrap();
    assert_eq!(prem, &Term::app(p.clone(), x));
    let expected = Term::app(
        p.clone(),
        Term::app(Term::select_op(Type::nat()), p),
    );
    assert_eq!(concl, &expected);
}

#[test]
fn select_ax_rejects_non_predicate() {
    // p must be `α → bool`.
    let bad = Term::free("p", Type::fun(Type::nat(), Type::nat()));
    assert!(Thm::select_ax(bad, Term::free("x", Type::nat())).is_err());
}

#[test]
fn spec_ax_on_natrec_is_the_choice_implication() {
    // natRec is def-style; spec_ax gives `(P_rec w) ⟹ P_rec(natRec)`.
    let nr = crate::defs::nat_rec(Type::nat());
    let rty = nr.type_of().unwrap(); // the recursor carrier type
    let w = Term::free("w", rty);
    let thm = Thm::spec_ax(nr.clone(), w.clone()).unwrap();
    assert!(thm.hyps().is_empty());
    let (prem, concl) = parse_hol_imp(thm.concl()).unwrap();
    // premise applies the predicate to the witness …
    let TermKind::App(_p1, pw_arg) = prem.kind() else {
        panic!("premise is not `p w`");
    };
    assert_eq!(pw_arg, &w);
    // … conclusion applies the SAME predicate to natRec itself (NOT to
    // `ε p` — the spec is not equated with the anonymous choice).
    let TermKind::App(_p2, pt_arg) = concl.kind() else {
        panic!("conclusion is not `p t`");
    };
    assert_eq!(pt_arg, &nr);
}

#[test]
fn spec_ax_rejects_let_style() {
    // nat_add is a let-style spec → must be refused.
    let w = Term::free("w", crate::defs::nat_add().type_of().unwrap());
    assert!(matches!(
        Thm::spec_ax(crate::defs::nat_add(), w),
        Err(Error::SpecIsLetStyle)
    ));
}

#[test]
fn spec_ax_rejects_wrong_witness_type() {
    let nr = crate::defs::nat_rec(Type::nat());
    // a `nat` witness, not the recursor carrier type → reject.
    assert!(Thm::spec_ax(nr, Term::free("w", Type::nat())).is_err());
}

#[test]
fn select_ax_rejects_witness_type_mismatch() {
    // The witness `x` must inhabit the predicate's domain α.
    let p = Term::free("p", Type::fun(Type::nat(), Type::bool()));
    let x = Term::free("x", Type::bool()); // bool, not nat
    assert!(matches!(
        Thm::select_ax(p, x),
        Err(Error::TypeMismatch { .. })
    ));
}

#[test]
fn spec_ax_rejects_declaration_only_and_non_spec() {
    // A declaration-only spec (`tm = None`, e.g. `cond`) has no predicate.
    let decl = crate::defs::cond(Type::nat());
    let w = Term::free("w", decl.type_of().unwrap());
    assert!(matches!(Thm::spec_ax(decl, w), Err(Error::SpecHasNoBody)));
    // A non-spec term is rejected before anything else.
    assert!(matches!(
        Thm::spec_ax(Term::nat_lit(5u32), Term::nat_lit(0u32)),
        Err(Error::NotASpec)
    ));
}

#[test]
fn lem_is_axiom_free_disjunction() {
    let p = Term::free("p", Type::bool());
    let thm = Thm::lem(p.clone()).unwrap();
    assert!(thm.hyps().is_empty(), "LEM carries no hypotheses");
    // Conclusion is `p ∨ ¬p`.
    let expected = crate::hol::hol_or(p.clone(), crate::hol::hol_not(p));
    assert_eq!(thm.concl(), &expected);
}

#[test]
fn lem_rejects_non_bool() {
    // LEM is only well-formed at type bool.
    assert!(Thm::lem(Term::free("n", Type::nat())).is_err());
}

#[test]
fn lem_on_bool_literals_and_compound_props() {
    // Literal propositions: `T ∨ ¬T`, `F ∨ ¬F`.
    for b in [true, false] {
        let p = Term::bool_lit(b);
        let thm = Thm::lem(p.clone()).unwrap();
        assert!(thm.hyps().is_empty());
        assert_eq!(thm.concl(), &crate::hol::hol_or(p.clone(), crate::hol::hol_not(p)));
    }
    // A compound proposition (an equation at nat) is `bool`-typed, so LEM
    // applies and the disjuncts are that whole proposition.
    let eq = crate::hol::hol_eq(Term::nat_lit(3u32), Term::free("k", Type::nat()));
    let thm = Thm::lem(eq.clone()).unwrap();
    let (l, r) = parse_hol_or(thm.concl()).unwrap();
    assert_eq!(l, &eq);
    assert_eq!(r, &crate::hol::hol_not(eq));
}

#[test]
fn lem_rejects_open_term() {
    // An open term (dangling `Bound`) is not typeable, so LEM rejects it
    // rather than building an ill-formed disjunction.
    assert!(Thm::lem(Term::bound(0)).is_err());
}

#[test]
fn lem_drives_a_case_split_via_or_elim() {
    // The canonical use of LEM: case-split on `p ∨ ¬p`. With `p ⟹ r` and
    // `¬p ⟹ r`, `or_elim` yields `r`. Here both branches are the vacuous
    // discharge of `assume r`, so the result is `{r} ⊢ r` — exercising
    // that LEM's disjunction is structurally an `or_elim` premise.
    let p = Term::free("p", Type::bool());
    let r = Term::free("r", Type::bool());
    let lem = Thm::lem(p.clone()).unwrap(); // ⊢ p ∨ ¬p
    let r_thm = Thm::assume(r.clone()).unwrap(); // {r} ⊢ r
    let left = r_thm.clone().imp_intro(&p).unwrap(); // {r} ⊢ p ⟹ r
    let right = r_thm.imp_intro(&crate::hol::hol_not(p)).unwrap(); // {r} ⊢ ¬p ⟹ r
    let out = lem.or_elim(left, right).expect("LEM feeds or_elim");
    assert_eq!(out.concl(), &r);
    assert!(out.hyps().contains(&r) && out.hyps().len() == 1);
}

// ---- TypeSpec subtype laws (spec_abs_rep / spec_rep_abs_fwd / _back) ----

#[test]
fn spec_abs_rep_unconditional_for_set_newtype() {
    // `set bool` is a newtype over `bool → bool`. abs (rep s) = s.
    let elem = Type::bool();
    let spec = crate::defs::set_spec();
    let args = crate::ty::TypeList::from(vec![elem.clone()]);
    let s = Term::free("s", Type::spec(spec.clone(), args.clone()));
    let thm = Thm::spec_abs_rep(spec, args, s.clone()).expect("abs (rep s) = s");
    assert!(thm.hyps().is_empty());
    let (_l, r) = parse_hol_eq(thm.concl()).unwrap();
    assert_eq!(r, &s, "rhs is the wrapper element itself");
}

#[test]
fn spec_rep_abs_fwd_discharges_to_unconditional_for_newtype() {
    // For a newtype the premise `P p` is `(λ_. T) p`; β + truth discharge
    // it, yielding the unconditional `rep (abs p) = p`.
    let elem = Type::bool();
    let carrier = Type::fun(elem.clone(), Type::bool()); // set bool's carrier
    let spec = crate::defs::set_spec();
    let args = crate::ty::TypeList::from(vec![elem]);
    let p = Term::free("p", carrier);
    let imp = Thm::spec_rep_abs_fwd(spec, args, p.clone()).expect("P p ⟹ rep (abs p) = p");
    assert!(imp.hyps().is_empty());
    // The antecedent `(λ_. T) p` β-reduces to `T`.
    let (prem, _eq) = parse_hol_imp(imp.concl()).unwrap();
    let beta = Thm::beta_conv(prem.clone()).expect("β on (λ_. T) p");
    assert_eq!(beta.concl().as_eq().unwrap().1, &Term::bool_lit(true));
}

#[test]
fn spec_rep_abs_back_has_emptiness_escape() {
    // back: rep (abs a) = a ⟹ (P a ∨ ¬∃x. P x).
    let elem = Type::bool();
    let carrier = Type::fun(elem.clone(), Type::bool());
    let spec = crate::defs::set_spec();
    let args = crate::ty::TypeList::from(vec![elem]);
    let a = Term::free("p", carrier);
    let thm = Thm::spec_rep_abs_back(spec, args, a).expect("back direction");
    assert!(thm.hyps().is_empty());
    // Conclusion is an implication whose consequent is a disjunction.
    let (_prem, disj) = parse_hol_imp(thm.concl()).unwrap();
    assert!(parse_hol_or(disj).is_ok(), "consequent is `P a ∨ ¬∃x. P x`");
}

#[test]
fn subtype_laws_reject_non_subtype_carrier() {
    // A type mismatch: feeding a `nat` where the carrier is `bool → bool`.
    let elem = Type::bool();
    let spec = crate::defs::set_spec();
    let args = crate::ty::TypeList::from(vec![elem]);
    assert!(Thm::spec_rep_abs_fwd(spec, args, Term::free("n", Type::nat())).is_err());
}
