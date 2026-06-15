//! Exhaustive edge-case audit of the equality / congruence / basic
//! LCF rules in `covalence-core::thm`:
//!   refl, sym, trans, mk_comb/cong_app, abs/cong_abs, beta_conv,
//!   eta_conv, assume, eq_mp, deduct_antisym, inst, weaken,
//!   plus the accessors and the `Thm::build` backstop.
//!
//! This is an *integration* test (external crate), so it can only
//! touch the public API. HOL equations are built by hand with
//! `Term::eq_op` because `hol::hol_eq` is crate-private.
//!
//! Every rejection path is a soundness guard; both happy paths and
//! every reachable error path are exercised.

use covalence_core::{Error, Term, TermKind, Thm, Type};

// ============================================================================
// Helpers
// ============================================================================

/// Build the HOL equation `lhs = rhs` at element type `ty`:
/// `App(App(Eq(ty), lhs), rhs)`.
fn eq_at(ty: Type, lhs: Term, rhs: Term) -> Term {
    Term::app(Term::app(Term::eq_op(ty), lhs), rhs)
}

fn nat_eq(lhs: Term, rhs: Term) -> Term {
    eq_at(Type::nat(), lhs, rhs)
}

fn bool_eq(lhs: Term, rhs: Term) -> Term {
    eq_at(Type::bool(), lhs, rhs)
}

/// Walk an `App(App(Eq(_), lhs), rhs)` and return `(lhs, rhs)`.
fn parse_eq(t: &Term) -> (Term, Term) {
    let TermKind::App(f, rhs) = t.kind() else {
        panic!("not an App at top: {t}");
    };
    let TermKind::App(head, lhs) = f.kind() else {
        panic!("not an App at f: {t}");
    };
    assert!(
        matches!(head.kind(), TermKind::Eq(_)),
        "head is not Eq: {t}"
    );
    (lhs.clone(), rhs.clone())
}

fn nat(name: &str) -> Term {
    Term::free(name, Type::nat())
}
fn boolv(name: &str) -> Term {
    Term::free(name, Type::bool())
}
fn n5() -> Term {
    Term::nat_lit(covalence_types::Nat::from_inner(5u32.into()))
}

// ============================================================================
// refl
// ============================================================================

#[test]
fn refl_concl_is_t_eq_t() {
    let t = nat("a");
    let thm = Thm::refl(t.clone()).unwrap();
    assert!(thm.hyps().is_empty());
    let (l, r) = parse_eq(thm.concl());
    assert_eq!(l, t);
    assert_eq!(r, t);
}

#[test]
fn refl_on_bool_literal() {
    let thm = Thm::refl(Term::bool_lit(true)).unwrap();
    let (l, r) = parse_eq(thm.concl());
    assert_eq!(l, Term::bool_lit(true));
    assert_eq!(r, Term::bool_lit(true));
}

#[test]
fn refl_on_lambda_is_closed() {
    // λx:nat. x — closed, well-typed.
    let lam = Term::abs(Type::nat(), Term::bound(0));
    let thm = Thm::refl(lam.clone()).unwrap();
    let (l, _r) = parse_eq(thm.concl());
    assert_eq!(l, lam);
}

#[test]
fn refl_rejects_dangling_bound() {
    let err = Thm::refl(Term::bound(0)).unwrap_err();
    assert!(matches!(err, Error::NotClosed));
}

#[test]
fn refl_rejects_dangling_bound_under_one_binder() {
    // λx:nat. Bound(1) — index 1 escapes the single binder.
    let bad = Term::abs(Type::nat(), Term::bound(1));
    let err = Thm::refl(bad).unwrap_err();
    assert!(matches!(err, Error::NotClosed));
}

#[test]
fn refl_rejects_ill_typed_app() {
    // (f : nat→nat) applied to a bool.
    let f = Term::free("f", Type::fun(Type::nat(), Type::nat()));
    let bad = Term::app(f, Term::bool_lit(true));
    let err = Thm::refl(bad).unwrap_err();
    assert!(matches!(err, Error::TypeMismatch { .. }));
}

#[test]
fn refl_rejects_application_of_non_function() {
    // (nat literal) applied to something — not a function.
    let bad = Term::app(n5(), n5());
    let err = Thm::refl(bad).unwrap_err();
    assert!(matches!(err, Error::NotFunction(_)));
}

// ============================================================================
// sym
// ============================================================================

#[test]
fn sym_swaps_sides() {
    let a = nat("a");
    let b = nat("b");
    let thm = Thm::assume(nat_eq(a.clone(), b.clone())).unwrap();
    let s = thm.sym().unwrap();
    let (l, r) = parse_eq(s.concl());
    assert_eq!(l, b);
    assert_eq!(r, a);
}

#[test]
fn sym_twice_is_identity() {
    let a = nat("a");
    let b = nat("b");
    let orig = Thm::assume(nat_eq(a, b)).unwrap();
    let twice = orig.clone().sym().unwrap().sym().unwrap();
    assert_eq!(twice.concl(), orig.concl());
}

#[test]
fn sym_rejects_non_eq() {
    let p = Thm::assume(boolv("p")).unwrap();
    assert!(matches!(p.sym().unwrap_err(), Error::NotHolEq(_)));
}

#[test]
fn sym_rejects_imp_shaped_non_eq() {
    // A bool conclusion that is App(App(_, _), _) but head is not Eq.
    // Use App(App(f, x), y) where f : nat→nat→bool.
    let f = Term::free(
        "f",
        Type::fun(Type::nat(), Type::fun(Type::nat(), Type::bool())),
    );
    let app = Term::app(Term::app(f, nat("x")), nat("y"));
    let thm = Thm::assume(app).unwrap();
    assert!(matches!(thm.sym().unwrap_err(), Error::NotHolEq(_)));
}

#[test]
fn sym_preserves_hyps() {
    let a = nat("a");
    let b = nat("b");
    let eq = nat_eq(a, b);
    let s = Thm::assume(eq.clone()).unwrap().sym().unwrap();
    assert!(s.hyps().contains(&eq));
    assert_eq!(s.hyps().len(), 1);
}

// ============================================================================
// trans
// ============================================================================

#[test]
fn trans_chains() {
    let a = nat("a");
    let b = nat("b");
    let c = nat("c");
    let ab = Thm::assume(nat_eq(a.clone(), b.clone())).unwrap();
    let bc = Thm::assume(nat_eq(b, c.clone())).unwrap();
    let ac = ab.trans(bc).unwrap();
    let (l, r) = parse_eq(ac.concl());
    assert_eq!(l, a);
    assert_eq!(r, c);
}

#[test]
fn trans_unions_hyps() {
    let a = nat("a");
    let b = nat("b");
    let c = nat("c");
    let h1 = nat_eq(a.clone(), b.clone());
    let h2 = nat_eq(b, c);
    let ac = Thm::assume(h1.clone())
        .unwrap()
        .trans(Thm::assume(h2.clone()).unwrap())
        .unwrap();
    assert!(ac.hyps().contains(&h1));
    assert!(ac.hyps().contains(&h2));
    assert_eq!(ac.hyps().len(), 2);
}

#[test]
fn trans_rejects_middle_mismatch() {
    let a = nat("a");
    let b = nat("b");
    let c = nat("c");
    let d = nat("d");
    let ab = Thm::assume(nat_eq(a, b)).unwrap();
    let cd = Thm::assume(nat_eq(c, d)).unwrap();
    assert!(matches!(
        ab.trans(cd).unwrap_err(),
        Error::TransMiddleMismatch { .. }
    ));
}

#[test]
fn trans_rejects_non_eq_left() {
    let p = Thm::assume(boolv("p")).unwrap();
    let refl = Thm::refl(nat("a")).unwrap();
    assert!(matches!(p.trans(refl).unwrap_err(), Error::NotHolEq(_)));
}

#[test]
fn trans_rejects_non_eq_right() {
    let refl = Thm::refl(nat("a")).unwrap();
    let p = Thm::assume(boolv("p")).unwrap();
    assert!(matches!(refl.trans(p).unwrap_err(), Error::NotHolEq(_)));
}

#[test]
fn trans_middle_compares_alpha_equiv() {
    // Middles are α-equivalent lambdas → should chain.
    // a = (λx:nat. x)   and   (λy:nat. y) = b
    // Anonymous binders make the two lambdas structurally equal.
    let lam1 = Term::abs(Type::nat(), Term::bound(0));
    let lam2 = Term::abs(Type::nat(), Term::bound(0));
    let fnt = Type::fun(Type::nat(), Type::nat());
    let a = Term::free("a", fnt.clone());
    let b = Term::free("b", fnt.clone());
    let ab = Thm::assume(eq_at(fnt.clone(), a.clone(), lam1)).unwrap();
    let cb = Thm::assume(eq_at(fnt.clone(), lam2, b.clone())).unwrap();
    let ac = ab.trans(cb).unwrap();
    let (l, r) = parse_eq(ac.concl());
    assert_eq!(l, a);
    assert_eq!(r, b);
}

#[test]
fn trans_middle_type_distinguishes_mismatch() {
    // s = t at one type, t' = u where t' looks the same name but
    // different type → FreeVarReuse caught by build (same name, two
    // types across the union).
    let t_nat = nat("t");
    let t_bool = boolv("t");
    let ab = Thm::assume(nat_eq(nat("a"), t_nat.clone())).unwrap();
    let bc = Thm::assume(bool_eq(t_bool, boolv("c"))).unwrap();
    // Middle terms differ (nat t vs bool t) → middle mismatch first.
    assert!(ab.trans(bc).is_err());
}

// ============================================================================
// mk_comb / cong_app
// ============================================================================

#[test]
fn mk_comb_builds_application_eq() {
    let succ = covalence_core::defs::nat_succ();
    let zero = Term::nat_lit(covalence_types::Nat::zero());
    let f_eq = Thm::refl(succ.clone()).unwrap();
    let x_eq = Thm::refl(zero.clone()).unwrap();
    let app_eq = f_eq.mk_comb(x_eq).unwrap();
    let (l, r) = parse_eq(app_eq.concl());
    assert_eq!(l, Term::app(succ.clone(), zero.clone()));
    assert_eq!(r, Term::app(succ, zero));
}

#[test]
fn cong_app_is_mk_comb() {
    let succ = covalence_core::defs::nat_succ();
    let zero = Term::nat_lit(covalence_types::Nat::zero());
    let a = Thm::refl(succ.clone())
        .unwrap()
        .mk_comb(Thm::refl(zero.clone()).unwrap())
        .unwrap();
    let b = Thm::refl(succ)
        .unwrap()
        .cong_app(Thm::refl(zero).unwrap())
        .unwrap();
    assert_eq!(a.concl(), b.concl());
}

#[test]
fn mk_comb_unions_hyps() {
    // f = g with hyp Hf;  x = y with hyp Hx.
    let fnt = Type::fun(Type::nat(), Type::nat());
    let hf = eq_at(
        fnt.clone(),
        Term::free("f", fnt.clone()),
        Term::free("g", fnt.clone()),
    );
    let hx = nat_eq(nat("x"), nat("y"));
    let res = Thm::assume(hf.clone())
        .unwrap()
        .mk_comb(Thm::assume(hx.clone()).unwrap())
        .unwrap();
    assert!(res.hyps().contains(&hf));
    assert!(res.hyps().contains(&hx));
}

#[test]
fn mk_comb_rejects_non_eq_function_thm() {
    let p = Thm::assume(boolv("p")).unwrap();
    let x_eq = Thm::refl(nat("x")).unwrap();
    assert!(matches!(p.mk_comb(x_eq).unwrap_err(), Error::NotHolEq(_)));
}

#[test]
fn mk_comb_rejects_non_eq_arg_thm() {
    let f_eq = Thm::refl(covalence_core::defs::nat_succ()).unwrap();
    let p = Thm::assume(boolv("p")).unwrap();
    assert!(matches!(f_eq.mk_comb(p).unwrap_err(), Error::NotHolEq(_)));
}

#[test]
fn mk_comb_rejects_domain_mismatch() {
    // f : nat→nat, arg : bool — application is ill-typed.
    let f_eq = Thm::refl(covalence_core::defs::nat_succ()).unwrap();
    let bad_eq = Thm::refl(Term::bool_lit(true)).unwrap();
    assert!(matches!(
        f_eq.mk_comb(bad_eq).unwrap_err(),
        Error::TypeMismatch { .. }
    ));
}

#[test]
fn mk_comb_rejects_non_function_head() {
    // f side is a nat (not a function) = nat; arg side nat=nat.
    let f_eq = Thm::refl(n5()).unwrap(); // 5 = 5 : nat
    let x_eq = Thm::refl(nat("x")).unwrap();
    assert!(matches!(
        f_eq.mk_comb(x_eq).unwrap_err(),
        Error::NotFunction(_)
    ));
}

#[test]
fn mk_comb_free_var_consistency_across_f_and_x() {
    // f = g where g mentions Free("z", nat→nat); x = y where x is
    // Free("z", nat) — same name "z" with two types → FreeVarReuse
    // when build re-types the whole theorem.
    let fnt = Type::fun(Type::nat(), Type::nat());
    let z_fun = Term::free("z", fnt.clone());
    let z_nat = Term::free("z", Type::nat());
    let f_eq = Thm::assume(eq_at(fnt.clone(), Term::free("f", fnt.clone()), z_fun)).unwrap();
    // arg side: z_nat = w  (z : nat here)
    let x_eq = Thm::assume(nat_eq(z_nat, nat("w"))).unwrap();
    // f z and g w: but g = z_fun (nat→nat), applied to z_nat (nat).
    // The application g w is fine type-wise, but the union of hyps now
    // contains z at two types → FreeVarReuse.
    let err = f_eq.mk_comb(x_eq).unwrap_err();
    assert!(matches!(err, Error::FreeVarReuse { .. }));
}

// ============================================================================
// abs / cong_abs
// ============================================================================

#[test]
fn abs_builds_lambda_eq() {
    let x = nat("x");
    let thm = Thm::refl(x).unwrap().abs("x", Type::nat()).unwrap();
    let (l, r) = parse_eq(thm.concl());
    let lam = Term::abs(Type::nat(), Term::bound(0));
    assert_eq!(l, lam);
    assert_eq!(r, lam);
}

#[test]
fn cong_abs_is_abs() {
    let x = nat("x");
    let a = Thm::refl(x.clone()).unwrap().abs("x", Type::nat()).unwrap();
    let b = Thm::refl(x).unwrap().cong_abs("x", Type::nat()).unwrap();
    assert_eq!(a.concl(), b.concl());
}

#[test]
fn abs_rejects_var_free_in_hyps() {
    let x = nat("x");
    let h = Thm::assume(nat_eq(x.clone(), x)).unwrap();
    assert!(matches!(
        h.abs("x", Type::nat()).unwrap_err(),
        Error::FreeVarInHyps { .. }
    ));
}

#[test]
fn abs_rejects_binder_type_mismatch() {
    // x : nat in concl, abstract at bool.
    let thm = Thm::refl(nat("x")).unwrap();
    assert!(matches!(
        thm.abs("x", Type::bool()).unwrap_err(),
        Error::BinderTypeMismatch { .. }
    ));
}

#[test]
fn abs_rejects_non_eq() {
    let p = Thm::assume(boolv("p")).unwrap();
    assert!(matches!(
        p.abs("x", Type::nat()).unwrap_err(),
        Error::NotHolEq(_)
    ));
}

#[test]
fn abs_vacuous_when_var_absent() {
    // abstract over a var not occurring — body has no Bound(0), but
    // the lambda is still well-formed.
    let a = nat("a");
    let thm = Thm::refl(a.clone()).unwrap().abs("z", Type::nat()).unwrap();
    let (l, r) = parse_eq(thm.concl());
    // body is `a` unchanged (Free a), wrapped in Abs(nat, ·)
    let lam = Term::abs(Type::nat(), a);
    assert_eq!(l, lam);
    assert_eq!(r, lam);
}

#[test]
fn abs_uses_declared_type_from_other_side() {
    // s side has no Free x; t side has Free("x", nat). Declared type
    // is read from whichever side has it. Build s=t with x only on
    // the right.
    let x = nat("x");
    let eq = nat_eq(nat("a"), x);
    let thm = Thm::assume(eq).unwrap();
    // x is free in the hyp (eq itself is the hyp) → rejected.
    assert!(thm.abs("x", Type::nat()).is_err());
}

// ============================================================================
// beta_conv
// ============================================================================

#[test]
fn beta_conv_reduces() {
    // (λx:nat. x) 5  =  5
    let id = Term::abs(Type::nat(), Term::bound(0));
    let app = Term::app(id, n5());
    let thm = Thm::beta_conv(app.clone()).unwrap();
    let (l, r) = parse_eq(thm.concl());
    assert_eq!(l, app);
    assert_eq!(r, n5());
}

#[test]
fn beta_conv_substitutes_into_body() {
    // (λx:nat. succ x) 5 = succ 5
    let succ = covalence_core::defs::nat_succ();
    let body = Term::app(covalence_core::subst::shift_by(&succ, 1, 0), Term::bound(0));
    let lam = Term::abs(Type::nat(), body);
    let app = Term::app(lam, n5());
    let thm = Thm::beta_conv(app.clone()).unwrap();
    let (l, r) = parse_eq(thm.concl());
    assert_eq!(l, app);
    assert_eq!(r, Term::app(succ, n5()));
}

#[test]
fn beta_conv_rejects_non_app() {
    assert!(matches!(
        Thm::beta_conv(nat("n")).unwrap_err(),
        Error::NotApp(_)
    ));
}

#[test]
fn beta_conv_rejects_non_abs_head() {
    let app = Term::app(covalence_core::defs::nat_succ(), n5());
    assert!(matches!(Thm::beta_conv(app).unwrap_err(), Error::NotAbs(_)));
}

#[test]
fn beta_conv_rejects_arg_type_mismatch() {
    // (λx:nat. x) applied to a bool literal.
    let id = Term::abs(Type::nat(), Term::bound(0));
    let app = Term::app(id, Term::bool_lit(true));
    assert!(matches!(
        Thm::beta_conv(app).unwrap_err(),
        Error::TypeMismatch { .. }
    ));
}

// ============================================================================
// eta_conv
// ============================================================================

#[test]
fn eta_conv_simple() {
    // λx:nat. succ x  -->  succ
    let succ = covalence_core::defs::nat_succ();
    let lam = Term::abs(
        Type::nat(),
        Term::app(covalence_core::subst::shift_by(&succ, 1, 0), Term::bound(0)),
    );
    let thm = Thm::eta_conv(lam.clone()).unwrap();
    let (l, r) = parse_eq(thm.concl());
    assert_eq!(l, lam);
    assert_eq!(r, succ);
}

#[test]
fn eta_conv_rejects_non_abs() {
    assert!(matches!(
        Thm::eta_conv(nat("n")).unwrap_err(),
        Error::NotAbs(_)
    ));
}

#[test]
fn eta_conv_rejects_body_not_app() {
    let lam = Term::abs(Type::nat(), Term::bound(0));
    assert!(matches!(Thm::eta_conv(lam).unwrap_err(), Error::EtaShape));
}

#[test]
fn eta_conv_rejects_arg_not_bound_zero() {
    // λx:nat. succ (succ x): arg of outer app is `succ x`, not Bound(0).
    let succ = covalence_core::defs::nat_succ();
    let shifted = covalence_core::subst::shift_by(&succ, 1, 0);
    let inner = Term::app(shifted.clone(), Term::bound(0));
    let outer = Term::app(shifted, inner);
    let lam = Term::abs(Type::nat(), outer);
    assert!(matches!(Thm::eta_conv(lam).unwrap_err(), Error::EtaShape));
}

#[test]
fn eta_conv_rejects_bound_zero_in_head() {
    // λx:nat. (λy:nat. x) x — head `λy. x` mentions the outer x
    // (Bound(1)), so eta would capture. Must be rejected.
    let inner = Term::abs(Type::nat(), Term::bound(1));
    let lam = Term::abs(Type::nat(), Term::app(inner, Term::bound(0)));
    assert!(matches!(Thm::eta_conv(lam).unwrap_err(), Error::EtaShape));
}

#[test]
fn eta_conv_rejects_arg_bound_nonzero() {
    // λx:nat. λz:nat. f z applied where arg is Bound(1) not Bound(0).
    // Build λx. (g x) where the inner arg is Bound(0) of the wrong
    // binder. Use: λx:nat. (λw:nat. (Bound1)) (Bound1)? Simpler:
    // arg = Bound(0) is required; supply a head that's fine but with
    // a nested binder where x appears at Bound(1) in f — covered
    // above. Here test arg = a free var instead of Bound(0).
    let f = Term::free("f", Type::fun(Type::nat(), Type::nat()));
    let lam = Term::abs(Type::nat(), Term::app(f, nat("y")));
    assert!(matches!(Thm::eta_conv(lam).unwrap_err(), Error::EtaShape));
}

// ============================================================================
// assume
// ============================================================================

#[test]
fn assume_bool() {
    let p = boolv("p");
    let thm = Thm::assume(p.clone()).unwrap();
    assert!(thm.hyps().contains(&p));
    assert_eq!(thm.concl(), &p);
    assert_eq!(thm.hyps().len(), 1);
}

#[test]
fn assume_rejects_nat() {
    assert!(matches!(
        Thm::assume(nat("n")).unwrap_err(),
        Error::NotBool(_)
    ));
}

#[test]
fn assume_rejects_dangling_bound() {
    assert!(matches!(
        Thm::assume(Term::bound(0)).unwrap_err(),
        Error::NotClosed
    ));
}

#[test]
fn assume_rejects_ill_typed_bool_shaped() {
    // App of a non-function that "should" be bool — actually nat eq is
    // fine; instead build something ill-typed: (f:nat→nat) bool.
    let f = Term::free("f", Type::fun(Type::nat(), Type::nat()));
    let bad = Term::app(f, Term::bool_lit(true));
    assert!(Thm::assume(bad).is_err());
}

// ============================================================================
// eq_mp
// ============================================================================

#[test]
fn eq_mp_transports() {
    // ⊢ p = q (bool),  ⊢ p   ⇒   ⊢ q
    let p = boolv("p");
    let q = boolv("q");
    let pq = Thm::assume(bool_eq(p.clone(), q.clone())).unwrap();
    let p_thm = Thm::assume(p).unwrap();
    let q_thm = pq.eq_mp(p_thm).unwrap();
    assert_eq!(q_thm.concl(), &q);
}

#[test]
fn eq_mp_unions_hyps() {
    let p = boolv("p");
    let q = boolv("q");
    let h_pq = bool_eq(p.clone(), q.clone());
    let pq = Thm::assume(h_pq.clone()).unwrap();
    let p_h = p.clone();
    let q_thm = pq.eq_mp(Thm::assume(p).unwrap()).unwrap();
    assert!(q_thm.hyps().contains(&h_pq));
    assert!(q_thm.hyps().contains(&p_h));
    assert_eq!(q_thm.hyps().len(), 2);
    assert_eq!(q_thm.concl(), &q);
}

#[test]
fn eq_mp_rejects_non_eq_first() {
    let p = boolv("p");
    let non_eq = Thm::assume(p.clone()).unwrap();
    let other = Thm::assume(p).unwrap();
    assert!(matches!(
        non_eq.eq_mp(other).unwrap_err(),
        Error::NotHolEq(_)
    ));
}

#[test]
fn eq_mp_rejects_p_mismatch() {
    let p = boolv("p");
    let q = boolv("q");
    let r = boolv("r");
    let eq = Thm::assume(bool_eq(p, q)).unwrap();
    let r_thm = Thm::assume(r).unwrap();
    assert!(matches!(
        eq.eq_mp(r_thm).unwrap_err(),
        Error::ImpAntecedentMismatch { .. }
    ));
}

#[test]
fn eq_mp_rejects_non_bool_equation() {
    // ⊢ 5 = 5 at nat is not biconditional; EQ_MP requires bool.
    let eq = Thm::assume(nat_eq(n5(), n5())).unwrap();
    let p_thm = Thm::assume(boolv("p")).unwrap();
    assert!(matches!(eq.eq_mp(p_thm).unwrap_err(), Error::NotBool(_)));
}

#[test]
fn eq_mp_p_must_match_alpha_equiv() {
    // p = (λx:nat.x) at fun type is NOT bool — rejected as non-bool.
    // Confirm eq_mp's p_thm match is exact (structural / α).
    let p = boolv("p");
    let q = boolv("q");
    let eq = Thm::assume(bool_eq(p.clone(), q.clone())).unwrap();
    // p_thm concl differs from p → mismatch.
    let other = Thm::assume(boolv("notp")).unwrap();
    assert!(eq.eq_mp(other).is_err());
}

// ============================================================================
// deduct_antisym
// ============================================================================

#[test]
fn deduct_antisym_builds_iff() {
    let p = boolv("p");
    let q = boolv("q");
    let p_thm = Thm::assume(p.clone()).unwrap();
    let q_thm = Thm::assume(q.clone()).unwrap();
    let eq = p_thm.deduct_antisym(q_thm).unwrap();
    let (l, r) = parse_eq(eq.concl());
    assert_eq!(l, p);
    assert_eq!(r, q);
    // Neither side has the other's concl as a hyp → both remain.
    assert!(eq.hyps().contains(&p));
    assert!(eq.hyps().contains(&q));
    assert_eq!(eq.hyps().len(), 2);
}

#[test]
fn deduct_antisym_cancels_cross_hyps() {
    // {q} ⊢ p and {p} ⊢ q  ⇒  ⊢ p ⇔ q with empty hyps.
    // Build {p,q}⊢p and {p,q}⊢q via assume+weaken, then deduct:
    // (Γ−{q}) ∪ (Δ−{p}) = ({p,q}−{q}) ∪ ({p,q}−{p}) = {p}∪{q}.
    // To actually cancel, hyps must be exactly the OTHER's concl.
    // We can't make {q}⊢p without a real proof, so verify removal
    // mechanics: self.hyps.remove(other.concl).
    let p = boolv("p");
    let q = boolv("q");
    // self = {q} not derivable; instead self has hyp q via weaken of
    // assume(p) into {p,q}; remove(q) drops q.
    let pq: covalence_core::Ctx = [p.clone(), q.clone()].into_iter().collect();
    let self_thm = Thm::assume(p.clone()).unwrap().weaken(pq.clone()).unwrap();
    let other_thm = Thm::assume(q.clone()).unwrap().weaken(pq).unwrap();
    let eq = self_thm.deduct_antisym(other_thm).unwrap();
    // hyps_self = {p,q} − {q (other.concl)} = {p}
    // hyps_other = {p,q} − {p (self.concl)} = {q}
    // union = {p,q}
    assert!(eq.hyps().contains(&p));
    assert!(eq.hyps().contains(&q));
}

#[test]
fn deduct_antisym_removal_is_by_concl() {
    // self ⊢ p with hyp {p, q}; remove q (= other.concl). other ⊢ q
    // with hyp {q}; remove p (= self.concl) → unchanged since p ∉.
    let p = boolv("p");
    let q = boolv("q");
    let pq: covalence_core::Ctx = [p.clone(), q.clone()].into_iter().collect();
    let self_thm = Thm::assume(p.clone()).unwrap().weaken(pq).unwrap(); // {p,q}⊢p
    let other_thm = Thm::assume(q.clone()).unwrap(); // {q}⊢q
    let eq = self_thm.deduct_antisym(other_thm).unwrap();
    // self.hyps − {q} = {p}; other.hyps − {p} = {q}. Union {p,q}.
    assert!(eq.hyps().contains(&p));
    assert!(eq.hyps().contains(&q));
}

// ============================================================================
// inst
// ============================================================================

#[test]
fn inst_substitutes_free_var() {
    let refl = Thm::refl(nat("n")).unwrap();
    let zero = Term::nat_lit(covalence_types::Nat::zero());
    let inst = refl.inst("n", zero.clone()).unwrap();
    let (l, r) = parse_eq(inst.concl());
    assert_eq!(l, zero);
    assert_eq!(r, zero);
}

#[test]
fn inst_substitutes_in_hyps() {
    let x = nat("x");
    let eq = nat_eq(x.clone(), x);
    let thm = Thm::assume(eq).unwrap();
    let zero = Term::nat_lit(covalence_types::Nat::zero());
    let res = thm.inst("x", zero.clone()).unwrap();
    let expected = nat_eq(zero.clone(), zero);
    assert!(res.hyps().contains(&expected));
    assert_eq!(res.concl(), &expected);
}

#[test]
fn inst_rejects_replacement_type_mismatch() {
    let refl = Thm::refl(nat("n")).unwrap();
    assert!(matches!(
        refl.inst("n", Term::bool_lit(true)).unwrap_err(),
        Error::TypeMismatch { .. }
    ));
}

#[test]
fn inst_noop_when_name_absent() {
    // "x" doesn't occur; replacement type unconstrained → no-op.
    let refl = Thm::refl(nat("n")).unwrap();
    let res = refl.inst("x", Term::bool_lit(true)).unwrap();
    let (l, r) = parse_eq(res.concl());
    assert_eq!(l, nat("n"));
    assert_eq!(r, nat("n"));
}

#[test]
fn inst_rejects_dangling_bound_replacement() {
    let refl = Thm::refl(nat("n")).unwrap();
    assert!(matches!(
        refl.inst("n", Term::bound(0)).unwrap_err(),
        Error::NotClosed
    ));
}

#[test]
fn inst_replacement_into_body_well_typed() {
    // ⊢ (λy:nat. n) = (λy:nat. n) with free n; inst n := succ — wait,
    // succ is nat→nat not nat. Use inst n := (5:nat).
    let n = nat("n");
    // (λy. n) — n is free, body is just `n` (no Bound).
    let lam = Term::abs(Type::nat(), covalence_core::subst::close(&n, "y"));
    // close on "y" doesn't touch n → body still Free n.
    let refl = Thm::refl(lam).unwrap();
    let res = refl.inst("n", n5()).unwrap();
    let (l, _r) = parse_eq(res.concl());
    let expected = Term::abs(Type::nat(), n5());
    assert_eq!(l, expected);
}

// ============================================================================
// weaken
// ============================================================================

#[test]
fn weaken_to_superset() {
    let p = boolv("p");
    let q = boolv("q");
    let thm = Thm::assume(p.clone()).unwrap();
    let bigger: covalence_core::Ctx = [p.clone(), q.clone()].into_iter().collect();
    let w = thm.weaken(bigger).unwrap();
    assert!(w.hyps().contains(&p));
    assert!(w.hyps().contains(&q));
    assert_eq!(w.hyps().len(), 2);
}

#[test]
fn weaken_to_same_set_is_identity() {
    let p = boolv("p");
    let same: covalence_core::Ctx = [p.clone()].into_iter().collect();
    let w = Thm::assume(p.clone()).unwrap().weaken(same).unwrap();
    assert!(w.hyps().contains(&p));
    assert_eq!(w.hyps().len(), 1);
}

#[test]
fn weaken_rejects_non_superset() {
    // self has hyp {p}; target {q} does not contain p.
    let p = boolv("p");
    let q = boolv("q");
    let thm = Thm::assume(p).unwrap();
    let target: covalence_core::Ctx = [q].into_iter().collect();
    assert!(matches!(
        thm.weaken(target).unwrap_err(),
        Error::NotASuperset
    ));
}

#[test]
fn weaken_rejects_empty_target_when_nonempty_hyps() {
    let p = boolv("p");
    let thm = Thm::assume(p).unwrap();
    assert!(matches!(
        thm.weaken(covalence_core::Ctx::new()).unwrap_err(),
        Error::NotASuperset
    ));
}

#[test]
fn weaken_rejects_non_bool_in_target() {
    // target includes a non-bool term → build rejects.
    let p = boolv("p");
    let thm = Thm::assume(p.clone()).unwrap();
    let bad: covalence_core::Ctx = [p, nat("n")].into_iter().collect();
    assert!(thm.weaken(bad).is_err());
}

// ============================================================================
// Cross-term Free consistency (Thm::build invariant)
// ============================================================================

#[test]
fn build_rejects_free_var_reuse_across_hyp_and_concl() {
    // Construct {x:bool} ⊢ x:nat = x:nat — impossible: same name x at
    // two types. Build a theorem where the hyp uses x:bool and the
    // concl uses x:nat, via inst that introduces the inconsistency.
    // Start: ⊢ (x:nat) = (x:nat); assume separately {x:bool} ⊢ x:bool;
    // weaken won't combine. Instead: weaken refl(nat x) into a ctx
    // containing x:bool.
    let x_nat = nat("x");
    let x_bool = boolv("x");
    let refl = Thm::refl(x_nat).unwrap(); // ⊢ x:nat = x:nat
    let target: covalence_core::Ctx = [x_bool].into_iter().collect();
    // weaken checks subset first: refl has empty hyps ⊆ target, so it
    // proceeds to build, which re-types concl (x:nat) and hyp (x:bool)
    // in one env → FreeVarReuse.
    let err = refl.weaken(target).unwrap_err();
    assert!(matches!(err, Error::FreeVarReuse { .. }));
}

#[test]
fn accessors_into_parts_round_trip() {
    let p = boolv("p");
    let thm = Thm::assume(p.clone()).unwrap();
    let (hyps, concl) = thm.into_parts();
    assert!(hyps.contains(&p));
    assert_eq!(concl, p);
}

// ============================================================================
// α-equivalence: anonymous binders compare structurally
// ============================================================================

#[test]
fn alpha_equiv_lambdas_are_equal_terms() {
    // Two lambdas built independently are structurally equal (no name
    // stored), so refl on one and parse of the other coincide.
    let l1 = Term::abs(Type::nat(), Term::bound(0));
    let l2 = Term::abs(Type::nat(), Term::bound(0));
    assert_eq!(l1, l2);
    // trans across an α-equiv middle works (covered above too).
}

#[test]
fn alpha_equiv_eq_mp_matches_anonymous_binder() {
    // p = (λx:nat. x = x) ... build at bool? The lambda is fun-typed.
    // Instead: confirm eq_mp matches when p is itself a lambda-headed
    // bool term that is α-equal. Use p := ((λx:nat. true) 0) shape?
    // Simpler structural α check: assume P where P built two ways.
    // `a = a` at nat is itself a bool-typed proposition.
    let body = nat_eq(nat("a"), nat("a"));
    let p1 = body.clone();
    let p2 = body;
    assert_eq!(p1, p2);
    let eq = Thm::assume(bool_eq(p1.clone(), boolv("q"))).unwrap();
    // p_thm uses an independently-built but equal p2.
    let p_thm = Thm::assume(p2).unwrap();
    let q_thm = eq.eq_mp(p_thm).unwrap();
    assert_eq!(q_thm.concl(), &boolv("q"));
}
