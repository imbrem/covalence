//! Exhaustive edge-case audit of the HOL connective + quantifier
//! inference rules in `covalence_core::thm`:
//!
//! `imp_intro`, `imp_elim`, `all_intro`, `all_elim`, `and_intro`,
//! `and_elim_l`, `and_elim_r`, `or_intro_l`, `or_intro_r`, `or_elim`,
//! `not_intro`, `not_elim`.
//!
//! The connectives `∧ ∨ ¬ ⟹` are *defined constants* in
//! `covalence_core::defs::logic`; the quantifiers `∀ ∃` are
//! polymorphic specs. These tests build the connective application
//! shapes by hand (the way `crate::hol` does internally) and feed both
//! well-formed and malformed shapes through the kernel rules, asserting
//! acceptance / rejection and inspecting hypothesis bookkeeping.
//!
//! This is an external (integration-test) crate, so it sees only the
//! public API.

use covalence_core::defs;
use covalence_core::subst::close;
use covalence_core::{Error, Term, TermKind, Thm, Type};

// ============================================================================
// Term-builder helpers (mirror `covalence_core::hol`, public-API-only)
// ============================================================================

fn b() -> Type {
    Type::bool()
}

fn nat() -> Type {
    Type::nat()
}

/// A fresh `bool`-typed free variable.
fn pvar(name: &str) -> Term {
    Term::free(name, b())
}

/// `p ∧ q` via the `and` defined constant.
fn and(p: Term, q: Term) -> Term {
    Term::app(Term::app(defs::and(), p), q)
}

/// `p ∨ q`.
fn or(p: Term, q: Term) -> Term {
    Term::app(Term::app(defs::or(), p), q)
}

/// `p ⟹ q`.
fn imp(p: Term, q: Term) -> Term {
    Term::app(Term::app(defs::imp(), p), q)
}

/// `¬p`.
fn not(p: Term) -> Term {
    Term::app(defs::not(), p)
}

/// `iff p q` (`p ⟺ q`) — used as a *non-`imp`* binary connective to
/// probe shape recognition.
fn iff(p: Term, q: Term) -> Term {
    Term::app(Term::app(defs::iff(), p), q)
}

/// HOL `lhs = rhs : bool` at element type `ty`.
fn eq(ty: Type, lhs: Term, rhs: Term) -> Term {
    Term::app(Term::app(Term::eq_op(ty), lhs), rhs)
}

/// `∀x:ty. body` where `body` mentions `Free("x", ty)`.
fn forall(ty: Type, body: Term) -> Term {
    let lambda = Term::abs(ty.clone(), close(&body, "x"));
    Term::app(defs::forall(ty), lambda)
}

/// `T` / `F`.
fn t() -> Term {
    Term::bool_lit(true)
}
fn f() -> Term {
    Term::bool_lit(false)
}

/// `{p} ⊢ p`.
fn assume(p: Term) -> Thm {
    Thm::assume(p).expect("assume bool-typed term")
}

// ----------------------------------------------------------------------------
// Conclusion-shape walkers (public API: walk `TermKind::App`)
// ----------------------------------------------------------------------------

/// Decompose `App(App(head, p), q)` into `(p, q)`, ignoring the head.
fn binop_args(t: &Term) -> (Term, Term) {
    let TermKind::App(f, q) = t.kind() else {
        panic!("not a binary application: {t}");
    };
    let TermKind::App(_head, p) = f.kind() else {
        panic!("not a binary application: {t}");
    };
    (p.clone(), q.clone())
}

/// Check that `t`'s head spec is the catalogue spec `want` (pointer
/// identity, via the public `TermSpec::ptr_eq`).
fn binop_head_is(t: &Term, want: &covalence_core::TermSpec) -> bool {
    let TermKind::App(f, _q) = t.kind() else {
        return false;
    };
    let TermKind::App(head, _p) = f.kind() else {
        return false;
    };
    matches!(head.kind(), TermKind::Spec(h, _) if h.ptr_eq(want))
}

fn unop_arg(t: &Term) -> Term {
    let TermKind::App(_head, p) = t.kind() else {
        panic!("not a unary application: {t}");
    };
    p.clone()
}

// ============================================================================
// imp_intro (DISCH)
// ============================================================================

#[test]
fn imp_intro_discharges_the_named_hyp() {
    // {p} ⊢ p  --imp_intro p-->  ⊢ p ⟹ p
    let p = pvar("p");
    let thm = assume(p.clone()).imp_intro(&p).expect("imp_intro");
    assert!(thm.hyps().is_empty(), "p must be discharged");
    assert!(binop_head_is(thm.concl(), &defs::imp_spec()));
    let (lhs, rhs) = binop_args(thm.concl());
    assert_eq!(lhs, p);
    assert_eq!(rhs, p);
}

#[test]
fn imp_intro_only_removes_the_named_hyp() {
    // {p, q} ⊢ q  --imp_intro p-->  {q} ⊢ p ⟹ q
    let p = pvar("p");
    let q = pvar("q");
    let pq: covalence_core::Ctx = [p.clone(), q.clone()].into_iter().collect();
    let q_thm = assume(q.clone()).weaken(pq).unwrap();
    let thm = q_thm.imp_intro(&p).unwrap();
    assert!(!thm.hyps().contains(&p), "p removed");
    assert!(thm.hyps().contains(&q), "q retained");
}

#[test]
fn imp_intro_absent_antecedent_is_weakening() {
    // ⊢ p  with q ∉ hyps  -->  ⊢ q ⟹ p, p stays a hyp here since
    // assume(p) keeps {p}; q is unrelated so nothing is removed.
    let p = pvar("p");
    let q = pvar("q");
    let thm = assume(p.clone()).imp_intro(&q).expect("imp_intro");
    assert!(thm.hyps().contains(&p));
    let (lhs, rhs) = binop_args(thm.concl());
    assert_eq!(lhs, q);
    assert_eq!(rhs, p);
}

#[test]
fn imp_intro_rejects_nat_antecedent() {
    let p = pvar("p");
    let bad = Term::free("n", nat());
    let err = assume(p).imp_intro(&bad).unwrap_err();
    assert!(matches!(err, Error::NotBool(_)));
}

#[test]
fn imp_intro_rejects_open_antecedent() {
    // Bound(0) outside any binder is open; `type_of` fails.
    let p = pvar("p");
    let err = assume(p).imp_intro(&Term::bound(0)).unwrap_err();
    assert!(matches!(err, Error::NotClosed));
}

#[test]
fn imp_intro_chains_right_associatively() {
    // {p, q} ⊢ q, discharge q then p: ⊢ p ⟹ (q ⟹ q)
    let p = pvar("p");
    let q = pvar("q");
    let pq: covalence_core::Ctx = [p.clone(), q.clone()].into_iter().collect();
    let q_thm = assume(q.clone()).weaken(pq).unwrap();
    let inner = q_thm.imp_intro(&q).unwrap(); // {p} ⊢ q ⟹ q
    let outer = inner.imp_intro(&p).unwrap(); // ⊢ p ⟹ (q ⟹ q)
    assert!(outer.hyps().is_empty());
    let (lhs, rhs) = binop_args(outer.concl());
    assert_eq!(lhs, p);
    assert!(binop_head_is(&rhs, &defs::imp_spec()));
}

// ============================================================================
// imp_elim (MP)
// ============================================================================

#[test]
fn imp_elim_modus_ponens() {
    let p = pvar("p");
    let q = pvar("q");
    let imp_thm = assume(imp(p.clone(), q.clone()));
    let result = imp_thm.imp_elim(assume(p)).expect("imp_elim");
    assert_eq!(result.concl(), &q);
}

#[test]
fn imp_elim_unions_hyps() {
    let p = pvar("p");
    let q = pvar("q");
    let extra = pvar("extra");
    let imp_body = imp(p.clone(), q.clone());
    let bigger: covalence_core::Ctx = [imp_body.clone(), extra.clone()].into_iter().collect();
    let imp_thm = assume(imp_body.clone()).weaken(bigger).unwrap();
    let result = imp_thm.imp_elim(assume(p.clone())).unwrap();
    // Hyp set is the union of both inputs' hyps: {p⟹q, extra} ∪ {p}.
    // `q` is the *conclusion*, not a hyp.
    assert!(result.hyps().contains(&imp_body));
    assert!(result.hyps().contains(&extra));
    assert!(result.hyps().contains(&p));
    assert!(!result.hyps().contains(&q));
}

#[test]
fn imp_elim_rejects_non_imp_conclusion() {
    // A bare assumption `⊢ p` is not an implication.
    let p = pvar("p");
    let err = assume(p.clone()).imp_elim(assume(p)).unwrap_err();
    assert!(matches!(err, Error::NotHolImp(_)));
}

#[test]
fn imp_elim_rejects_iff_shaped_conclusion() {
    // `p ⟺ q` has an `iff` head, not `imp` — must be rejected even
    // though both are binary bool connectives.
    let p = pvar("p");
    let q = pvar("q");
    let iff_thm = assume(iff(p.clone(), q));
    let err = iff_thm.imp_elim(assume(p)).unwrap_err();
    assert!(matches!(err, Error::NotHolImp(_)));
}

#[test]
fn imp_elim_rejects_and_shaped_conclusion() {
    let p = pvar("p");
    let q = pvar("q");
    let and_thm = assume(and(p.clone(), q));
    let err = and_thm.imp_elim(assume(p)).unwrap_err();
    assert!(matches!(err, Error::NotHolImp(_)));
}

#[test]
fn imp_elim_rejects_antecedent_mismatch() {
    let p = pvar("p");
    let q = pvar("q");
    let r = pvar("r");
    let imp_thm = assume(imp(p, q));
    let err = imp_thm.imp_elim(assume(r)).unwrap_err();
    assert!(matches!(err, Error::ImpAntecedentMismatch { .. }));
}

#[test]
fn imp_intro_imp_elim_round_trip() {
    let p = pvar("p");
    let imp_thm = assume(p.clone()).imp_intro(&p).unwrap();
    let recovered = imp_thm.imp_elim(assume(p.clone())).unwrap();
    assert_eq!(recovered.concl(), &p);
}

// ============================================================================
// all_intro (GEN)
// ============================================================================

#[test]
fn all_intro_generalises_free_var() {
    // ⊢ x = x : bool  --all_intro x:nat-->  ⊢ ∀x:nat. x = x
    let x = Term::free("x", nat());
    let refl = Thm::refl(x).unwrap();
    let univ = refl.all_intro("x", nat()).expect("all_intro");
    assert!(univ.hyps().is_empty());
    // The conclusion's head is the `forall` spec.
    let TermKind::App(head, lambda) = univ.concl().kind() else {
        panic!("forall concl not an application");
    };
    assert!(matches!(head.kind(), TermKind::Spec(h, _) if h.ptr_eq(&defs::forall_spec())));
    let TermKind::Abs(ty, _body) = lambda.kind() else {
        panic!("forall body not a lambda");
    };
    assert_eq!(ty, &nat());
}

#[test]
fn all_intro_rejects_var_free_in_hyps() {
    // {x = x} ⊢ x = x — generalising over `x` violates the GEN side
    // condition.
    let x = Term::free("x", nat());
    let h = eq(nat(), x.clone(), x);
    let thm = assume(h);
    let err = thm.all_intro("x", nat()).unwrap_err();
    assert!(matches!(err, Error::FreeVarInHyps { .. }));
}

#[test]
fn all_intro_rejects_binder_type_mismatch() {
    // `x : nat` in the conclusion, but generalise at `bool`.
    let x = Term::free("x", nat());
    let refl = Thm::refl(x).unwrap();
    let err = refl.all_intro("x", b()).unwrap_err();
    assert!(matches!(err, Error::BinderTypeMismatch { .. }));
}

#[test]
fn all_intro_vacuous_when_var_absent() {
    // `x` does not occur free; generalisation is vacuous but valid.
    let p = pvar("p");
    let refl = Thm::refl(p).unwrap();
    let univ = refl.all_intro("x", nat()).expect("vacuous gen");
    let TermKind::App(_head, lambda) = univ.concl().kind() else {
        panic!("not forall");
    };
    let TermKind::Abs(ty, _) = lambda.kind() else {
        panic!("not lambda");
    };
    assert_eq!(ty, &nat());
}

#[test]
fn all_intro_rejected_even_with_extra_unrelated_hyp() {
    // {q, x = x} ⊢ x = x — `x` occurs free in the `x = x` hyp, so GEN
    // over `x` MUST be rejected regardless of the extra `q` hyp. (The
    // self-hyp from `assume` always carries the conclusion, so any
    // free var of the conclusion is also a free var of a hyp.)
    let x = Term::free("x", nat());
    let q = pvar("q");
    let concl = eq(nat(), x.clone(), x);
    let big: covalence_core::Ctx = [q.clone(), concl.clone()].into_iter().collect();
    let thm = assume(concl).weaken(big).unwrap();
    let err = thm.all_intro("x", nat()).unwrap_err();
    assert!(matches!(err, Error::FreeVarInHyps { .. }));
}

#[test]
fn all_intro_succeeds_when_var_only_in_concl() {
    // Build ⊢ x = x with NO hyps (refl), then generalise.
    let x = Term::free("x", nat());
    let refl = Thm::refl(x).unwrap(); // ⊢ x = x, empty hyps
    assert!(refl.hyps().is_empty());
    let univ = refl.all_intro("x", nat()).unwrap();
    assert!(univ.hyps().is_empty());
}

// ============================================================================
// all_elim (SPEC)
// ============================================================================

#[test]
fn all_elim_instantiates_witness() {
    // ⊢ ∀x:nat. x = x  --[5]-->  ⊢ 5 = 5
    let x = Term::free("x", nat());
    let univ = Thm::refl(x).unwrap().all_intro("x", nat()).unwrap();
    let five = Term::nat_lit(5u32);
    let inst = univ.all_elim(five.clone()).expect("all_elim");
    let (lhs, rhs) = binop_args(inst.concl());
    assert_eq!(lhs, five);
    assert_eq!(rhs, five);
}

#[test]
fn all_elim_rejects_non_forall() {
    let p = pvar("p");
    let err = assume(p).all_elim(Term::nat_lit(0u32)).unwrap_err();
    assert!(matches!(err, Error::NotHolForall(_)));
}

#[test]
fn all_elim_rejects_witness_type_mismatch() {
    let x = Term::free("x", nat());
    let univ = Thm::refl(x).unwrap().all_intro("x", nat()).unwrap();
    let err = univ.all_elim(t()).unwrap_err(); // bool witness for nat ∀
    assert!(matches!(err, Error::TypeMismatch { .. }));
}

#[test]
fn all_elim_rejects_open_witness() {
    let x = Term::free("x", nat());
    let univ = Thm::refl(x).unwrap().all_intro("x", nat()).unwrap();
    let err = univ.all_elim(Term::bound(0)).unwrap_err();
    assert!(matches!(err, Error::NotClosed));
}

#[test]
fn gen_spec_round_trips() {
    let x = Term::free("x", nat());
    let refl = Thm::refl(x.clone()).unwrap();
    let univ = refl.clone().all_intro("x", nat()).unwrap();
    let recovered = univ.all_elim(x).unwrap();
    assert_eq!(recovered.concl(), refl.concl());
}

#[test]
fn all_elim_preserves_hyps() {
    // {q} ⊢ ∀x:nat. x = x  --[7]-->  {q} ⊢ 7 = 7. Build the closed ∀
    // term and assume it directly (a closed ∀ has no free `x`).
    let q = pvar("q");
    let univ_term = forall(nat(), {
        let xf = Term::free("x", nat());
        eq(nat(), xf.clone(), xf)
    });
    let big: covalence_core::Ctx = [q.clone(), univ_term.clone()].into_iter().collect();
    let univ = assume(univ_term).weaken(big).unwrap();
    let inst = univ.all_elim(Term::nat_lit(7u32)).unwrap();
    assert!(inst.hyps().contains(&q));
}

// ============================================================================
// and_intro (CONJ)
// ============================================================================

#[test]
fn and_intro_builds_conjunction() {
    let p = pvar("p");
    let q = pvar("q");
    let thm = assume(p.clone())
        .and_intro(assume(q.clone()))
        .expect("and_intro");
    assert!(binop_head_is(thm.concl(), &defs::and_spec()));
    let (lhs, rhs) = binop_args(thm.concl());
    assert_eq!(lhs, p);
    assert_eq!(rhs, q);
}

#[test]
fn and_intro_unions_hyps() {
    let p = pvar("p");
    let q = pvar("q");
    let thm = assume(p.clone()).and_intro(assume(q.clone())).unwrap();
    assert!(thm.hyps().contains(&p));
    assert!(thm.hyps().contains(&q));
}

#[test]
fn and_intro_accepts_literals() {
    // ⊢ T ∧ T after and_intro of two `T` assumptions.
    let thm = assume(t()).and_intro(assume(t())).unwrap();
    let (lhs, rhs) = binop_args(thm.concl());
    assert_eq!(lhs, t());
    assert_eq!(rhs, t());
}

// Note: both inputs come from `Thm` values, which are already
// guaranteed bool-typed by `Thm::build`. The explicit `NotBool` checks
// in `and_intro` are defense-in-depth and not reachable from a
// well-formed `Thm`; we therefore cannot exercise that rejection path
// through the public API. (Same for or_intro / and's bool checks.)

// ============================================================================
// and_elim_l / and_elim_r (CONJUNCT1 / CONJUNCT2)
// ============================================================================

#[test]
fn and_elim_l_projects_left() {
    let p = pvar("p");
    let q = pvar("q");
    let conj = assume(and(p.clone(), q));
    let left = conj.and_elim_l().expect("and_elim_l");
    assert_eq!(left.concl(), &p);
}

#[test]
fn and_elim_r_projects_right() {
    let p = pvar("p");
    let q = pvar("q");
    let conj = assume(and(p, q.clone()));
    let right = conj.and_elim_r().expect("and_elim_r");
    assert_eq!(right.concl(), &q);
}

#[test]
fn and_elim_preserves_hyps() {
    // The conjunction itself is the hyp; the projection keeps it.
    let p = pvar("p");
    let q = pvar("q");
    let conj_term = and(p.clone(), q);
    let conj = assume(conj_term.clone());
    let left = conj.and_elim_l().unwrap();
    assert!(left.hyps().contains(&conj_term));
}

#[test]
fn and_elim_l_rejects_non_conjunction() {
    let p = pvar("p");
    let err = assume(p).and_elim_l().unwrap_err();
    assert!(matches!(err, Error::ConnectiveRule(_)));
}

#[test]
fn and_elim_r_rejects_non_conjunction() {
    let p = pvar("p");
    let err = assume(p).and_elim_r().unwrap_err();
    assert!(matches!(err, Error::ConnectiveRule(_)));
}

#[test]
fn and_elim_rejects_disjunction_shape() {
    // `p ∨ q` is binary but has the `or` head, not `and`. CONJUNCT1
    // must reject it — otherwise it would unsoundly extract `p` from
    // `p ∨ q`.
    let p = pvar("p");
    let q = pvar("q");
    let err = assume(or(p, q)).and_elim_l().unwrap_err();
    assert!(matches!(err, Error::ConnectiveRule(_)));
}

#[test]
fn and_elim_rejects_implication_shape() {
    let p = pvar("p");
    let q = pvar("q");
    let err = assume(imp(p, q)).and_elim_l().unwrap_err();
    assert!(matches!(err, Error::ConnectiveRule(_)));
}

#[test]
fn and_intro_then_elim_round_trips() {
    let p = pvar("p");
    let q = pvar("q");
    let conj = assume(p.clone()).and_intro(assume(q.clone())).unwrap();
    assert_eq!(conj.clone().and_elim_l().unwrap().concl(), &p);
    assert_eq!(conj.and_elim_r().unwrap().concl(), &q);
}

// ============================================================================
// or_intro_l / or_intro_r (DISJ1 / DISJ2)
// ============================================================================

#[test]
fn or_intro_l_builds_disjunction() {
    // ⊢ p  --or_intro_l q-->  ⊢ p ∨ q
    let p = pvar("p");
    let q = pvar("q");
    let thm = assume(p.clone()).or_intro_l(q.clone()).expect("or_intro_l");
    assert!(binop_head_is(thm.concl(), &defs::or_spec()));
    let (lhs, rhs) = binop_args(thm.concl());
    assert_eq!(lhs, p);
    assert_eq!(rhs, q);
}

#[test]
fn or_intro_r_builds_disjunction() {
    // ⊢ q  --or_intro_r p-->  ⊢ p ∨ q
    let p = pvar("p");
    let q = pvar("q");
    let thm = assume(q.clone()).or_intro_r(p.clone()).expect("or_intro_r");
    let (lhs, rhs) = binop_args(thm.concl());
    assert_eq!(lhs, p);
    assert_eq!(rhs, q);
}

#[test]
fn or_intro_l_preserves_hyps() {
    let p = pvar("p");
    let q = pvar("q");
    let thm = assume(p.clone()).or_intro_l(q).unwrap();
    assert!(thm.hyps().contains(&p));
}

#[test]
fn or_intro_l_rejects_nat_other_disjunct() {
    // The supplied other disjunct must be bool.
    let p = pvar("p");
    let bad = Term::free("n", nat());
    let err = assume(p).or_intro_l(bad).unwrap_err();
    assert!(matches!(err, Error::NotBool(_)));
}

#[test]
fn or_intro_r_rejects_nat_other_disjunct() {
    let q = pvar("q");
    let bad = Term::free("n", nat());
    let err = assume(q).or_intro_r(bad).unwrap_err();
    assert!(matches!(err, Error::NotBool(_)));
}

#[test]
fn or_intro_l_rejects_open_other_disjunct() {
    let p = pvar("p");
    let err = assume(p).or_intro_l(Term::bound(0)).unwrap_err();
    assert!(matches!(err, Error::NotClosed));
}

// ============================================================================
// or_elim (DISJ_CASES)
// ============================================================================

#[test]
fn or_elim_combines_branches() {
    // ⊢ p ∨ q, ⊢ p ⟹ r, ⊢ q ⟹ r  ⇒  ⊢ r
    let p = pvar("p");
    let q = pvar("q");
    let r = pvar("r");
    let disj = assume(or(p.clone(), q.clone()));
    let left = assume(imp(p, r.clone()));
    let right = assume(imp(q, r.clone()));
    let result = disj.or_elim(left, right).expect("or_elim");
    assert_eq!(result.concl(), &r);
}

#[test]
fn or_elim_unions_all_three_hyp_sets() {
    let p = pvar("p");
    let q = pvar("q");
    let r = pvar("r");
    let disj_term = or(p.clone(), q.clone());
    let left_term = imp(p.clone(), r.clone());
    let right_term = imp(q.clone(), r.clone());
    let disj = assume(disj_term.clone());
    let left = assume(left_term.clone());
    let right = assume(right_term.clone());
    let result = disj.or_elim(left, right).unwrap();
    assert!(result.hyps().contains(&disj_term));
    assert!(result.hyps().contains(&left_term));
    assert!(result.hyps().contains(&right_term));
}

#[test]
fn or_elim_rejects_non_disjunction() {
    let p = pvar("p");
    let q = pvar("q");
    let r = pvar("r");
    // self is `p ∧ q`, not a disjunction.
    let bad = assume(and(p.clone(), q.clone()));
    let left = assume(imp(p, r.clone()));
    let right = assume(imp(q, r));
    let err = bad.or_elim(left, right).unwrap_err();
    assert!(matches!(err, Error::ConnectiveRule(_)));
}

#[test]
fn or_elim_rejects_non_imp_left_branch() {
    let p = pvar("p");
    let q = pvar("q");
    let r = pvar("r");
    let disj = assume(or(p.clone(), q.clone()));
    let bad_left = assume(r.clone()); // not an implication
    let right = assume(imp(q, r));
    let err = disj.or_elim(bad_left, right).unwrap_err();
    assert!(matches!(err, Error::NotHolImp(_)));
}

#[test]
fn or_elim_rejects_left_antecedent_mismatch() {
    // left branch is `s ⟹ r` but the left disjunct is `p` (s ≠ p).
    let p = pvar("p");
    let q = pvar("q");
    let r = pvar("r");
    let s = pvar("s");
    let disj = assume(or(p, q.clone()));
    let left = assume(imp(s, r.clone())); // wrong antecedent
    let right = assume(imp(q, r));
    let err = disj.or_elim(left, right).unwrap_err();
    assert!(matches!(err, Error::ConnectiveRule(_)));
}

#[test]
fn or_elim_rejects_right_antecedent_mismatch() {
    let p = pvar("p");
    let q = pvar("q");
    let r = pvar("r");
    let s = pvar("s");
    let disj = assume(or(p.clone(), q));
    let left = assume(imp(p, r.clone()));
    let right = assume(imp(s, r)); // wrong antecedent
    let err = disj.or_elim(left, right).unwrap_err();
    assert!(matches!(err, Error::ConnectiveRule(_)));
}

#[test]
fn or_elim_rejects_consequent_mismatch() {
    // Both branches well-formed but with different consequents r vs r2.
    let p = pvar("p");
    let q = pvar("q");
    let r = pvar("r");
    let r2 = pvar("r2");
    let disj = assume(or(p.clone(), q.clone()));
    let left = assume(imp(p, r));
    let right = assume(imp(q, r2));
    let err = disj.or_elim(left, right).unwrap_err();
    assert!(matches!(err, Error::ConnectiveRule(_)));
}

#[test]
fn or_intro_or_elim_round_trip() {
    // ⊢ p, weaken to p∨q, eliminate with two identity branches ⇒ ⊢ r.
    let p = pvar("p");
    let q = pvar("q");
    let r = pvar("r");
    let disj = assume(p.clone()).or_intro_l(q.clone()).unwrap(); // ⊢ p ∨ q
    let left = assume(imp(p, r.clone()));
    let right = assume(imp(q, r.clone()));
    let result = disj.or_elim(left, right).unwrap();
    assert_eq!(result.concl(), &r);
}

// ============================================================================
// not_intro (NOT_INTRO)
// ============================================================================

#[test]
fn not_intro_folds_imp_false() {
    // ⊢ p ⟹ F  --not_intro-->  ⊢ ¬p
    let p = pvar("p");
    let thm = assume(imp(p.clone(), f())).not_intro().expect("not_intro");
    assert!(matches!(thm.concl().kind(), TermKind::App(head, _)
        if matches!(head.kind(), TermKind::Spec(h, _) if h.ptr_eq(&defs::not_spec()))));
    assert_eq!(unop_arg(thm.concl()), p);
}

#[test]
fn not_intro_preserves_hyps() {
    let p = pvar("p");
    let imp_term = imp(p, f());
    let thm = assume(imp_term.clone()).not_intro().unwrap();
    assert!(thm.hyps().contains(&imp_term));
}

#[test]
fn not_intro_rejects_non_imp() {
    let p = pvar("p");
    let err = assume(p).not_intro().unwrap_err();
    assert!(matches!(err, Error::NotHolImp(_)));
}

#[test]
fn not_intro_rejects_consequent_not_false() {
    // `p ⟹ q` (q ≠ F) — the consequent isn't `F`, so NOT_INTRO must
    // reject. Otherwise it would unsoundly conclude `¬p` from `p ⟹ q`.
    let p = pvar("p");
    let q = pvar("q");
    let err = assume(imp(p, q)).not_intro().unwrap_err();
    assert!(matches!(err, Error::ConnectiveRule(_)));
}

#[test]
fn not_intro_rejects_consequent_true() {
    // `p ⟹ T` — consequent is `T`, not `F`. Reject.
    let p = pvar("p");
    let err = assume(imp(p, t())).not_intro().unwrap_err();
    assert!(matches!(err, Error::ConnectiveRule(_)));
}

// ============================================================================
// not_elim (NOT_ELIM)
// ============================================================================

#[test]
fn not_elim_yields_false() {
    // ⊢ ¬p, ⊢ p  ⇒  ⊢ F
    let p = pvar("p");
    let result = assume(not(p.clone()))
        .not_elim(assume(p))
        .expect("not_elim");
    assert_eq!(result.concl(), &f());
}

#[test]
fn not_elim_unions_hyps() {
    let p = pvar("p");
    let not_term = not(p.clone());
    let result = assume(not_term.clone())
        .not_elim(assume(p.clone()))
        .unwrap();
    assert!(result.hyps().contains(&not_term));
    assert!(result.hyps().contains(&p));
}

#[test]
fn not_elim_rejects_non_negation() {
    // self isn't `¬…`.
    let p = pvar("p");
    let err = assume(p.clone()).not_elim(assume(p)).unwrap_err();
    assert!(matches!(err, Error::ConnectiveRule(_)));
}

#[test]
fn not_elim_rejects_mismatched_hypothesis() {
    // ⊢ ¬p but supply ⊢ q (q ≠ p).
    let p = pvar("p");
    let q = pvar("q");
    let err = assume(not(p)).not_elim(assume(q)).unwrap_err();
    assert!(matches!(err, Error::ConnectiveRule(_)));
}

#[test]
fn not_intro_not_elim_round_trip() {
    // From ⊢ p ⟹ F, NOT_INTRO to ¬p, then NOT_ELIM with ⊢ p back to F.
    let p = pvar("p");
    let neg = assume(imp(p.clone(), f())).not_intro().unwrap(); // ⊢ ¬p (hyp: p⟹F)
    let result = neg.not_elim(assume(p)).unwrap();
    assert_eq!(result.concl(), &f());
}

// ============================================================================
// Cross-connective shape-confusion guards
// ============================================================================

#[test]
fn not_elim_rejects_and_head_unary_lookalike() {
    // `and` partially applied: `and p` is a unary application whose
    // head is `and`, not `not`. not_elim must reject (parse_hol_not
    // checks the spec head).
    let p = pvar("p");
    // `and p` : bool → bool, not bool — assume would reject it. So
    // instead confirm a `¬`-shaped term with a *different* spec head
    // (here `iff p q` is binary, won't even reach the unary parse).
    let q = pvar("q");
    let err = assume(iff(p, q)).not_elim(assume(pvar("z"))).unwrap_err();
    assert!(matches!(err, Error::ConnectiveRule(_)));
}

#[test]
fn imp_elim_handles_nested_implication() {
    // ⊢ p ⟹ (q ⟹ r), ⊢ p  ⇒  ⊢ q ⟹ r
    let p = pvar("p");
    let q = pvar("q");
    let r = pvar("r");
    let nested = imp(p.clone(), imp(q.clone(), r.clone()));
    let result = assume(nested).imp_elim(assume(p)).unwrap();
    assert!(binop_head_is(result.concl(), &defs::imp_spec()));
    let (lhs, rhs) = binop_args(result.concl());
    assert_eq!(lhs, q);
    assert_eq!(rhs, r);
}
