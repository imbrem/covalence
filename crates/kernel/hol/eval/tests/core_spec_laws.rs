//! Core spec-law rules exercised with *moved-catalogue* fixtures.
//!
//! These tests lived in `covalence-core`'s `hol_light_tests` and moved
//! here with the `defs/` term catalogue (stage E2): the rules under
//! test (`spec_ax`, the subtype laws, `unfold_term_spec`) are core
//! kernel rules, but the specs used as fixtures (`set`, `rel.holds`,
//! `nat.bitAnd`) now live in `covalence_hol_eval::defs`.

use covalence_core::{Error, Term, Type, TypeList};
use covalence_hol_eval::defs;

/// The pure tier (`Thm<CoreLang>`) — these are core-rule tests.
type Thm = covalence_core::Thm;
/// `lhs = rhs` split (HOL equality application spine).
fn as_eq(t: &Term) -> (&Term, &Term) {
    t.as_eq().expect("expected an equation")
}

/// `p ⟹ q` split on the defined `imp` connective.
fn as_imp(t: &Term) -> (&Term, &Term) {
    use covalence_core::TermKind;
    if let TermKind::App(pq, q) = t.kind()
        && let TermKind::App(head, p) = pq.kind()
        && let TermKind::Spec(spec, _) = head.kind()
        && spec.ptr_eq(&defs::imp_spec())
    {
        return (p, q);
    }
    panic!("expected `p ==> q`, got {t}");
}

/// Is `t` a disjunction `p ∨ q`?
fn is_or(t: &Term) -> bool {
    use covalence_core::TermKind;
    if let TermKind::App(pq, _) = t.kind()
        && let TermKind::App(head, _) = pq.kind()
        && let TermKind::Spec(spec, _) = head.kind()
    {
        return spec.ptr_eq(&defs::or_spec());
    }
    false
}

#[test]
fn spec_ax_rejects_declaration_only_and_non_spec() {
    // A declaration-only spec (`tm = None`) has no predicate. `nat.bitAnd`
    // is declaration-only by design — it only reduces on literals, no body.
    // (`nat.div`, by contrast, carries a body, so `spec_ax` differs.)
    let decl = defs::nat_bit_and();
    let w = Term::free("w", decl.type_of().unwrap());
    assert!(matches!(Thm::spec_ax(decl, w), Err(Error::SpecHasNoBody)));
    // A non-spec term is rejected before anything else.
    assert!(matches!(
        Thm::spec_ax(Term::nat_lit(5u32), Term::nat_lit(0u32)),
        Err(Error::NotASpec)
    ));
}

// ---- TypeSpec subtype laws (spec_abs_rep / spec_rep_abs_fwd / _back) ----

#[test]
fn spec_abs_rep_unconditional_for_set_newtype() {
    // `set bool` is a newtype over `bool → bool`. abs (rep s) = s.
    let elem = Type::bool();
    let spec = defs::set_spec();
    let args = TypeList::from(vec![elem.clone()]);
    let s = Term::free("s", Type::spec(spec.clone(), args.clone()));
    let thm = Thm::spec_abs_rep(spec, args, s.clone()).expect("abs (rep s) = s");
    assert!(thm.hyps().is_empty());
    let (_l, r) = as_eq(thm.concl());
    assert_eq!(r, &s, "rhs is the wrapper element itself");
}

#[test]
fn spec_rep_abs_fwd_discharges_to_unconditional_for_newtype() {
    // For a newtype the premise `P p` is `(λ_. T) p`; β + truth discharge
    // it, yielding the unconditional `rep (abs p) = p`.
    let elem = Type::bool();
    let carrier = Type::fun(elem.clone(), Type::bool()); // set bool's carrier
    let spec = defs::set_spec();
    let args = TypeList::from(vec![elem]);
    let p = Term::free("p", carrier);
    let imp = Thm::spec_rep_abs_fwd(spec, args, p.clone()).expect("P p ⟹ rep (abs p) = p");
    assert!(imp.hyps().is_empty());
    // The antecedent `(λ_. T) p` β-reduces to `T`.
    let (prem, _eq) = as_imp(imp.concl());
    let beta = Thm::beta_conv(prem.clone()).expect("β on (λ_. T) p");
    assert_eq!(beta.concl().as_eq().unwrap().1, &Term::bool_lit(true));
}

#[test]
fn spec_rep_abs_back_has_emptiness_escape() {
    // back: rep (abs a) = a ⟹ (P a ∨ ¬∃x. P x).
    let elem = Type::bool();
    let carrier = Type::fun(elem.clone(), Type::bool());
    let spec = defs::set_spec();
    let args = TypeList::from(vec![elem]);
    let a = Term::free("p", carrier);
    let thm = Thm::spec_rep_abs_back(spec, args, a).expect("back direction");
    assert!(thm.hyps().is_empty());
    // Conclusion is an implication whose consequent is a disjunction.
    let (_prem, disj) = as_imp(thm.concl());
    assert!(is_or(disj), "consequent is `P a ∨ ¬∃x. P x`");
}

#[test]
fn subtype_laws_reject_non_subtype_carrier() {
    // A type mismatch: feeding a `nat` where the carrier is `bool → bool`.
    let elem = Type::bool();
    let spec = defs::set_spec();
    let args = TypeList::from(vec![elem]);
    assert!(Thm::spec_rep_abs_fwd(spec, args, Term::free("n", Type::nat())).is_err());
}

#[test]
fn unfold_term_spec_handles_swapped_type_params() {
    // Regression: a multi-type-parameter let-spec instantiated with its
    // parameters *swapped*. `rel.holds : rel 'a 'b → 'a → 'b → bool`
    // unfolded at `['b,'a]` must yield a body of type
    // `rel 'b 'a → 'b → 'a → bool`. A sequential `{a:=b, b:=a}` fold
    // would cascade — `a→b` then `b→a` collapses both to one variable,
    // giving the bogus `rel 'a 'a → …`. Simultaneous substitution fixes
    // it.
    let a = Type::tfree("a");
    let b = Type::tfree("b");
    let holds = defs::rel_holds(b.clone(), a.clone()); // rel.holds['b,'a]
    let expected_ty = Type::fun(
        defs::rel(b.clone(), a.clone()),
        Type::fun(b.clone(), Type::fun(a.clone(), Type::bool())),
    );
    assert_eq!(
        holds.type_of().unwrap(),
        expected_ty,
        "leaf type at ['b,'a]"
    );

    let thm = Thm::unfold_term_spec(holds.clone()).expect("unfold rel.holds['b,'a]");
    assert!(thm.hyps().is_empty());
    let (lhs, rhs) = as_eq(thm.concl());
    assert_eq!(lhs, &holds);
    // The unfolded body must keep the swapped type — not collapse to one.
    assert_eq!(
        rhs.type_of().unwrap(),
        expected_ty,
        "unfolded body preserves swapped type parameters"
    );
}
