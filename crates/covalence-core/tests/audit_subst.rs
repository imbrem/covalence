//! Exhaustive edge-case audit of the substitution / de Bruijn machinery
//! and the `type_of` type-checker, plus `Ctx`/`TermSet` set semantics.
//!
//! These functions underpin the soundness of every inference rule:
//! `close`/`open` implement binder introduction/elimination, `shift_by`
//! and `subst_free` implement capture-avoiding substitution, `type_of`
//! is the gatekeeper that rejects ill-typed terms before they can become
//! theorems, and `Ctx` is the hypothesis set whose semantics determine
//! when two theorems' assumptions agree.
//!
//! Tests are written against the *actual* observed behavior. Any
//! genuine soundness concern is flagged with a `// SUSPECT:` comment.
//! The audit found no soundness bugs; see the final report.

use std::collections::BTreeMap;

use covalence_core::subst::{self, close, has_free_var, is_closed, open, shift_by, subst_free};
use covalence_core::{Ctx, Term, Type, TypeKind, Var};

// ---------------------------------------------------------------------------
// helpers
// ---------------------------------------------------------------------------

fn ty_a() -> Type {
    Type::tfree("a")
}

/// A closed identity-ish abstraction `λ:nat. Bound(0)`.
fn lam_id() -> Term {
    Term::abs(Type::nat(), Term::bound(0))
}

// ===========================================================================
// close / open round trips
// ===========================================================================

#[test]
fn close_replaces_free_with_bound0() {
    let t = Term::free("x", Type::nat());
    let c = close(&t, "x");
    assert_eq!(c, Term::bound(0));
}

#[test]
fn close_leaves_other_frees_untouched() {
    let t = Term::free("y", Type::nat());
    let c = close(&t, "x");
    assert_eq!(c, t);
}

#[test]
fn close_increments_depth_under_binders() {
    // body = λ:nat. x ; closing on x must produce Bound(1) under the
    // inner binder (depth 1), not Bound(0).
    let inner = Term::free("x", Type::nat());
    let body = Term::abs(Type::nat(), inner);
    let c = close(&body, "x");
    let expected = Term::abs(Type::nat(), Term::bound(1));
    assert_eq!(c, expected);
}

#[test]
fn close_nested_binders_distinct_indices() {
    // λ.λ. (x, y)  where x is closed at outer, y stays free.
    // close on x at depth-2 should give Bound(2).
    let app = Term::app(Term::free("x", Type::nat()), Term::free("y", Type::nat()));
    let body = Term::abs(Type::nat(), Term::abs(Type::bool(), app));
    let c = close(&body, "x");
    let expected = Term::abs(
        Type::nat(),
        Term::abs(
            Type::bool(),
            Term::app(Term::bound(2), Term::free("y", Type::nat())),
        ),
    );
    assert_eq!(c, expected);
}

#[test]
fn close_then_open_with_same_free_is_identity_on_closed() {
    // For a closed term mentioning Free("x"), close then open(_, x)
    // should reproduce the original.
    let orig = Term::app(Term::free("x", Type::nat()), Term::free("z", Type::bool()));
    let closed = close(&orig, "x");
    let reopened = open(&closed, &Term::free("x", Type::nat()));
    assert_eq!(reopened, orig);
}

#[test]
fn close_then_open_under_binder_roundtrip() {
    // λ:bool. (x z) ; close x, then open with Free("x").
    let inner = Term::app(Term::free("x", Type::nat()), Term::free("z", Type::bool()));
    let orig = Term::abs(Type::bool(), inner);
    let closed = close(&orig, "x");
    let reopened = open(&closed, &Term::free("x", Type::nat()));
    assert_eq!(reopened, orig);
}

// ===========================================================================
// open: beta / forall-elim behavior
// ===========================================================================

#[test]
fn open_substitutes_bound0() {
    // body = Bound(0) ; open with a literal => the literal.
    let u = Term::nat_lit(7u32);
    assert_eq!(open(&Term::bound(0), &u), u);
}

#[test]
fn open_decrements_outer_bound_indices() {
    // body = Bound(1) (refers to an enclosing binder beyond the one
    // being eliminated). open consumes binder 0, so Bound(1) -> Bound(0).
    assert_eq!(open(&Term::bound(1), &Term::nat_lit(0u32)), Term::bound(0));
}

#[test]
fn open_shifts_replacement_under_binders() {
    // body = λ:nat. Bound(1)  (Bound(1) is the binder we eliminate).
    // Replacing it with Free("x") at depth 1: x is shifted up by 1, but
    // x is a Free with no bound indices, so it is unchanged. The result
    // is λ:nat. x.
    let body = Term::abs(Type::nat(), Term::bound(1));
    let r = open(&body, &Term::free("x", Type::nat()));
    let expected = Term::abs(Type::nat(), Term::free("x", Type::nat()));
    assert_eq!(r, expected);
}

#[test]
fn open_capture_avoiding_replacement_with_bound() {
    // body = λ:nat. Bound(1) ; replacement u = Bound(0) which refers to
    // an OUTER binder of the whole term. When substituted at depth 1
    // inside the body, u must shift to Bound(1) so it still points at
    // the same outer binder (capture avoidance). open(body, Bound(0))
    // = λ:nat. Bound(1).
    let body = Term::abs(Type::nat(), Term::bound(1));
    let r = open(&body, &Term::bound(0));
    let expected = Term::abs(Type::nat(), Term::bound(1));
    assert_eq!(r, expected);
}

#[test]
fn open_inner_binder_index_preserved() {
    // body = λ:nat. Bound(0)  (Bound(0) is the *inner* lambda's binder,
    // i < depth, so it is left alone). open should not disturb it.
    let body = Term::abs(Type::nat(), Term::bound(0));
    let r = open(&body, &Term::nat_lit(5u32));
    assert_eq!(r, body);
}

// ===========================================================================
// shift_by: cutoffs, underflow panic, identity
// ===========================================================================

#[test]
fn shift_by_zero_is_identity() {
    let t = Term::abs(Type::nat(), Term::bound(0));
    assert_eq!(shift_by(&t, 0, 0), t);
}

#[test]
fn shift_by_positive_above_cutoff() {
    assert_eq!(shift_by(&Term::bound(2), 3, 0), Term::bound(5));
}

#[test]
fn shift_by_respects_cutoff() {
    // Bound(0) is below cutoff 1 -> untouched; Bound(1) >= cutoff ->
    // shifted.
    assert_eq!(shift_by(&Term::bound(0), 5, 1), Term::bound(0));
    assert_eq!(shift_by(&Term::bound(1), 5, 1), Term::bound(6));
}

#[test]
fn shift_by_cutoff_increments_under_binder() {
    // λ. Bound(1) with delta 10, cutoff 0. Inside the binder cutoff
    // becomes 1; Bound(1) >= 1 so shifts to Bound(11).
    let t = Term::abs(Type::nat(), Term::bound(1));
    let s = shift_by(&t, 10, 0);
    assert_eq!(s, Term::abs(Type::nat(), Term::bound(11)));
}

#[test]
fn shift_by_negative_ok_when_no_underflow() {
    // Bound(3) shifted by -2 at cutoff 0 -> Bound(1).
    assert_eq!(shift_by(&Term::bound(3), -2, 0), Term::bound(1));
}

#[test]
#[should_panic(expected = "Bound underflow")]
fn shift_by_negative_underflow_panics() {
    // Bound(0) shifted by -1 at cutoff 0 would become -1: documented
    // panic, NOT a silent wrap to u32::MAX.
    let _ = shift_by(&Term::bound(0), -1, 0);
}

#[test]
#[should_panic(expected = "Bound underflow")]
fn shift_by_underflow_under_binder_panics() {
    // λ. Bound(1) shifted by -2: inside, cutoff=1, Bound(1) -> -1.
    let t = Term::abs(Type::nat(), Term::bound(1));
    let _ = shift_by(&t, -2, 0);
}

#[test]
fn shift_by_leaves_free_and_const_alone() {
    let f = Term::free("x", Type::nat());
    assert_eq!(shift_by(&f, 9, 0), f);
    let c = Term::const_("c", Type::bool());
    assert_eq!(shift_by(&c, 9, 0), c);
}

// ===========================================================================
// subst_free: capture avoidance
// ===========================================================================

#[test]
fn subst_free_basic() {
    let t = Term::free("x", Type::nat());
    let r = Term::nat_lit(42u32);
    assert_eq!(subst_free(&t, &Var::new("x", Type::nat()), &r), r);
}

#[test]
fn subst_free_other_name_untouched() {
    let t = Term::free("y", Type::nat());
    let r = Term::nat_lit(42u32);
    assert_eq!(subst_free(&t, &Var::new("x", Type::nat()), &r), t);
}

#[test]
fn subst_free_shifts_replacement_under_binder() {
    // t = λ:nat. x ; replacement r = Bound(0) (refers to some OUTER
    // binder of t). Substituting under the lambda must shift r up by 1
    // so it keeps pointing at the outer environment: result λ:nat.
    // Bound(1).
    let t = Term::abs(Type::nat(), Term::free("x", Type::nat()));
    let r = Term::bound(0);
    let out = subst_free(&t, &Var::new("x", Type::nat()), &r);
    let expected = Term::abs(Type::nat(), Term::bound(1));
    assert_eq!(out, expected);
}

#[test]
fn subst_free_nested_binders_shift_by_depth() {
    // t = λ.λ. x ; r = Bound(0). Substituting at depth 2 shifts r to
    // Bound(2).
    let t = Term::abs(
        Type::nat(),
        Term::abs(Type::bool(), Term::free("x", Type::nat())),
    );
    let out = subst_free(&t, &Var::new("x", Type::nat()), &Term::bound(0));
    let expected = Term::abs(Type::nat(), Term::abs(Type::bool(), Term::bound(2)));
    assert_eq!(out, expected);
}

#[test]
fn subst_free_closed_replacement_unchanged_under_binder() {
    // A closed replacement (no Bound) is unaffected by the depth shift.
    let t = Term::abs(Type::nat(), Term::free("x", Type::nat()));
    let r = Term::nat_lit(3u32);
    let out = subst_free(&t, &Var::new("x", Type::nat()), &r);
    let expected = Term::abs(Type::nat(), Term::nat_lit(3u32));
    assert_eq!(out, expected);
}

// ===========================================================================
// type_of: acceptance
// ===========================================================================

#[test]
fn type_of_free_is_its_type() {
    assert_eq!(Term::free("x", Type::nat()).type_of().unwrap(), Type::nat());
}

#[test]
fn type_of_abs_is_arrow() {
    // λ:nat. Bound(0) : nat -> nat
    assert_eq!(
        lam_id().type_of().unwrap(),
        Type::fun(Type::nat(), Type::nat())
    );
}

#[test]
fn type_of_app_well_typed() {
    // (λ:nat. Bound(0)) 5 : nat
    let app = Term::app(lam_id(), Term::nat_lit(5u32));
    assert_eq!(app.type_of().unwrap(), Type::nat());
}

#[test]
fn type_of_eq_op() {
    // = at nat : nat -> nat -> bool
    let t = Term::eq_op(Type::nat());
    assert_eq!(
        t.type_of().unwrap(),
        Type::fun(Type::nat(), Type::fun(Type::nat(), Type::bool()))
    );
}

#[test]
fn type_of_select_op() {
    // ε at nat : (nat -> bool) -> nat
    let t = Term::select_op(Type::nat());
    assert_eq!(
        t.type_of().unwrap(),
        Type::fun(Type::fun(Type::nat(), Type::bool()), Type::nat())
    );
}

#[test]
fn type_of_full_eq_application() {
    // (= at nat) 1 2 : bool
    let eq = Term::eq_op(Type::nat());
    let applied = Term::app(Term::app(eq, Term::nat_lit(1u32)), Term::nat_lit(2u32));
    assert_eq!(applied.type_of().unwrap(), Type::bool());
}

#[test]
fn type_of_bound_under_correct_binders() {
    // λ.λ. Bound(1) : nat -> bool -> nat  (Bound(1) = outer binder)
    let t = Term::abs(Type::nat(), Term::abs(Type::bool(), Term::bound(1)));
    assert_eq!(
        t.type_of().unwrap(),
        Type::fun(Type::nat(), Type::fun(Type::bool(), Type::nat()))
    );
}

#[test]
fn type_of_innermost_bound() {
    // λ.λ. Bound(0) : nat -> bool -> bool  (Bound(0) = inner binder)
    let t = Term::abs(Type::nat(), Term::abs(Type::bool(), Term::bound(0)));
    assert_eq!(
        t.type_of().unwrap(),
        Type::fun(Type::nat(), Type::fun(Type::bool(), Type::bool()))
    );
}

// ===========================================================================
// type_of: rejection
// ===========================================================================

#[test]
fn type_of_dangling_bound_is_not_closed() {
    // Bound(0) with no enclosing binder.
    assert!(Term::bound(0).type_of().is_err());
}

#[test]
fn type_of_bound_escaping_single_binder() {
    // λ:nat. Bound(1) — Bound(1) escapes the single binder.
    let t = Term::abs(Type::nat(), Term::bound(1));
    assert!(t.type_of().is_err());
}

#[test]
fn type_of_app_domain_mismatch() {
    // (λ:nat. Bound(0)) applied to a bool literal -> domain mismatch.
    let app = Term::app(lam_id(), Term::bool_lit(true));
    assert!(app.type_of().is_err());
}

#[test]
fn type_of_app_of_non_function() {
    // apply a nat literal to something -> NotFunction.
    let app = Term::app(Term::nat_lit(1u32), Term::nat_lit(2u32));
    assert!(app.type_of().is_err());
}

#[test]
fn type_of_free_reused_at_two_types() {
    // (x:nat) applied... actually build x:nat = x:bool style reuse:
    // App( = at nat applied to x:nat, x:bool ) so the same name x has
    // two declared types within one term.
    let lhs = Term::app(Term::eq_op(Type::nat()), Term::free("x", Type::nat()));
    let whole = Term::app(lhs, Term::free("x", Type::bool()));
    let err = whole.type_of();
    assert!(
        err.is_err(),
        "free var reused at two types must be rejected"
    );
}

#[test]
fn type_of_free_consistent_same_type_ok() {
    // Same name, same type, twice -> fine.
    let lhs = Term::app(Term::eq_op(Type::nat()), Term::free("x", Type::nat()));
    let whole = Term::app(lhs, Term::free("x", Type::nat()));
    assert_eq!(whole.type_of().unwrap(), Type::bool());
}

#[test]
fn type_of_ill_typed_eq_args() {
    // (= at nat) applied to a bool literal -> domain mismatch (nat vs
    // bool).
    let t = Term::app(Term::eq_op(Type::nat()), Term::bool_lit(true));
    assert!(t.type_of().is_err());
}

#[test]
fn type_of_abs_body_uses_binder_type() {
    // λ:bool. (= at nat) Bound(0) — Bound(0) has type bool but = expects
    // nat -> rejected.
    let body = Term::app(Term::eq_op(Type::nat()), Term::bound(0));
    let t = Term::abs(Type::bool(), body);
    assert!(t.type_of().is_err());
}

// ===========================================================================
// Spec / SpecAbs / SpecRep typing
// ===========================================================================

#[test]
fn type_of_spec_abs_newtype_no_tvars() {
    // f32 := newtype over u32 (carrier u32, no tvars).
    // spec_abs(f32) : u32 -> f32.
    let abs = Term::spec_abs(covalence_core::defs::f32_spec(), Vec::<Type>::new());
    let ty = abs.type_of().unwrap();
    let TypeKind::Fun(dom, cod) = ty.kind() else {
        panic!("expected a function type, got {ty:?}");
    };
    assert_eq!(*dom, covalence_core::defs::u32_ty());
    assert_eq!(*cod, covalence_core::defs::f32_ty());
}

#[test]
fn type_of_spec_rep_newtype_no_tvars() {
    // rep(f32) : f32 -> u32 (the reverse of abs).
    let rep = Term::spec_rep(covalence_core::defs::f32_spec(), Vec::<Type>::new());
    let ty = rep.type_of().unwrap();
    let TypeKind::Fun(dom, cod) = ty.kind() else {
        panic!("expected a function type, got {ty:?}");
    };
    assert_eq!(*dom, covalence_core::defs::f32_ty());
    assert_eq!(*cod, covalence_core::defs::u32_ty());
}

/// Coprod's tagged carrier relation `nat → bool → bool → bool`.
fn coprod_nat_bool_carrier() -> Type {
    Type::fun(
        Type::nat(),
        Type::fun(Type::bool(), Type::fun(Type::bool(), Type::bool())),
    )
}

#[test]
fn type_of_spec_abs_polymorphic_positional_args() {
    // coprod := subtype with tagged carrier ('a -> 'b -> bool -> bool),
    // tvars [a, b]. spec_abs(coprod, [nat, bool]) :
    // (nat -> bool -> bool -> bool) -> coprod nat bool.
    let spec = covalence_core::defs::coprod_spec();
    let abs = Term::spec_abs(spec.clone(), vec![Type::nat(), Type::bool()]);
    let ty = abs.type_of().unwrap();
    let wrapper = covalence_core::defs::coprod(Type::nat(), Type::bool());
    assert_eq!(ty, Type::fun(coprod_nat_bool_carrier(), wrapper));
}

#[test]
fn type_of_spec_rep_polymorphic_is_inverse_of_abs() {
    let spec = covalence_core::defs::coprod_spec();
    let rep = Term::spec_rep(spec.clone(), vec![Type::nat(), Type::bool()]);
    let ty = rep.type_of().unwrap();
    let wrapper = covalence_core::defs::coprod(Type::nat(), Type::bool());
    assert_eq!(ty, Type::fun(wrapper, coprod_nat_bool_carrier()));
}

#[test]
fn type_of_spec_leaf_term() {
    // cond_spec is a TermSpec; instantiating it should type-check.
    let t = Term::term_spec(covalence_core::defs::cond_spec(), vec![Type::nat()]);
    assert!(t.type_of().is_ok());
}

// ===========================================================================
// subst_tfree(s): simultaneous vs sequential
// ===========================================================================

#[test]
fn subst_tfree_in_type_basic() {
    let ty = Type::fun(ty_a(), Type::nat());
    let out = subst::subst_tfree_in_type(&ty, "a", &Type::bool());
    assert_eq!(out, Type::fun(Type::bool(), Type::nat()));
}

#[test]
fn subst_tfrees_simultaneous_no_cascade_type() {
    // {a := b, b := c} on type `a -> b` must give `b -> c`, NOT `c -> c`
    // (a fold would cascade a -> b -> c).
    let ty = Type::fun(ty_a(), Type::tfree("b"));
    let mut sub: BTreeMap<smol_str::SmolStr, Type> = BTreeMap::new();
    sub.insert("a".into(), Type::tfree("b"));
    sub.insert("b".into(), Type::tfree("c"));
    let out = subst::subst_tfrees_in_type(&ty, &sub);
    let expected = Type::fun(Type::tfree("b"), Type::tfree("c"));
    assert_eq!(out, expected);
    // Definitely NOT the cascaded result.
    assert_ne!(out, Type::fun(Type::tfree("c"), Type::tfree("c")));
}

#[test]
fn subst_tfrees_simultaneous_no_cascade_term() {
    // Same property at the term level: a Free annotated `a` and another
    // annotated `b`.
    let t = Term::app(Term::free("p", ty_a()), Term::free("q", Type::tfree("b")));
    let mut sub: BTreeMap<smol_str::SmolStr, Type> = BTreeMap::new();
    sub.insert("a".into(), Type::tfree("b"));
    sub.insert("b".into(), Type::tfree("c"));
    let out = subst::subst_tfrees_in_term(&t, &sub);
    let expected = Term::app(
        Term::free("p", Type::tfree("b")),
        Term::free("q", Type::tfree("c")),
    );
    assert_eq!(out, expected);
}

#[test]
fn subst_tfrees_swaps_two_params_type() {
    // The case the rel-theory bug hit: a *swap* `{a := b, b := a}` on
    // `a -> b` must give `b -> a` (a sequential fold collapses it to
    // `a -> a`, because `a := b` then `b := a` rewrites the `b`s it just
    // introduced). This is the hardest simultaneous case.
    let ty = Type::fun(ty_a(), Type::tfree("b"));
    let mut sub: BTreeMap<smol_str::SmolStr, Type> = BTreeMap::new();
    sub.insert("a".into(), Type::tfree("b"));
    sub.insert("b".into(), Type::tfree("a"));
    let out = subst::subst_tfrees_in_type(&ty, &sub);
    assert_eq!(
        out,
        Type::fun(Type::tfree("b"), Type::tfree("a")),
        "swap a<->b"
    );
    // The cascade bug would collapse both to one variable.
    assert_ne!(out, Type::fun(Type::tfree("a"), Type::tfree("a")));
    assert_ne!(out, Type::fun(Type::tfree("b"), Type::tfree("b")));
}

#[test]
fn subst_tfrees_swaps_two_params_term() {
    // Same swap at the term level (Free annotations + an Eq op).
    let t = Term::app(
        Term::app(Term::eq_op(ty_a()), Term::free("p", ty_a())),
        Term::free("q", Type::tfree("b")),
    );
    let mut sub: BTreeMap<smol_str::SmolStr, Type> = BTreeMap::new();
    sub.insert("a".into(), Type::tfree("b"));
    sub.insert("b".into(), Type::tfree("a"));
    let out = subst::subst_tfrees_in_term(&t, &sub);
    let expected = Term::app(
        Term::app(
            Term::eq_op(Type::tfree("b")),
            Term::free("p", Type::tfree("b")),
        ),
        Term::free("q", Type::tfree("a")),
    );
    assert_eq!(out, expected);
}

#[test]
fn subst_tfrees_three_cycle() {
    // A 3-cycle `{a:=b, b:=c, c:=a}` on `a -> b -> c` rotates to
    // `b -> c -> a` — no fold order reproduces this.
    let ty = Type::fun(ty_a(), Type::fun(Type::tfree("b"), Type::tfree("c")));
    let mut sub: BTreeMap<smol_str::SmolStr, Type> = BTreeMap::new();
    sub.insert("a".into(), Type::tfree("b"));
    sub.insert("b".into(), Type::tfree("c"));
    sub.insert("c".into(), Type::tfree("a"));
    let out = subst::subst_tfrees_in_type(&ty, &sub);
    let expected = Type::fun(
        Type::tfree("b"),
        Type::fun(Type::tfree("c"), Type::tfree("a")),
    );
    assert_eq!(out, expected);
}

#[test]
fn subst_tfrees_replacement_is_not_reprocessed() {
    // A replacement that *is* a substituted key must be returned verbatim,
    // never re-substituted: `{a := a}` is the identity, and `{a := nat}`
    // where `nat` is irrelevant. The subtle one: `{a := b}` where `b` is
    // NOT a key leaves `b` alone, and `{a := b, b := nat}` gives `a -> b`
    // not `a -> nat` for the `a` occurrence.
    let ty = Type::fun(ty_a(), Type::tfree("b"));
    let mut sub: BTreeMap<smol_str::SmolStr, Type> = BTreeMap::new();
    sub.insert("a".into(), Type::tfree("b"));
    sub.insert("b".into(), Type::nat());
    let out = subst::subst_tfrees_in_type(&ty, &sub);
    // `a` -> `b` (the value, NOT re-substituted to nat); `b` -> nat.
    assert_eq!(out, Type::fun(Type::tfree("b"), Type::nat()));
}

#[test]
fn subst_tfree_in_term_updates_annotations() {
    // Free("x", a) and the Eq op at type a.
    let t = Term::app(Term::eq_op(ty_a()), Term::free("x", ty_a()));
    let out = subst::subst_tfree_in_term(&t, "a", &Type::nat());
    let expected = Term::app(Term::eq_op(Type::nat()), Term::free("x", Type::nat()));
    assert_eq!(out, expected);
}

#[test]
fn subst_tfrees_empty_map_is_identity() {
    let t = Term::free("x", ty_a());
    let sub: BTreeMap<smol_str::SmolStr, Type> = BTreeMap::new();
    assert_eq!(subst::subst_tfrees_in_term(&t, &sub), t);
    let ty = Type::fun(ty_a(), Type::nat());
    assert_eq!(subst::subst_tfrees_in_type(&ty, &sub), ty);
}

// ===========================================================================
// match_types: one-way matching
// ===========================================================================

#[test]
fn match_types_binds_pattern_tvar() {
    let mut sub = BTreeMap::new();
    let r = subst::match_types(&ty_a(), &Type::nat(), &mut sub);
    assert!(r.is_ok());
    assert_eq!(sub.get("a").cloned(), Some(Type::nat()));
}

#[test]
fn match_types_consistent_repeat_ok() {
    // pattern `a -> a` against `nat -> nat` is consistent.
    let pat = Type::fun(ty_a(), ty_a());
    let tgt = Type::fun(Type::nat(), Type::nat());
    let mut sub = BTreeMap::new();
    assert!(subst::match_types(&pat, &tgt, &mut sub).is_ok());
    assert_eq!(sub.get("a").cloned(), Some(Type::nat()));
}

#[test]
fn match_types_inconsistent_repeat_err() {
    // pattern `a -> a` against `nat -> bool` is inconsistent.
    let pat = Type::fun(ty_a(), ty_a());
    let tgt = Type::fun(Type::nat(), Type::bool());
    let mut sub = BTreeMap::new();
    assert!(subst::match_types(&pat, &tgt, &mut sub).is_err());
}

#[test]
fn match_types_structural_mismatch_err() {
    // nat vs bool with no schematic var to absorb it.
    let mut sub = BTreeMap::new();
    assert!(subst::match_types(&Type::nat(), &Type::bool(), &mut sub).is_err());
}

#[test]
fn match_types_is_one_way_not_unification() {
    // A concrete pattern (nat) cannot match against a schematic target
    // (tfree b): matching is one-way, only the *pattern's* tvars are
    // schematic.
    let mut sub = BTreeMap::new();
    assert!(subst::match_types(&Type::nat(), &Type::tfree("b"), &mut sub).is_err());
}

#[test]
fn match_types_bool_and_spec_arms() {
    // `bool` matches `bool` (no schematic var).
    let mut sub = BTreeMap::new();
    assert!(subst::match_types(&Type::bool(), &Type::bool(), &mut sub).is_ok());
    assert!(sub.is_empty());

    // A `Spec` pattern with an inner tvar binds it from the target:
    // `set 'a` vs `set nat` → {a := nat}. This is the path `Def::body`
    // uses to recover the substitution; without the `Spec` arm it would
    // erroneously fail (and `Def::body`'s `.expect` would panic).
    let set_a = covalence_core::defs::set(Type::tfree("a"));
    let set_nat = covalence_core::defs::set(Type::nat());
    let mut sub = BTreeMap::new();
    assert!(subst::match_types(&set_a, &set_nat, &mut sub).is_ok());
    assert_eq!(sub.get("a"), Some(&Type::nat()));

    // Different spec heads do not match (`set 'a` vs `option nat`).
    let opt_nat = covalence_core::defs::option(Type::nat());
    let mut sub = BTreeMap::new();
    assert!(subst::match_types(&set_a, &opt_nat, &mut sub).is_err());
}

// ===========================================================================
// predicates: is_closed / has_free_var / find_free_type / uses_bound_outer
//             / collect_term_tvars
// ===========================================================================

#[test]
fn is_closed_true_for_closed() {
    assert!(is_closed(&lam_id()));
    assert!(is_closed(&Term::free("x", Type::nat())));
    assert!(is_closed(&Term::nat_lit(0u32)));
}

#[test]
fn is_closed_false_for_dangling() {
    assert!(!is_closed(&Term::bound(0)));
    assert!(!is_closed(&Term::abs(Type::nat(), Term::bound(1))));
}

#[test]
fn has_free_var_finds_name() {
    let t = Term::app(Term::free("x", Type::nat()), Term::free("y", Type::bool()));
    assert!(has_free_var(&t, "x"));
    assert!(has_free_var(&t, "y"));
    assert!(!has_free_var(&t, "z"));
}

#[test]
fn find_free_type_returns_declared_type() {
    let t = Term::abs(Type::nat(), Term::free("x", Type::bool()));
    assert_eq!(subst::find_free_type(&t, "x"), Some(Type::bool()));
    assert_eq!(subst::find_free_type(&t, "nope"), None);
}

#[test]
fn uses_bound_outer_detects_outer_index() {
    // λ. Bound(1) uses the outer Bound(0)-as-seen-from-outside.
    let t = Term::abs(Type::nat(), Term::bound(1));
    assert!(subst::uses_bound_outer(&t, 0));
    // λ. Bound(0) does NOT use any outer binder.
    let t2 = Term::abs(Type::nat(), Term::bound(0));
    assert!(!subst::uses_bound_outer(&t2, 0));
}

#[test]
fn collect_term_tvars_gathers_all_annotations() {
    use std::collections::BTreeSet;
    // λ:a. (x:b) where the binder type is `a` and the body Free has `b`.
    let t = Term::abs(ty_a(), Term::free("x", Type::tfree("b")));
    let mut out = BTreeSet::new();
    subst::collect_term_tvars(&t, &mut out);
    assert!(out.contains("a"));
    assert!(out.contains("b"));
    assert_eq!(out.len(), 2);
}

// ===========================================================================
// Ctx / TermSet: true-set semantics
// ===========================================================================

fn h(name: &str) -> Term {
    Term::free(name, Type::bool())
}

#[test]
fn ctx_new_is_empty() {
    let c = Ctx::new();
    assert!(c.is_empty());
    assert_eq!(c.len(), 0);
}

#[test]
fn ctx_insert_dedups() {
    let c = Ctx::new().insert(h("a")).insert(h("a"));
    assert_eq!(c.len(), 1);
    assert!(c.contains(&h("a")));
}

#[test]
fn ctx_insert_distinct_grows() {
    let c = Ctx::new().insert(h("a")).insert(h("b"));
    assert_eq!(c.len(), 2);
}

#[test]
fn ctx_equality_is_order_insensitive() {
    let c1 = Ctx::new().insert(h("a")).insert(h("b"));
    let c2 = Ctx::new().insert(h("b")).insert(h("a"));
    assert_eq!(c1, c2);
}

#[test]
fn ctx_remove() {
    let c = Ctx::new().insert(h("a")).insert(h("b"));
    let c2 = c.remove(&h("a"));
    assert_eq!(c2.len(), 1);
    assert!(!c2.contains(&h("a")));
    assert!(c2.contains(&h("b")));
}

#[test]
fn ctx_remove_absent_is_noop_equal() {
    let c = Ctx::new().insert(h("a"));
    let c2 = c.remove(&h("zzz"));
    assert_eq!(c, c2);
}

#[test]
fn ctx_remove_last_yields_empty() {
    let c = Ctx::singleton(h("a")).remove(&h("a"));
    assert!(c.is_empty());
    assert_eq!(c, Ctx::new());
}

#[test]
fn ctx_union_with_empty_is_self() {
    let c = Ctx::new().insert(h("a")).insert(h("b"));
    assert_eq!(c.union(&Ctx::new()), c);
    assert_eq!(Ctx::new().union(&c), c);
}

#[test]
fn ctx_union_with_self_is_self() {
    let c = Ctx::new().insert(h("a")).insert(h("b"));
    assert_eq!(c.union(&c), c);
}

#[test]
fn ctx_union_combines_and_dedups() {
    let c1 = Ctx::new().insert(h("a")).insert(h("b"));
    let c2 = Ctx::new().insert(h("b")).insert(h("c"));
    let u = c1.union(&c2);
    assert_eq!(u.len(), 3);
    for n in ["a", "b", "c"] {
        assert!(u.contains(&h(n)));
    }
}

#[test]
fn ctx_subset_semantics() {
    let small = Ctx::new().insert(h("a"));
    let big = Ctx::new().insert(h("a")).insert(h("b"));
    assert!(small.is_subset(&big));
    assert!(!big.is_subset(&small));
    // empty is subset of everything.
    assert!(Ctx::new().is_subset(&big));
    // self-subset.
    assert!(big.is_subset(&big));
}

#[test]
fn ctx_from_iter_dedups() {
    let c: Ctx = vec![h("a"), h("b"), h("a")].into_iter().collect();
    assert_eq!(c.len(), 2);
}

#[test]
fn ctx_singleton() {
    let c = Ctx::singleton(h("a"));
    assert_eq!(c.len(), 1);
    assert!(c.contains(&h("a")));
}

#[test]
fn ctx_empty_equals_default() {
    assert_eq!(Ctx::new(), Ctx::default());
    // An inserted-then-removed-to-empty context equals a fresh one.
    let drained = Ctx::singleton(h("a")).remove(&h("a"));
    assert_eq!(drained, Ctx::new());
}

#[test]
fn ctx_iter_yields_all_members() {
    use std::collections::BTreeSet;
    let c = Ctx::new().insert(h("a")).insert(h("b")).insert(h("c"));
    let seen: BTreeSet<Term> = c.iter().cloned().collect();
    assert_eq!(seen.len(), 3);
}
