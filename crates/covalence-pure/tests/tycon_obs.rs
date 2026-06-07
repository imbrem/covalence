//! Tests for `TypeKind::TyConObs` — Arc-identity type constructors.
//!
//! Mirrors the term-side `TermKind::Obs` story on the type side: each
//! `Type::tycon_obs` call allocates a fresh observer Arc, so two
//! independent calls produce distinct types even with the same hint
//! and the same args. `subst_tfree` propagates through `TyConObs`'s
//! args without affecting its identity.

use covalence_pure::{Thm, Type, TypeKind};

#[derive(Debug)]
struct TypeDefMarker;

#[derive(Debug)]
struct OtherMarker;

#[test]
fn distinct_tycon_obs_calls_yield_distinct_types() {
    let a = Type::tycon_obs(TypeDefMarker, "T", vec![]);
    let b = Type::tycon_obs(TypeDefMarker, "T", vec![]);
    assert_ne!(a, b, "distinct tycon_obs calls produce distinct types");
}

#[test]
fn cloning_a_tycon_obs_preserves_identity() {
    let a = Type::tycon_obs(TypeDefMarker, "T", vec![]);
    let b = a.clone();
    assert_eq!(a, b, "clone preserves Arc identity");
}

#[test]
fn tycon_obs_hint_is_alpha_transparent() {
    // Same observer Arc, different hints: still equal (Hint is α-transparent).
    let a = Type::tycon_obs(TypeDefMarker, "Foo", vec![]);
    let b_dyn = match a.kind() {
        TypeKind::TyConObs(d, _, _) => d.clone(),
        _ => panic!(),
    };
    let b = Type::tycon_obs_from_dyn(b_dyn, "Bar", vec![]);
    assert_eq!(a, b, "hint should not affect equality");
}

#[test]
fn tycon_obs_args_participate_in_equality() {
    // Same observer Arc, different args: unequal.
    let a = Type::tycon_obs(TypeDefMarker, "list", vec![Type::tfree("a")]);
    let dyn_obs = match a.kind() {
        TypeKind::TyConObs(d, _, _) => d.clone(),
        _ => panic!(),
    };
    let b = Type::tycon_obs_from_dyn(dyn_obs.clone(), "list", vec![Type::bytes()]);
    assert_ne!(a, b, "different type-args produce different types");
}

#[test]
fn tycon_obs_inst_tfree_propagates_through_args() {
    // Build `⊢ x ≡ x` where x : list 'a, then inst_tfree('a, bytes).
    let list_a = Type::tycon_obs(TypeDefMarker, "list", vec![Type::tfree("a")]);
    let dyn_obs = match list_a.kind() {
        TypeKind::TyConObs(d, _, _) => d.clone(),
        _ => panic!(),
    };
    let x = covalence_pure::Term::free("x", list_a.clone());
    let thm = Thm::refl(x).unwrap();
    let inst = thm.inst_tfree("a", Type::bytes()).unwrap();

    // The concl now has list bytes (same Arc, different args).
    let list_bytes = Type::tycon_obs_from_dyn(dyn_obs, "list", vec![Type::bytes()]);
    let expected_x = covalence_pure::Term::free("x", list_bytes);
    let expected = Thm::refl(expected_x).unwrap();
    assert_eq!(inst.concl(), expected.concl());
}

#[test]
fn different_rust_markers_yield_unequal_types_even_with_same_hint() {
    let a = Type::tycon_obs(TypeDefMarker, "T", vec![]);
    let b = Type::tycon_obs(OtherMarker, "T", vec![]);
    assert_ne!(a, b, "different observer Rust types are different identities");
}

#[test]
fn tycon_obs_is_not_prop() {
    let a = Type::tycon_obs(TypeDefMarker, "Foo", vec![]);
    assert!(!a.is_prop());
}

#[test]
fn free_tvars_walks_tycon_obs_args() {
    let ty = Type::tycon_obs(
        TypeDefMarker,
        "pair",
        vec![Type::tfree("a"), Type::tfree("b")],
    );
    use smol_str::SmolStr;
    assert_eq!(ty.free_tvars(), vec![SmolStr::new("a"), SmolStr::new("b")]);
}

#[test]
fn tycon_obs_can_be_used_as_a_term_type() {
    // Type::tycon_obs is a legitimate type and can label Free / Const /
    // Obs leaves. Refl over an x of such type type-checks.
    let tau = Type::tycon_obs(TypeDefMarker, "τ", vec![]);
    let x = covalence_pure::Term::free("x", tau);
    let thm = Thm::refl(x.clone()).unwrap();
    match thm.concl().kind() {
        covalence_pure::TermKind::Eq(a, b) => {
            assert_eq!(a, &x);
            assert_eq!(b, &x);
        }
        _ => panic!(),
    }
}
