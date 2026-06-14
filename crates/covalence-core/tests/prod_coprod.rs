//! Integration tests for the `prod` (pair/fst/snd) and `coprod`
//! (inl/inr/coprodCase) constructors and eliminators in
//! `covalence_core::defs`.
//!
//! These exercise the kernel-level *type correctness*, *definitional
//! body type-checking*, *structure*, and *singleton identity* of the
//! product / coproduct catalogue entries. The kernel proves no
//! equations, so derived facts like `fst (pair a b) = a` are NOT
//! tested here — only types, definitional bodies, structure and
//! Display.

use covalence_core::defs::{
    coprod, coprod_case, coprod_case_spec, coprod_spec, fst, fst_spec, inl, inl_spec, inr,
    inr_spec, pair, pair_spec, prod, prod_spec, snd, snd_spec,
};
use covalence_core::{TermKind, Type, TypeKind};

// ============================================================================
// 1. Type-correctness of accessors
// ============================================================================

/// `pair α β : α → β → prod α β`.
#[test]
fn pair_type_concrete() {
    let (a, b) = (Type::nat(), Type::int());
    let expected = Type::fun(a.clone(), Type::fun(b.clone(), prod(a.clone(), b.clone())));
    assert_eq!(pair(a, b).type_of().unwrap(), expected);
}

#[test]
fn pair_type_bool_unit() {
    let (a, b) = (Type::bool(), Type::unit());
    let expected = Type::fun(a.clone(), Type::fun(b.clone(), prod(a.clone(), b.clone())));
    assert_eq!(pair(a, b).type_of().unwrap(), expected);
}

#[test]
fn pair_type_tfree_mix() {
    let (a, b) = (Type::tfree("a"), Type::tfree("b"));
    let expected = Type::fun(a.clone(), Type::fun(b.clone(), prod(a.clone(), b.clone())));
    assert_eq!(pair(a, b).type_of().unwrap(), expected);
}

/// `fst α β : prod α β → α`.
#[test]
fn fst_type_concrete() {
    let (a, b) = (Type::nat(), Type::int());
    let expected = Type::fun(prod(a.clone(), b.clone()), a.clone());
    assert_eq!(fst(a, b).type_of().unwrap(), expected);
}

#[test]
fn fst_type_tfree_mix() {
    let (a, b) = (Type::tfree("a"), Type::tfree("b"));
    let expected = Type::fun(prod(a.clone(), b.clone()), a.clone());
    assert_eq!(fst(a, b).type_of().unwrap(), expected);
}

/// `snd α β : prod α β → β`.
#[test]
fn snd_type_concrete() {
    let (a, b) = (Type::nat(), Type::int());
    let expected = Type::fun(prod(a.clone(), b.clone()), b.clone());
    assert_eq!(snd(a, b).type_of().unwrap(), expected);
}

#[test]
fn snd_type_bool_unit() {
    let (a, b) = (Type::bool(), Type::unit());
    let expected = Type::fun(prod(a.clone(), b.clone()), b.clone());
    assert_eq!(snd(a, b).type_of().unwrap(), expected);
}

/// `inl α β : α → coprod α β`.
#[test]
fn inl_type_concrete() {
    let (a, b) = (Type::nat(), Type::int());
    let expected = Type::fun(a.clone(), coprod(a.clone(), b.clone()));
    assert_eq!(inl(a, b).type_of().unwrap(), expected);
}

#[test]
fn inl_type_tfree_mix() {
    let (a, b) = (Type::tfree("a"), Type::tfree("b"));
    let expected = Type::fun(a.clone(), coprod(a.clone(), b.clone()));
    assert_eq!(inl(a, b).type_of().unwrap(), expected);
}

/// `inr α β : β → coprod α β`.
#[test]
fn inr_type_concrete() {
    let (a, b) = (Type::nat(), Type::int());
    let expected = Type::fun(b.clone(), coprod(a.clone(), b.clone()));
    assert_eq!(inr(a, b).type_of().unwrap(), expected);
}

#[test]
fn inr_type_bool_unit() {
    let (a, b) = (Type::bool(), Type::unit());
    let expected = Type::fun(b.clone(), coprod(a.clone(), b.clone()));
    assert_eq!(inr(a, b).type_of().unwrap(), expected);
}

/// `coprod_case α β γ : (α→γ) → (β→γ) → coprod α β → γ`.
#[test]
fn coprod_case_type_concrete() {
    let (a, b, c) = (Type::nat(), Type::int(), Type::bool());
    let expected = Type::fun(
        Type::fun(a.clone(), c.clone()),
        Type::fun(
            Type::fun(b.clone(), c.clone()),
            Type::fun(coprod(a.clone(), b.clone()), c.clone()),
        ),
    );
    assert_eq!(coprod_case(a, b, c).type_of().unwrap(), expected);
}

#[test]
fn coprod_case_type_tfree_mix() {
    let (a, b, c) = (Type::tfree("a"), Type::tfree("b"), Type::tfree("c"));
    let expected = Type::fun(
        Type::fun(a.clone(), c.clone()),
        Type::fun(
            Type::fun(b.clone(), c.clone()),
            Type::fun(coprod(a.clone(), b.clone()), c.clone()),
        ),
    );
    assert_eq!(coprod_case(a, b, c).type_of().unwrap(), expected);
}

// ============================================================================
// 2. Definitional bodies exist and type-check (polymorphic at tfree)
// ============================================================================

#[test]
fn pair_spec_body_typechecks() {
    let spec = pair_spec();
    let body = spec.tm().expect("pair has a definitional body");
    assert_eq!(Some(&body.type_of().unwrap()), spec.ty());
}

#[test]
fn fst_spec_body_typechecks() {
    let spec = fst_spec();
    let body = spec.tm().expect("fst has a definitional body");
    assert_eq!(Some(&body.type_of().unwrap()), spec.ty());
}

#[test]
fn snd_spec_body_typechecks() {
    let spec = snd_spec();
    let body = spec.tm().expect("snd has a definitional body");
    assert_eq!(Some(&body.type_of().unwrap()), spec.ty());
}

#[test]
fn inl_spec_body_typechecks() {
    let spec = inl_spec();
    let body = spec.tm().expect("inl has a definitional body");
    assert_eq!(Some(&body.type_of().unwrap()), spec.ty());
}

#[test]
fn inr_spec_body_typechecks() {
    let spec = inr_spec();
    let body = spec.tm().expect("inr has a definitional body");
    assert_eq!(Some(&body.type_of().unwrap()), spec.ty());
}

#[test]
fn coprod_case_spec_body_typechecks() {
    let spec = coprod_case_spec();
    let body = spec.tm().expect("coprodCase has a definitional body");
    assert_eq!(Some(&body.type_of().unwrap()), spec.ty());
}

/// The recorded `ty()` for each constructor matches the polymorphic
/// expected type built over the spec's type variables.
#[test]
fn spec_recorded_types_are_polymorphic() {
    let (a, b, c) = (Type::tfree("a"), Type::tfree("b"), Type::tfree("c"));

    assert_eq!(
        pair_spec().ty(),
        Some(&Type::fun(
            a.clone(),
            Type::fun(b.clone(), prod(a.clone(), b.clone()))
        ))
    );
    assert_eq!(
        fst_spec().ty(),
        Some(&Type::fun(prod(a.clone(), b.clone()), a.clone()))
    );
    assert_eq!(
        snd_spec().ty(),
        Some(&Type::fun(prod(a.clone(), b.clone()), b.clone()))
    );
    assert_eq!(
        inl_spec().ty(),
        Some(&Type::fun(a.clone(), coprod(a.clone(), b.clone())))
    );
    assert_eq!(
        inr_spec().ty(),
        Some(&Type::fun(b.clone(), coprod(a.clone(), b.clone())))
    );
    assert_eq!(
        coprod_case_spec().ty(),
        Some(&Type::fun(
            Type::fun(a.clone(), c.clone()),
            Type::fun(
                Type::fun(b.clone(), c.clone()),
                Type::fun(coprod(a.clone(), b.clone()), c.clone()),
            ),
        ))
    );
}

// ============================================================================
// 3. Singletons & identity (LazyLock-shared handles)
// ============================================================================

#[test]
fn term_specs_are_shared_singletons() {
    assert!(pair_spec().ptr_eq(&pair_spec()));
    assert!(fst_spec().ptr_eq(&fst_spec()));
    assert!(snd_spec().ptr_eq(&snd_spec()));
    assert!(inl_spec().ptr_eq(&inl_spec()));
    assert!(inr_spec().ptr_eq(&inr_spec()));
    assert!(coprod_case_spec().ptr_eq(&coprod_case_spec()));
}

#[test]
fn type_specs_are_shared_singletons() {
    assert!(prod_spec().ptr_eq(&prod_spec()));
    assert!(coprod_spec().ptr_eq(&coprod_spec()));
}

#[test]
fn distinct_specs_are_not_ptr_eq() {
    assert!(!prod_spec().ptr_eq(&coprod_spec()));
}

// ============================================================================
// 4. Structure / Display
// ============================================================================

#[test]
fn prod_type_is_spec_with_label_and_args() {
    let p = prod(Type::nat(), Type::int());
    match p.kind() {
        TypeKind::Spec(spec, args) => {
            assert_eq!(spec.symbol().label(), "prod");
            assert_eq!(args.as_slice(), &[Type::nat(), Type::int()]);
        }
        other => panic!("expected TypeKind::Spec, got {other:?}"),
    }
}

#[test]
fn coprod_type_is_spec_with_label_and_args() {
    let c = coprod(Type::nat(), Type::int());
    match c.kind() {
        TypeKind::Spec(spec, args) => {
            assert_eq!(spec.symbol().label(), "coprod");
            assert_eq!(args.as_slice(), &[Type::nat(), Type::int()]);
        }
        other => panic!("expected TypeKind::Spec, got {other:?}"),
    }
}

#[test]
fn prod_type_display() {
    assert_eq!(format!("{}", prod(Type::nat(), Type::int())), "(prod nat int)");
}

#[test]
fn coprod_type_display() {
    assert_eq!(
        format!("{}", coprod(Type::nat(), Type::int())),
        "(coprod nat int)"
    );
}

#[test]
fn constructor_term_kinds_and_labels() {
    // Each constructor term is a `TermKind::Spec` leaf carrying its
    // catalogue label and positional type arguments.
    match pair(Type::nat(), Type::int()).kind() {
        TermKind::Spec(spec, args) => {
            assert_eq!(spec.symbol().label(), "prod.pair");
            assert_eq!(args.as_slice(), &[Type::nat(), Type::int()]);
        }
        other => panic!("expected TermKind::Spec, got {other:?}"),
    }
    match inl(Type::nat(), Type::int()).kind() {
        TermKind::Spec(spec, _) => assert_eq!(spec.symbol().label(), "coprod.inl"),
        other => panic!("expected TermKind::Spec, got {other:?}"),
    }
    match inr(Type::nat(), Type::int()).kind() {
        TermKind::Spec(spec, _) => assert_eq!(spec.symbol().label(), "coprod.inr"),
        other => panic!("expected TermKind::Spec, got {other:?}"),
    }
    match fst(Type::nat(), Type::int()).kind() {
        TermKind::Spec(spec, _) => assert_eq!(spec.symbol().label(), "prod.fst"),
        other => panic!("expected TermKind::Spec, got {other:?}"),
    }
    match snd(Type::nat(), Type::int()).kind() {
        TermKind::Spec(spec, _) => assert_eq!(spec.symbol().label(), "prod.snd"),
        other => panic!("expected TermKind::Spec, got {other:?}"),
    }
    match coprod_case(Type::nat(), Type::int(), Type::bool()).kind() {
        TermKind::Spec(spec, args) => {
            assert_eq!(spec.symbol().label(), "coprod.case");
            assert_eq!(args.len(), 3);
        }
        other => panic!("expected TermKind::Spec, got {other:?}"),
    }
}

#[test]
fn constructor_term_display() {
    // Non-empty type args render as `(label arg...)`.
    assert_eq!(
        format!("{}", pair(Type::nat(), Type::int())),
        "(prod.pair nat int)"
    );
    assert_eq!(
        format!("{}", inl(Type::nat(), Type::int())),
        "(coprod.inl nat int)"
    );
    assert_eq!(
        format!("{}", coprod_case(Type::nat(), Type::int(), Type::bool())),
        "(coprod.case nat int bool)"
    );
}

// ============================================================================
// 5. Edge cases
// ============================================================================

/// Both arguments the same type: `prod nat nat`.
#[test]
fn prod_same_type_both_args() {
    let p = prod(Type::nat(), Type::nat());
    match p.kind() {
        TypeKind::Spec(spec, args) => {
            assert_eq!(spec.symbol().label(), "prod");
            assert_eq!(args.as_slice(), &[Type::nat(), Type::nat()]);
        }
        other => panic!("expected TypeKind::Spec, got {other:?}"),
    }
    // pair nat nat : nat → nat → prod nat nat
    let expected = Type::fun(
        Type::nat(),
        Type::fun(Type::nat(), prod(Type::nat(), Type::nat())),
    );
    assert_eq!(pair(Type::nat(), Type::nat()).type_of().unwrap(), expected);
}

#[test]
fn coprod_same_type_both_args() {
    let c = coprod(Type::int(), Type::int());
    match c.kind() {
        TypeKind::Spec(spec, args) => {
            assert_eq!(spec.symbol().label(), "coprod");
            assert_eq!(args.as_slice(), &[Type::int(), Type::int()]);
        }
        other => panic!("expected TypeKind::Spec, got {other:?}"),
    }
    // inl int int and inr int int both target coprod int int.
    assert_eq!(
        inl(Type::int(), Type::int()).type_of().unwrap(),
        Type::fun(Type::int(), coprod(Type::int(), Type::int()))
    );
    assert_eq!(
        inr(Type::int(), Type::int()).type_of().unwrap(),
        Type::fun(Type::int(), coprod(Type::int(), Type::int()))
    );
}

/// Nested: `coprod (prod nat int) unit`.
#[test]
fn nested_coprod_of_prod_and_unit() {
    let left = prod(Type::nat(), Type::int());
    let c = coprod(left.clone(), Type::unit());
    match c.kind() {
        TypeKind::Spec(spec, args) => {
            assert_eq!(spec.symbol().label(), "coprod");
            assert_eq!(args.as_slice(), &[left.clone(), Type::unit()]);
            // The first arg is itself a `prod` Spec.
            assert!(matches!(args[0].kind(), TypeKind::Spec(s, _) if s.symbol().label() == "prod"));
        }
        other => panic!("expected TypeKind::Spec, got {other:?}"),
    }
    // inl (prod nat int) unit : (prod nat int) → coprod (prod nat int) unit
    let expected = Type::fun(left.clone(), c.clone());
    assert_eq!(inl(left, Type::unit()).type_of().unwrap(), expected);
}

/// Nested: `prod (coprod nat int) (prod bool unit)`.
#[test]
fn deeply_nested_prod() {
    let inner_l = coprod(Type::nat(), Type::int());
    let inner_r = prod(Type::bool(), Type::unit());
    let p = prod(inner_l.clone(), inner_r.clone());
    let expected = Type::fun(
        inner_l.clone(),
        Type::fun(inner_r.clone(), prod(inner_l.clone(), inner_r.clone())),
    );
    assert_eq!(pair(inner_l, inner_r).type_of().unwrap(), expected);
    assert_eq!(
        format!("{p}"),
        "(prod (coprod nat int) (prod bool unit))"
    );
}

/// `coprod_case` where γ differs from both α and β.
#[test]
fn coprod_case_distinct_result_type() {
    let (a, b, c) = (Type::nat(), Type::int(), Type::unit());
    let expected = Type::fun(
        Type::fun(a.clone(), c.clone()),
        Type::fun(
            Type::fun(b.clone(), c.clone()),
            Type::fun(coprod(a.clone(), b.clone()), c.clone()),
        ),
    );
    assert_eq!(coprod_case(a, b, c).type_of().unwrap(), expected);
}

/// `coprod_case` collapsing to a single result type equal to one input
/// (γ == α): `coprodCase nat int nat`.
#[test]
fn coprod_case_result_equals_left() {
    let (a, b, c) = (Type::nat(), Type::int(), Type::nat());
    let expected = Type::fun(
        Type::fun(a.clone(), c.clone()),
        Type::fun(
            Type::fun(b.clone(), c.clone()),
            Type::fun(coprod(a.clone(), b.clone()), c.clone()),
        ),
    );
    assert_eq!(coprod_case(a, b, c).type_of().unwrap(), expected);
}

/// Coercions involving `unit`: `coprod nat unit` (option-like).
#[test]
fn coprod_with_unit_right() {
    let c = coprod(Type::nat(), Type::unit());
    assert_eq!(format!("{c}"), "(coprod nat unit)");
    // inr nat unit : unit → coprod nat unit
    assert_eq!(
        inr(Type::nat(), Type::unit()).type_of().unwrap(),
        Type::fun(Type::unit(), c.clone())
    );
    // inl nat unit : nat → coprod nat unit
    assert_eq!(
        inl(Type::nat(), Type::unit()).type_of().unwrap(),
        Type::fun(Type::nat(), c)
    );
}

/// `prod unit unit` — degenerate but well-formed.
#[test]
fn prod_unit_unit() {
    let p = prod(Type::unit(), Type::unit());
    assert_eq!(format!("{p}"), "(prod unit unit)");
    let expected = Type::fun(Type::unit(), Type::fun(Type::unit(), p));
    assert_eq!(
        pair(Type::unit(), Type::unit()).type_of().unwrap(),
        expected
    );
}
