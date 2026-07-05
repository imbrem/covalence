//! Integration tests for the `list` and `stream` `defs/` catalogue
//! entries of `covalence-core`.
//!
//! `list α := stream (option α) where finite`; `stream α := nat → α`
//! (opaque wrapper). We test only *types*, definition-body presence
//! and shape, structural form of the `TypeKind::Spec` leaves, and
//! handle identity. The kernel does not prove equations, so we never
//! assert derived equalities (e.g. `head (cons x xs) = some x`).

use covalence_core::{Type, TypeKind};
use covalence_hol_eval::defs::*;

// ============================================================================
// Helpers
// ============================================================================

/// Assert `ty` is a `TypeKind::Spec` with the given label and type args.
fn assert_spec(ty: &Type, label: &str, args: &[Type]) {
    match ty.kind() {
        TypeKind::Spec(spec, got_args) => {
            assert_eq!(spec.symbol().label(), label, "label mismatch for {ty:?}");
            assert_eq!(got_args.as_slice(), args, "type-arg mismatch for {ty:?}");
        }
        other => panic!("expected TypeKind::Spec({label}), got {other:?}"),
    }
}

// ============================================================================
// 1. list type structure
// ============================================================================

#[test]
fn list_nat_is_spec_leaf() {
    assert_spec(&list(Type::nat()), "list", &[Type::nat()]);
}

#[test]
fn list_int_is_spec_leaf() {
    assert_spec(&list(Type::int()), "list", &[Type::int()]);
}

#[test]
fn list_tfree_is_spec_leaf() {
    let a = Type::tfree("a");
    assert_spec(&list(a.clone()), "list", &[a]);
}

#[test]
fn list_spec_carrier_is_stream_of_option() {
    // `list α := stream (option α) where finite` — the carrier is the
    // spec'd `stream (option α-as-tfree-a)`.
    let carrier = stream(option(Type::tfree("a")));
    assert_eq!(list_spec().ty(), Some(&carrier));
}

#[test]
fn list_spec_has_finite_selector_predicate() {
    // The subtype selector predicate is the `finite` predicate.
    assert!(list_spec().tm().is_some(), "list has a selector predicate");
}

#[test]
fn list_spec_is_shared_singleton() {
    assert!(list_spec().ptr_eq(&list_spec()));
}

// ============================================================================
// 2. list constructor / destructor types
// ============================================================================

#[test]
fn nil_has_list_type() {
    // nil : list α  (at nat)
    assert_eq!(nil(Type::nat()).type_of().unwrap(), list(Type::nat()));
    // and at int
    assert_eq!(nil(Type::int()).type_of().unwrap(), list(Type::int()));
}

#[test]
fn nil_at_tfree_has_list_type() {
    let a = Type::tfree("a");
    assert_eq!(nil(a.clone()).type_of().unwrap(), list(a));
}

#[test]
fn cons_has_curried_prepend_type() {
    // cons : α → list α → list α
    let a = Type::nat();
    let expected = Type::fun(a.clone(), Type::fun(list(a.clone()), list(a)));
    assert_eq!(cons(Type::nat()).type_of().unwrap(), expected);
}

#[test]
fn cons_at_int_has_curried_prepend_type() {
    let a = Type::int();
    let expected = Type::fun(a.clone(), Type::fun(list(a.clone()), list(a)));
    assert_eq!(cons(Type::int()).type_of().unwrap(), expected);
}

#[test]
fn head_has_list_to_option_type() {
    // head : list α → option α
    let a = Type::nat();
    let expected = Type::fun(list(a.clone()), option(a));
    assert_eq!(head(Type::nat()).type_of().unwrap(), expected);
}

#[test]
fn head_at_tfree_has_list_to_option_type() {
    let a = Type::tfree("a");
    let expected = Type::fun(list(a.clone()), option(a));
    assert_eq!(head(Type::tfree("a")).type_of().unwrap(), expected);
}

#[test]
fn tail_has_list_to_list_type() {
    // tail : list α → list α
    let a = Type::int();
    let expected = Type::fun(list(a.clone()), list(a));
    assert_eq!(tail(Type::int()).type_of().unwrap(), expected);
}

#[test]
fn list_index_has_nat_to_list_to_option_type() {
    // listIndex : nat → list α → option α
    let a = Type::nat();
    let expected = Type::fun(Type::nat(), Type::fun(list(a.clone()), option(a)));
    assert_eq!(list_index(Type::nat()).type_of().unwrap(), expected);
}

#[test]
fn list_index_at_tfree_type() {
    let a = Type::tfree("a");
    let expected = Type::fun(Type::nat(), Type::fun(list(a.clone()), option(a)));
    assert_eq!(list_index(Type::tfree("a")).type_of().unwrap(), expected);
}

// ============================================================================
// 3. Defined list ops have bodies, and the body type matches the spec ty
// ============================================================================

#[test]
fn defined_list_ops_carry_bodies_matching_their_ty() {
    // Constructors/destructors plus the `let`-style ops are *defined*
    // (via the stream carrier bridge or via foldr). Each carries a body
    // whose type matches the recorded spec ty. (foldr/foldl are
    // ε-predicate ops — checked separately, since their body type is
    // `ty → bool`.)
    let specs = [
        ("nil", nil_spec()),
        ("cons", cons_spec()),
        ("head", head_spec()),
        ("tail", tail_spec()),
        ("listIndex", list_index_spec()),
        ("listLength", list_length_spec()),
        ("listCat", list_cat_spec()),
        ("listMap", list_map_spec()),
        ("listFilter", list_filter_spec()),
        ("listTake", list_take_spec()),
        ("listSkip", list_skip_spec()),
        ("listRepeat", list_repeat_spec()),
        ("listFlatten", list_flatten_spec()),
    ];
    for (name, spec) in specs {
        let tm = spec
            .tm()
            .unwrap_or_else(|| panic!("{name} should carry a definition body"));
        let ty = tm
            .type_of()
            .unwrap_or_else(|e| panic!("{name} body type-of: {e:?}"));
        let recorded = spec
            .ty()
            .unwrap_or_else(|| panic!("{name} has a recorded ty"));
        assert_eq!(&ty, recorded, "{name}: body type vs recorded ty");
    }
}

#[test]
fn nil_body_type_is_list() {
    let spec = nil_spec();
    let tm = spec.tm().expect("nil has a body");
    assert_eq!(tm.type_of().unwrap(), list(Type::tfree("a")));
}

#[test]
fn cons_body_type_is_curried_prepend() {
    let a = Type::tfree("a");
    let spec = cons_spec();
    let tm = spec.tm().expect("cons has a body");
    let expected = Type::fun(a.clone(), Type::fun(list(a.clone()), list(a)));
    assert_eq!(tm.type_of().unwrap(), expected);
}

// ============================================================================
// 4. Structural recursors: ε-predicate ops (listFoldr / listFoldl)
// ============================================================================

#[test]
fn fold_recursors_carry_selector_predicates() {
    // listFoldr / listFoldl are def-style: their `tm` is a Hilbert-ε
    // selector predicate over the fold function, so its type is
    // `ty → bool` (NOT the recorded function `ty` itself).
    let specs = [
        ("listFoldr", list_foldr_spec()),
        ("listFoldl", list_foldl_spec()),
    ];
    for (name, spec) in specs {
        let recorded = spec
            .ty()
            .unwrap_or_else(|| panic!("{name} has a committed ty"));
        let pred = spec
            .tm()
            .unwrap_or_else(|| panic!("{name} carries a selector predicate"));
        let pred_ty = pred
            .type_of()
            .unwrap_or_else(|e| panic!("{name} predicate type-of: {e:?}"));
        let expected = Type::fun(recorded.clone(), Type::bool());
        assert_eq!(pred_ty, expected, "{name}: predicate is `ty → bool`");
    }
}

#[test]
fn list_length_has_list_to_nat_type() {
    // listLength : list α → nat
    let a = Type::nat();
    let expected = Type::fun(list(a), Type::nat());
    assert_eq!(list_length(Type::nat()).type_of().unwrap(), expected);
}

#[test]
fn list_cat_has_binary_list_type() {
    // listCat : list α → list α → list α
    let a = Type::nat();
    let la = list(a);
    let expected = Type::fun(la.clone(), Type::fun(la.clone(), la));
    assert_eq!(list_cat(Type::nat()).type_of().unwrap(), expected);
}

#[test]
fn list_map_has_two_type_args_function_type() {
    // listMap : (α → β) → list α → list β
    let a = Type::nat();
    let b = Type::int();
    let f_ty = Type::fun(a.clone(), b.clone());
    let expected = Type::fun(f_ty, Type::fun(list(a), list(b)));
    assert_eq!(
        list_map(Type::nat(), Type::int()).type_of().unwrap(),
        expected
    );
}

#[test]
fn list_filter_has_predicate_list_type() {
    // listFilter : (α → bool) → list α → list α
    let a = Type::nat();
    let p_ty = Type::fun(a.clone(), Type::bool());
    let la = list(a);
    let expected = Type::fun(p_ty, Type::fun(la.clone(), la));
    assert_eq!(list_filter(Type::nat()).type_of().unwrap(), expected);
}

#[test]
fn list_foldr_has_expected_type() {
    // listFoldr : (α → β → β) → β → list α → β
    let a = Type::nat();
    let b = Type::int();
    let f_ty = Type::fun(a.clone(), Type::fun(b.clone(), b.clone()));
    let expected = Type::fun(f_ty, Type::fun(b.clone(), Type::fun(list(a), b)));
    assert_eq!(
        list_foldr(Type::nat(), Type::int()).type_of().unwrap(),
        expected
    );
}

#[test]
fn list_foldl_has_expected_type() {
    // listFoldl : (β → α → β) → β → list α → β
    let a = Type::nat();
    let b = Type::int();
    let f_ty = Type::fun(b.clone(), Type::fun(a.clone(), b.clone()));
    let expected = Type::fun(f_ty, Type::fun(b.clone(), Type::fun(list(a), b)));
    assert_eq!(
        list_foldl(Type::nat(), Type::int()).type_of().unwrap(),
        expected
    );
}

#[test]
fn list_take_and_skip_have_nat_list_list_type() {
    // listTake / listSkip : nat → list α → list α
    let a = Type::nat();
    let la = list(a);
    let expected = Type::fun(Type::nat(), Type::fun(la.clone(), la));
    assert_eq!(list_take(Type::nat()).type_of().unwrap(), expected);
    assert_eq!(list_skip(Type::nat()).type_of().unwrap(), expected);
}

#[test]
fn list_repeat_has_nat_elem_list_type() {
    // listRepeat : nat → α → list α
    let a = Type::int();
    let expected = Type::fun(Type::nat(), Type::fun(a.clone(), list(a)));
    assert_eq!(list_repeat(Type::int()).type_of().unwrap(), expected);
}

#[test]
fn list_flatten_has_nested_list_type() {
    // listFlatten : list (list α) → list α
    let a = Type::nat();
    let expected = Type::fun(list(list(a.clone())), list(a));
    assert_eq!(list_flatten(Type::nat()).type_of().unwrap(), expected);
}

// ============================================================================
// 5. stream type + stream ops
// ============================================================================

#[test]
fn stream_nat_is_spec_leaf() {
    assert_spec(&stream(Type::nat()), "stream", &[Type::nat()]);
}

#[test]
fn stream_int_is_spec_leaf() {
    assert_spec(&stream(Type::int()), "stream", &[Type::int()]);
}

#[test]
fn stream_spec_carrier_is_nat_to_tfree() {
    // `stream α := nat → α`; carrier (at tfree a) is `nat → a`.
    let carrier = Type::fun(Type::nat(), Type::tfree("a"));
    assert_eq!(stream_spec().ty(), Some(&carrier));
}

#[test]
fn stream_spec_is_shared_singleton() {
    assert!(stream_spec().ptr_eq(&stream_spec()));
}

#[test]
fn stream_at_has_extract_type() {
    // streamAt : stream α → nat → α
    let a = Type::nat();
    let expected = Type::fun(stream(a.clone()), Type::fun(Type::nat(), a));
    assert_eq!(stream_at(Type::nat()).type_of().unwrap(), expected);
}

#[test]
fn stream_mk_has_build_type() {
    // streamMk : (nat → α) → stream α
    let a = Type::int();
    let expected = Type::fun(Type::fun(Type::nat(), a.clone()), stream(a));
    assert_eq!(stream_mk(Type::int()).type_of().unwrap(), expected);
}

#[test]
fn stream_head_has_stream_to_elem_type() {
    // streamHead : stream α → α
    let a = Type::nat();
    let expected = Type::fun(stream(a.clone()), a);
    assert_eq!(stream_head(Type::nat()).type_of().unwrap(), expected);
}

#[test]
fn stream_tail_has_stream_to_stream_type() {
    // streamTail : stream α → stream α
    let a = Type::int();
    let expected = Type::fun(stream(a.clone()), stream(a));
    assert_eq!(stream_tail(Type::int()).type_of().unwrap(), expected);
}

#[test]
fn stream_const_has_elem_to_stream_type() {
    // streamConst : α → stream α
    let a = Type::nat();
    let expected = Type::fun(a.clone(), stream(a));
    assert_eq!(stream_const(Type::nat()).type_of().unwrap(), expected);
}

#[test]
fn stream_iterate_has_expected_type() {
    // streamIterate : α → (α → α) → stream α
    let a = Type::nat();
    let f_ty = Type::fun(a.clone(), a.clone());
    let expected = Type::fun(a.clone(), Type::fun(f_ty, stream(a)));
    assert_eq!(stream_iterate(Type::nat()).type_of().unwrap(), expected);
}

#[test]
fn stream_nth_has_flipped_extract_type() {
    // streamNth : nat → stream α → α
    let a = Type::int();
    let expected = Type::fun(Type::nat(), Type::fun(stream(a.clone()), a));
    assert_eq!(stream_nth(Type::int()).type_of().unwrap(), expected);
}

#[test]
fn finite_has_stream_option_to_bool_type() {
    // finite : stream (option α) → bool
    let a = Type::nat();
    let expected = Type::fun(stream(option(a)), Type::bool());
    assert_eq!(finite(Type::nat()).type_of().unwrap(), expected);
}

// ============================================================================
// 5b. stream op bodies: defined vs declaration-only
// ============================================================================

#[test]
fn stream_bridge_ops_are_abs_rep_coercions() {
    // streamAt / streamMk are now `let`-defined as the newtype
    // rep / abs coercions, so each carries a body.
    assert!(stream_at_spec().tm().is_some(), "streamAt has a body (rep)");
    assert!(stream_mk_spec().tm().is_some(), "streamMk has a body (abs)");
}

#[test]
fn defined_stream_ops_carry_bodies_matching_their_ty() {
    // every stream op is defined in terms of the bridge ops (or, for
    // the bridge ops themselves, the abs/rep coercions); each has a
    // body whose type matches its recorded ty.
    let specs = [
        ("streamAt", stream_at_spec()),
        ("streamMk", stream_mk_spec()),
        ("streamHead", stream_head_spec()),
        ("streamTail", stream_tail_spec()),
        ("streamConst", stream_const_spec()),
        ("streamIterate", stream_iterate_spec()),
        ("streamNth", stream_nth_spec()),
        ("finite", finite_spec()),
    ];
    for (name, spec) in specs {
        let tm = spec
            .tm()
            .unwrap_or_else(|| panic!("{name} should carry a body"));
        let ty = tm
            .type_of()
            .unwrap_or_else(|e| panic!("{name} body type-of: {e:?}"));
        let recorded = spec
            .ty()
            .unwrap_or_else(|| panic!("{name} has a recorded ty"));
        assert_eq!(&ty, recorded, "{name}: body type vs recorded ty");
    }
}

// ============================================================================
// 6. Edge cases: nesting, option element types, tfree
// ============================================================================

#[test]
fn nested_list_of_list_nat() {
    // list (list nat) — outer spec leaf with one arg = list nat.
    let inner = list(Type::nat());
    let outer = list(inner.clone());
    assert_spec(&outer, "list", std::slice::from_ref(&inner));
    // inner arg is itself a list-spec leaf.
    assert_spec(&inner, "list", &[Type::nat()]);
}

#[test]
fn list_of_option_nat() {
    // list (option nat).
    let elem = option(Type::nat());
    let ty = list(elem.clone());
    assert_spec(&ty, "list", std::slice::from_ref(&elem));
    assert_spec(&elem, "option", &[Type::nat()]);
}

#[test]
fn stream_of_option_nat() {
    // stream (option nat) — exactly the carrier shape of `list nat`.
    let elem = option(Type::nat());
    let ty = stream(elem.clone());
    assert_spec(&ty, "stream", std::slice::from_ref(&elem));
    assert_spec(&elem, "option", &[Type::nat()]);
}

#[test]
fn list_of_tfree() {
    let a = Type::tfree("a");
    assert_spec(&list(a.clone()), "list", &[a]);
}

#[test]
fn nested_list_constructor_types_compose() {
    // cons at (list nat) : list nat → list (list nat) → list (list nat)
    let inner = list(Type::nat());
    let expected = Type::fun(
        inner.clone(),
        Type::fun(list(inner.clone()), list(inner.clone())),
    );
    assert_eq!(cons(inner).type_of().unwrap(), expected);
}

#[test]
fn head_at_list_nat_returns_option_of_list() {
    // head at (list nat) : list (list nat) → option (list nat)
    let inner = list(Type::nat());
    let expected = Type::fun(list(inner.clone()), option(inner));
    assert_eq!(head(list(Type::nat())).type_of().unwrap(), expected);
}

#[test]
fn finite_at_option_carrier_for_list_of_option() {
    // finite at (option nat) : stream (option (option nat)) → bool
    let inner = option(Type::nat());
    let expected = Type::fun(stream(option(inner.clone())), Type::bool());
    assert_eq!(finite(inner).type_of().unwrap(), expected);
}
