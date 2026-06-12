//! Semi-trusted derived-type / derived-term catalogue.
//!
//! This module is the home of the kernel's canonical
//! `TypeSpec` / `TermSpec` definitions — see
//! `docs/type-hierarchy.md` for the design vision.
//!
//! ## Trust status
//!
//! Code here is *semi-trusted*: a bug cannot forge a `Thm`
//! (the `Thm`-constructing rules live in `crate::thm`, which is
//! the only piece of the kernel users have to fully trust). But
//! these definitions *do* connect to computation — e.g.
//! `natAdd : nat → nat → nat` is a `TermSpec` that the reduction
//! mechanism recognises by pointer identity — so an incorrect
//! definition here would let the kernel reduce a closed arithmetic
//! expression to the wrong value. We treat it as audit-required
//! even though it's "below" `thm`.
//!
//! ## Module layout
//!
//! Each concept gets its own file at the root of `defs/`. Submodules
//! import each other freely — `option` depends on `coprod` for the
//! eventual unfolding of `option α := coprod α unit`, `list` depends
//! on `option` for its constructor, `blob` depends on `list`/widths,
//! and so on. The `helpers` module hosts the `close_spec`/`quot_spec`
//! factories and a few small utilities shared by every spec entry.

#[macro_use]
mod macros;

mod blob;
mod canonical;
mod coprod;
mod floats;
mod helpers;
mod int;
mod list;
mod nat;
mod option;
mod prod;
mod rat;
mod real;
mod rel;
mod result;
mod set;
mod sigs;
mod spec;
mod stream;
mod symbol;

pub use blob::{blob_spec, blob_ty};
pub use canonical::Canonical;
pub use coprod::{
    bit_spec, bit_ty, coprod, coprod_spec, result, result_spec, u128_spec, u128_ty, u16_spec,
    u16_ty, u2_spec, u2_ty, u256_spec, u256_ty, u32_spec, u32_ty, u4_spec, u4_ty, u512_spec,
    u512_ty, u64_spec, u64_ty, u8_spec, u8_ty,
};
pub use floats::{f32_spec, f32_ty, f64_spec, f64_ty};
pub use helpers::{close_spec, quot_spec};
pub use int::{
    int_abs, int_abs_spec, int_add, int_add_spec, int_div, int_div_spec, int_le, int_le_spec,
    int_lt, int_lt_spec, int_mod, int_mod_spec, int_mul, int_mul_spec, int_neg, int_neg_spec,
    int_pred, int_pred_spec, int_sgn, int_sgn_spec, int_sub, int_sub_spec, int_succ,
    int_succ_spec, int_zero,
};
pub use list::{
    cons, cons_spec, head, head_spec, list, list_cat, list_cat_spec, list_filter, list_filter_spec,
    list_flatten, list_flatten_spec, list_foldl, list_foldl_spec, list_foldr, list_foldr_spec,
    list_index, list_index_spec, list_length, list_length_spec, list_map, list_map_spec,
    list_repeat, list_repeat_spec, list_skip, list_skip_spec, list_spec, list_take, list_take_spec,
    nil, nil_spec, tail, tail_spec,
};
pub use nat::{
    iter, iter_spec, nat_add, nat_add_spec, nat_bit_and, nat_bit_and_spec, nat_bit_or,
    nat_bit_or_spec, nat_bit_xor, nat_bit_xor_spec, nat_div, nat_div_spec, nat_from_bytes_be,
    nat_from_bytes_be_spec, nat_from_bytes_le, nat_from_bytes_le_spec, nat_le, nat_le_spec, nat_lt,
    nat_lt_spec, nat_mod, nat_mod_spec, nat_mul, nat_mul_spec, nat_pow, nat_pow_spec,
    nat_pred, nat_pred_spec, nat_rec, nat_rec_spec, nat_shl, nat_shl_spec, nat_shr, nat_shr_spec,
    nat_sub, nat_sub_spec, nat_succ, nat_succ_spec, nat_to_bytes_be, nat_to_bytes_be_spec,
    nat_to_bytes_le, nat_to_bytes_le_spec, nat_to_int, nat_to_int_spec,
};
pub use option::{none, none_spec, option, option_spec, some, some_spec};
pub use prod::{prod, prod_spec, signed1, signed1_spec, signed2, signed2_spec};
pub use rat::{field_of_fractions, field_of_fractions_spec, rat_spec, rat_ty};
pub use real::{real_spec, real_ty};
pub use rel::{
    part, part_spec, per, per_spec, pord, pord_spec, preord, preord_spec, rel, rel_spec,
};
pub use result::{err, err_spec, ok, ok_spec};
pub use set::{
    list_to_set, list_to_set_spec, set, set_card, set_card_spec, set_diff, set_diff_spec,
    set_intersect, set_intersect_spec, set_spec, set_subset, set_subset_spec, set_union,
    set_union_spec,
};
pub use spec::{TermSpec, TypeSpec};
pub use stream::{stream, stream_spec};
pub use symbol::{Opacity, Symbol};

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Type, TypeKind};

    #[test]
    fn set_alpha_round_trip() {
        let s_nat = set(Type::nat());
        match s_nat.kind() {
            TypeKind::Spec(spec, args) => {
                assert_eq!(spec.symbol().label(), "set");
                assert_eq!(args.len(), 1);
                assert_eq!(&args[0], &Type::nat());
            }
            _ => panic!("expected TypeKind::Spec, got {s_nat:?}"),
        }
    }

    #[test]
    fn set_lazy_static_is_shared() {
        assert!(set_spec().ptr_eq(&set_spec()));
    }

    #[test]
    fn rel_two_args() {
        let r = rel(Type::nat(), Type::int());
        match r.kind() {
            TypeKind::Spec(spec, args) => {
                assert_eq!(spec.symbol().label(), "rel");
                assert_eq!(args.len(), 2);
                assert_eq!(&args[0], &Type::nat());
                assert_eq!(&args[1], &Type::int());
            }
            _ => panic!("expected TypeKind::Spec, got {r:?}"),
        }
    }

    #[test]
    fn set_display_with_args() {
        let s = set(Type::nat());
        assert_eq!(format!("{s}"), "(set nat)");
    }

    #[test]
    fn nat_add_spec_carries_definitional_body() {
        // natAdd is now a `let` definition: tm is the lambda body
        // λn m. natRec[nat] m (λ_ acc. succ acc) n, of type
        // nat → nat → nat (matching the spec's `ty`).
        let spec = nat_add_spec();
        let tm = spec.tm().expect("nat_add carries its body");
        let ty = tm.type_of().expect("body type-checks");
        let expected = Type::fun(Type::nat(), Type::fun(Type::nat(), Type::nat()));
        assert_eq!(ty, expected);
        // And the spec's recorded ty matches.
        assert_eq!(spec.ty(), Some(&expected));
    }

    #[test]
    fn iter_spec_body_well_typed() {
        // iter : nat → (α → α) → α → α
        let spec = iter_spec();
        let tm = spec.tm().expect("iter has body");
        let ty = tm.type_of().expect("iter body type-checks");
        let alpha = Type::tfree("a");
        let f_ty = Type::fun(alpha.clone(), alpha.clone());
        let expected = Type::fun(
            Type::nat(),
            Type::fun(f_ty, Type::fun(alpha.clone(), alpha)),
        );
        assert_eq!(ty, expected);
    }

    #[test]
    fn iter_at_nat_round_trip() {
        let t = iter(Type::nat());
        let expected = Type::fun(
            Type::nat(),
            Type::fun(
                Type::fun(Type::nat(), Type::nat()),
                Type::fun(Type::nat(), Type::nat()),
            ),
        );
        assert_eq!(t.type_of().unwrap(), expected);
    }

    #[test]
    fn nat_rec_spec_predicate_well_typed() {
        // natRec's predicate is `λr. ...` over `α → (nat → α → α) → nat → α`.
        let spec = nat_rec_spec();
        let tm = spec.tm().expect("nat_rec carries a predicate");
        let ty = tm.type_of().expect("predicate type-checks");
        let alpha = Type::tfree("a");
        let f_ty = Type::fun(Type::nat(), Type::fun(alpha.clone(), alpha.clone()));
        let r_ty = Type::fun(
            alpha.clone(),
            Type::fun(f_ty, Type::fun(Type::nat(), alpha)),
        );
        let expected = Type::fun(r_ty, Type::bool());
        assert_eq!(ty, expected);
    }

    #[test]
    fn nat_add_term_has_expected_type() {
        let t = nat_add();
        let nat = Type::nat();
        let expected = Type::fun(nat.clone(), Type::fun(nat.clone(), nat));
        assert_eq!(t.type_of().unwrap(), expected);
    }

    #[test]
    fn nat_le_term_has_expected_type() {
        let t = nat_le();
        let expected = Type::fun(Type::nat(), Type::fun(Type::nat(), Type::bool()));
        assert_eq!(t.type_of().unwrap(), expected);
    }

    #[test]
    fn int_add_term_has_expected_type() {
        let t = int_add();
        let int = Type::int();
        let expected = Type::fun(int.clone(), Type::fun(int.clone(), int));
        assert_eq!(t.type_of().unwrap(), expected);
    }

    #[test]
    fn nat_add_spec_is_shared_singleton() {
        assert!(nat_add_spec().ptr_eq(&nat_add_spec()));
    }

    #[test]
    fn nat_add_term_display() {
        assert_eq!(format!("{}", nat_add()), "natAdd");
    }

    #[test]
    fn coprod_type_builds() {
        let c = coprod(Type::nat(), Type::int());
        match c.kind() {
            TypeKind::Spec(spec, args) => {
                assert_eq!(spec.symbol().label(), "coprod");
                assert_eq!(args.len(), 2);
                assert_eq!(&args[0], &Type::nat());
                assert_eq!(&args[1], &Type::int());
            }
            _ => panic!("expected TypeKind::Spec, got {c:?}"),
        }
    }

    #[test]
    fn coprod_predicate_well_typed() {
        let spec = coprod_spec();
        let tm = spec.tm().expect("coprod has predicate");
        let ty = tm
            .type_of()
            .unwrap_or_else(|e| panic!("coprod predicate type-of: {e:?}"));
        let alpha = Type::tfree("a");
        let beta = Type::tfree("b");
        let carrier = Type::fun(alpha, Type::fun(beta, Type::bool()));
        let expected = Type::fun(carrier, Type::bool());
        assert_eq!(ty, expected);
    }

    #[test]
    fn prod_predicate_well_typed() {
        let spec = prod_spec();
        let tm = spec.tm().expect("prod has predicate");
        let ty = tm.type_of().expect("prod predicate type-of");
        let alpha = Type::tfree("a");
        let beta = Type::tfree("b");
        let carrier = Type::fun(alpha, Type::fun(beta, Type::bool()));
        let expected = Type::fun(carrier, Type::bool());
        assert_eq!(ty, expected);
    }

    #[test]
    fn option_type_builds() {
        let o = option(Type::nat());
        match o.kind() {
            TypeKind::Spec(spec, args) => {
                assert_eq!(spec.symbol().label(), "option");
                assert_eq!(args.len(), 1);
                assert_eq!(&args[0], &Type::nat());
            }
            _ => panic!("expected TypeKind::Spec, got {o:?}"),
        }
    }

    #[test]
    fn bit_is_zero_ary_spec() {
        let b = bit_ty();
        match b.kind() {
            TypeKind::Spec(spec, args) => {
                assert_eq!(spec.symbol().label(), "bit");
                assert!(args.is_empty(), "bit takes no type args");
            }
            _ => panic!("expected TypeKind::Spec, got {b:?}"),
        }
    }

    #[test]
    fn fixed_width_chain_doubles() {
        let u2_spec = u2_spec();
        let carrier = u2_spec.ty().expect("u2 has carrier");
        let expected = Type::fun(bit_ty(), Type::fun(bit_ty(), Type::bool()));
        assert_eq!(carrier, &expected);

        let u4_spec = u4_spec();
        let carrier = u4_spec.ty().expect("u4 has carrier");
        let expected = Type::fun(u2_ty(), Type::fun(u2_ty(), Type::bool()));
        assert_eq!(carrier, &expected);

        let u64_spec = u64_spec();
        let carrier = u64_spec.ty().expect("u64 has carrier");
        let expected = Type::fun(u32_ty(), Type::fun(u32_ty(), Type::bool()));
        assert_eq!(carrier, &expected);
    }

    #[test]
    fn all_fixed_widths_have_well_typed_predicates() {
        for spec in [
            bit_spec(),
            u2_spec(),
            u4_spec(),
            u8_spec(),
            u16_spec(),
            u32_spec(),
            u64_spec(),
            u128_spec(),
            u256_spec(),
            u512_spec(),
        ] {
            let label = spec.symbol().label().to_string();
            let tm = spec.tm().expect("has tm");
            let ty = tm
                .type_of()
                .unwrap_or_else(|e| panic!("{label} predicate type-of: {e:?}"));
            let carrier = spec.ty().expect("has ty").clone();
            let expected = Type::fun(carrier, Type::bool());
            assert_eq!(ty, expected, "{label}");
        }
    }

    #[test]
    fn all_relation_property_specs_well_typed() {
        for spec in [preord_spec(), pord_spec(), per_spec(), part_spec()] {
            let label = spec.symbol().label().to_string();
            let tm = spec.tm().expect("has tm");
            let ty = tm
                .type_of()
                .unwrap_or_else(|e| panic!("{label} predicate type-of: {e:?}"));
            let carrier = spec.ty().expect("has ty").clone();
            let expected = Type::fun(carrier, Type::bool());
            assert_eq!(ty, expected, "{label}");
        }
    }

    #[test]
    fn preord_at_nat_round_trip() {
        let p = preord(Type::nat());
        match p.kind() {
            TypeKind::Spec(spec, args) => {
                assert_eq!(spec.symbol().label(), "preord");
                assert_eq!(args.len(), 1);
                assert_eq!(&args[0], &Type::nat());
            }
            _ => panic!("expected TypeKind::Spec, got {p:?}"),
        }
    }

    #[test]
    fn some_at_nat_has_expected_type() {
        let s = some(Type::nat());
        let expected = Type::fun(Type::nat(), option(Type::nat()));
        assert_eq!(s.type_of().unwrap(), expected);
    }

    #[test]
    fn none_at_nat_has_expected_type() {
        let n = none(Type::nat());
        assert_eq!(n.type_of().unwrap(), option(Type::nat()));
    }

    #[test]
    fn cons_at_nat_has_expected_type() {
        let c = cons(Type::nat());
        let expected = Type::fun(
            Type::nat(),
            Type::fun(list(Type::nat()), list(Type::nat())),
        );
        assert_eq!(c.type_of().unwrap(), expected);
    }

    #[test]
    fn nil_at_nat_has_expected_type() {
        let n = nil(Type::nat());
        assert_eq!(n.type_of().unwrap(), list(Type::nat()));
    }

    #[test]
    fn ok_at_nat_int_has_expected_type() {
        let o = ok(Type::nat(), Type::int());
        let expected = Type::fun(Type::nat(), result(Type::nat(), Type::int()));
        assert_eq!(o.type_of().unwrap(), expected);
    }

    #[test]
    fn err_at_nat_int_has_expected_type() {
        let e = err(Type::nat(), Type::int());
        let expected = Type::fun(Type::int(), result(Type::nat(), Type::int()));
        assert_eq!(e.type_of().unwrap(), expected);
    }

    #[test]
    fn head_at_nat_has_expected_type() {
        let h = head(Type::nat());
        let expected = Type::fun(list(Type::nat()), option(Type::nat()));
        assert_eq!(h.type_of().unwrap(), expected);
    }

    #[test]
    fn rat_real_are_zero_ary_types() {
        let r = rat_ty();
        assert!(matches!(r.kind(), TypeKind::Spec(_, args) if args.is_empty()));
        let re = real_ty();
        assert!(matches!(re.kind(), TypeKind::Spec(_, args) if args.is_empty()));
    }

    #[test]
    fn close_spec_factory_well_typed() {
        let car = Type::int();
        let pred = int_le();
        let handle = close_spec(Canonical::Real, car, pred);
        let tm = handle.tm().expect("close: has tm");
        let ty = tm.type_of().expect("close predicate type-of");
        let expected = Type::fun(Type::fun(Type::int(), Type::bool()), Type::bool());
        assert_eq!(ty, expected);
    }

    #[test]
    fn coprod_display_with_args() {
        let c = coprod(Type::nat(), Type::int());
        assert_eq!(format!("{c}"), "(coprod nat int)");
    }

    #[test]
    fn stream_alpha_round_trip() {
        let s = stream(Type::nat());
        match s.kind() {
            TypeKind::Spec(spec, args) => {
                assert_eq!(spec.symbol().label(), "stream");
                assert_eq!(args.len(), 1);
                assert_eq!(&args[0], &Type::nat());
            }
            _ => panic!("expected TypeKind::Spec, got {s:?}"),
        }
    }

    #[test]
    fn blob_carrier_is_list_u8() {
        // After flattening, blob's carrier should be exactly `list u8`
        // (using the catalogue's list spec, not a raw stream-of-option).
        let b = blob_ty();
        assert_eq!(b, list(u8_ty()));
    }

    #[test]
    fn canonical_labels_match_doc_text() {
        assert_eq!(Canonical::Set.label(), "set");
        assert_eq!(Canonical::Coprod.label(), "coprod");
        assert_eq!(Canonical::Option.label(), "option");
        assert_eq!(Canonical::FieldOfFractions.label(), "fieldOfFractions");
        assert_eq!(Canonical::Real.label(), "real");
    }

    #[test]
    fn canonical_is_transparent() {
        assert_eq!(
            <Canonical as Symbol>::opacity(&Canonical::Set),
            Opacity::Transparent
        );
    }

    #[test]
    fn smolstr_is_opaque() {
        let s: smol_str::SmolStr = "foo".into();
        assert_eq!(<smol_str::SmolStr as Symbol>::opacity(&s), Opacity::Opaque);
    }

    #[test]
    fn typespec_construction_round_trips() {
        let spec = TypeSpec::new(
            Canonical::Set,
            Some(Type::fun(Type::tfree("a"), Type::bool())),
            None,
        );
        assert_eq!(spec.symbol().label(), "set");
        assert!(spec.ty().is_some());
        assert!(spec.tm().is_none());
    }

    #[test]
    fn termspec_construction_round_trips() {
        let spec = TermSpec::new(Canonical::List, Some(Type::tfree("a")), None);
        assert_eq!(spec.symbol().label(), "list");
    }

    #[test]
    fn user_supplied_smolstr_symbol_is_opaque() {
        // A user-supplied SmolStr symbol carries opaque equality:
        // two specs with the same SmolStr and same definition compare
        // equal, two with different SmolStrs (even same definition)
        // do not.
        let a: smol_str::SmolStr = "myType".into();
        let b: smol_str::SmolStr = "myType".into();
        let c: smol_str::SmolStr = "otherType".into();
        let ty = Some(Type::tfree("a"));
        let s1 = TypeSpec::new(a, ty.clone(), None);
        let s2 = TypeSpec::new(b, ty.clone(), None);
        let s3 = TypeSpec::new(c, ty, None);
        assert_eq!(s1, s2);
        assert_ne!(s1, s3);
    }
}
