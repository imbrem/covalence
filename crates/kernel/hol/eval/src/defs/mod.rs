//! The **untrusted derived-term catalogue** — the `defs/` op/constant
//! definitions, moved out of the `covalence-core` TCB (stage E2 of
//! `notes/vibes/handoff/defs-out-of-core.md`).
//!
//! ## What lives here vs in core
//!
//! - **Here (untrusted data, eval tier):** the *term-op catalogue* — the
//!   nat/int/fixed-width/bytes arithmetic specs, the `fun`/`set`/`rel`/
//!   `rat`/`text`/`floats`/`result` families, the higher-order `list`
//!   ops, and the `.cov` bootstrap ([`cov`]). These sit **next to** the
//!   certificate rules (`crate::rules` / `crate::certs`) whose dispatch
//!   tables key on their canonical spec handles, and next to the native
//!   `covalence-pure-eval` CanonRules that compute them — the
//!   auditability goal: "what `nat.add` means in HOL" beside "what it
//!   computes natively".
//! - **In core (the D3 transitional residue, re-exported here):** the
//!   spec *machinery* (`TermSpec`/`TypeSpec`, the sealed
//!   [`Canonical`]/symbol trust layer) and the structural TYPE catalogue
//!   the literal leaves' `type_of` needs (`u8`…`s64`/`bits`, `int`,
//!   `bytes`, `unit` and their carrier chains: `prod`/`coprod`/`option`/
//!   `list`/`stream`, the logic connectives their bodies quantify with,
//!   and the residue-referenced term ops). That residue dies with the
//!   literal leaves (`TermKind::Nat/Int/SmallInt/Blob`) — see
//!   `crates/kernel/hol/core/SKELETONS.md`.
//!
//! Downstream code (`covalence-init`, `covalence-alethe`, …) should
//! import the catalogue from **here** (`covalence_hol_eval::defs`), which
//! re-exports the core residue flatly, so the eventual migration of the
//! remaining families is invisible to consumers.
//!
//! ## Trust status
//!
//! Definitions here are plain *data*: they cannot forge a `Thm`. Their
//! computational meaning enters through the eval-tier certificate rules
//! (`crate::rules`, gated by [`CoreEval`](crate::CoreEval)'s `admits`),
//! whose dispatch tables in `crate::certs` key on the canonical spec
//! handles defined here — a wrong definition + a matching table entry
//! is exactly the per-rule eval-tier trust this crate declares.

#[macro_use]
mod macros;

mod blob;
pub mod cov;
mod floats;
mod fun;
mod int;
pub mod int_ops;
mod list;
mod nat;
mod rat;
mod rel;
mod result;
mod set;
mod stream;
mod text;

/// The `covalence-core` residue (spec machinery + structural type
/// catalogue + residue term ops), re-exported flatly so this module is
/// the single import surface for the whole catalogue.
pub use covalence_core::defs::*;

pub use blob::{
    bytes_at, bytes_at_spec, bytes_cat, bytes_cat_spec, bytes_cons_nat, bytes_cons_nat_spec,
    bytes_len, bytes_len_spec, bytes_slice, bytes_slice_spec,
};
pub use cov::{CoreEnv, CovError, Entry, core_env, parse_core, term_str, type_str};
pub use floats::{
    FLOAT_CVT_TAGS, FloatKey, FloatOp, FloatWidth, TypedF64, as_f64_bits, f32_spec, f32_ty,
    f64_from_bits, f64_op, f64_op_spec, f64_spec, f64_to_bits, f64_ty, float_bits_op,
    float_bits_spec, lookup_f64_op, lookup_float_op, mk_f64,
};
pub use fun::{compose, compose_spec, flip, flip_spec, id, id_spec, konst, konst_spec};
pub use int::{
    int_abs, int_abs_spec, int_add, int_add_spec, int_div, int_div_spec, int_le, int_le_spec,
    int_lt, int_lt_spec, int_mod, int_mod_spec, int_mul, int_mul_spec, int_neg, int_neg_spec,
    int_pos_spec, int_pos_ty, int_pred, int_pred_spec, int_sgn, int_sgn_spec, int_sub,
    int_sub_spec, int_succ, int_succ_spec, int_zero,
};
pub use int_ops::{
    IntOp, int_from_int, int_from_nat, int_op, int_op_spec, int_sext, int_to_int, int_to_nat,
    int_zext, list_index_int, list_index_int_spec,
};
pub use list::{
    head, head_spec, list_cat, list_cat_spec, list_filter, list_filter_spec, list_flatten,
    list_flatten_spec, list_foldl, list_foldl_spec, list_index, list_index_spec, list_map,
    list_map_spec, list_repeat, list_repeat_spec, list_skip, list_skip_spec, list_take,
    list_take_spec, tail, tail_spec,
};
pub use nat::{
    nat_bit_and, nat_bit_and_spec, nat_bit_or, nat_bit_or_spec, nat_bit_xor, nat_bit_xor_spec,
    nat_div, nat_div_spec, nat_from_bytes_be, nat_from_bytes_be_spec, nat_from_bytes_le,
    nat_from_bytes_le_spec, nat_mod, nat_mod_spec, nat_mul, nat_mul_spec, nat_pow, nat_pow_spec,
    nat_shl, nat_shl_spec, nat_shr, nat_shr_spec, nat_sub, nat_sub_spec, nat_to_bytes_be,
    nat_to_bytes_be_spec, nat_to_bytes_le, nat_to_bytes_le_spec, nat_to_int, nat_to_int_spec,
};
pub use rat::{rat_le, rat_le_spec, rat_spec, rat_ty};
pub use rel::{
    part, part_spec, per, per_spec, pord, pord_spec, preord, preord_spec, rel, rel_compose,
    rel_compose_spec, rel_converse, rel_converse_spec, rel_deterministic, rel_deterministic_spec,
    rel_graph, rel_graph_spec, rel_holds, rel_holds_spec, rel_id, rel_id_spec, rel_is_function,
    rel_is_function_spec, rel_mk, rel_mk_spec, rel_spec, rel_to_fun, rel_to_fun_spec, rel_total,
    rel_total_spec,
};
pub use result::{err, err_spec, ok, ok_spec, result, result_spec};
pub use set::{
    list_elems, list_elems_spec, set, set_all, set_all_spec, set_any, set_any_spec, set_card,
    set_card_opt, set_card_opt_spec, set_card_spec, set_diff, set_diff_spec, set_empty,
    set_empty_spec, set_finite, set_finite_spec, set_flatten, set_flatten_spec, set_image,
    set_image_spec, set_insert, set_insert_spec, set_intersect, set_intersect_spec, set_is_empty,
    set_is_empty_spec, set_mem, set_mem_spec, set_min, set_min_spec, set_mk, set_mk_spec,
    set_preimage, set_preimage_spec, set_singleton, set_singleton_spec, set_spec, set_subset,
    set_subset_spec, set_union, set_union_spec,
};
pub use stream::{stream_iterate, stream_iterate_spec, stream_nth, stream_nth_spec};
pub use text::{
    CHAR_MAX_EXCL, SURROGATE_HI, SURROGATE_LO, char_code, char_code_spec, char_mk, char_mk_spec,
    char_spec, char_ty, string_spec, string_ty,
};

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_core::{Term, Type, TypeKind};

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
        assert_eq!(format!("{}", nat_add()), "nat.add");
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
        // Carrier is the *tagged* relation `α → β → bool → bool` (the
        // trailing `bool` is the inl/inr discriminator).
        let carrier = Type::fun(
            alpha,
            Type::fun(beta, Type::fun(Type::bool(), Type::bool())),
        );
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
    fn bits_is_list_bool() {
        // bits := list bool — a newtype over `list bool`.
        assert_eq!(bits_spec().ty().unwrap(), &list(Type::bool()));
    }

    #[test]
    fn signed_widths_are_newtypes_over_unsigned() {
        // sN := uN — a thin newtype; the carrier is the unsigned uN.
        assert_eq!(s1_spec().ty().unwrap(), &bit_ty());
        assert_eq!(s8_spec().ty().unwrap(), &u8_ty());
        assert_eq!(s32_spec().ty().unwrap(), &u32_ty());
        assert_eq!(s512_spec().ty().unwrap(), &u512_ty());
        // …and a distinct type from its unsigned carrier.
        assert_ne!(s8_ty(), u8_ty());
    }

    #[test]
    fn int_ops_have_expected_types() {
        use covalence_core::IntTag;
        // u8.add : u8 → u8 → u8
        assert_eq!(
            int_op_spec(IntTag::U8, IntOp::Add).ty().cloned(),
            Some(Type::fun(u8_ty(), Type::fun(u8_ty(), u8_ty()))),
        );
        // s32.lt : s32 → s32 → bool
        assert_eq!(
            int_op_spec(IntTag::S32, IntOp::Lt).ty().cloned(),
            Some(Type::fun(s32_ty(), Type::fun(s32_ty(), Type::bool()))),
        );
        // u8.toNat : u8 → nat ; s8.toInt : s8 → int
        assert_eq!(
            int_to_nat(IntTag::U8).type_of().unwrap(),
            Type::fun(u8_ty(), Type::nat()),
        );
        assert_eq!(
            int_to_int(IntTag::S8).type_of().unwrap(),
            Type::fun(s8_ty(), Type::int()),
        );
    }

    #[test]
    fn list_index_by_fixed_width_is_polymorphic() {
        use covalence_core::IntTag;
        // list.index.u8 : u8 → list 'a → option 'a — has a real body
        // and type-checks at a concrete element type.
        let idx = list_index_int(IntTag::U8, Type::nat());
        assert_eq!(
            idx.type_of().unwrap(),
            Type::fun(u8_ty(), Type::fun(list(Type::nat()), option(Type::nat()))),
        );
        assert!(list_index_int_spec(IntTag::U8).tm().is_some(), "has a body");
    }

    #[test]
    fn small_int_literals_have_fixed_width_types() {
        assert_eq!(Term::u8_lit(255).type_of().unwrap(), u8_ty());
        assert_eq!(Term::u16_lit(0).type_of().unwrap(), u16_ty());
        assert_eq!(Term::u32_lit(7).type_of().unwrap(), u32_ty());
        assert_eq!(Term::u64_lit(1).type_of().unwrap(), u64_ty());
        assert_eq!(Term::s8_lit(-1).type_of().unwrap(), s8_ty());
        assert_eq!(Term::s16_lit(-1).type_of().unwrap(), s16_ty());
        assert_eq!(Term::s32_lit(-1).type_of().unwrap(), s32_ty());
        assert_eq!(Term::s64_lit(-1).type_of().unwrap(), s64_ty());
    }

    #[test]
    fn fixed_widths_are_bits_subtypes() {
        // uN := { v : bits | length v = N } — every fixed width is a
        // subtype of `bits` (not a product chain), so the carrier is
        // `bits` for all of them.
        assert_eq!(bit_spec().ty().unwrap(), &bits_ty());
        assert_eq!(u2_spec().ty().unwrap(), &bits_ty());
        assert_eq!(u8_spec().ty().unwrap(), &bits_ty());
        assert_eq!(u64_spec().ty().unwrap(), &bits_ty());
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
        let expected = Type::fun(Type::nat(), Type::fun(list(Type::nat()), list(Type::nat())));
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
    fn rat_is_a_zero_ary_type() {
        let r = rat_ty();
        assert!(matches!(r.kind(), TypeKind::Spec(_, args) if args.is_empty()));
    }

    #[test]
    fn rat_le_has_expected_type() {
        // ratLe : rat → rat → bool
        let f = rat_le();
        let expected = Type::fun(rat_ty(), Type::fun(rat_ty(), Type::bool()));
        assert_eq!(f.type_of().unwrap(), expected);
    }

    #[test]
    fn close_spec_factory_well_typed() {
        // `close` over `int`/`intLe` — a stand-in for any cut-style subtype
        // (the reals themselves now live in `covalence-hol::init::real`).
        let car = Type::int();
        let pred = int_le();
        let handle = TypeSpec::close(Canonical::Rat, car, pred);
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
    fn stream_is_opaque_typespec() {
        // `stream α` is a TypeKind::Spec wrapper over the carrier
        // `nat → α`. Opaque to the type-checker — you can't apply
        // `s : stream α` directly. Use `stream_at` / `stream_mk`
        // to bridge between the spec leaf and the carrier function.
        let s = stream(Type::nat());
        match s.kind() {
            TypeKind::Spec(spec, args) => {
                assert_eq!(spec.symbol().label(), "stream");
                assert_eq!(args.len(), 1);
                assert_eq!(&args[0], &Type::nat());
            }
            _ => panic!("expected TypeKind::Spec, got {s:?}"),
        }
        // Carrier is `nat → α`.
        let spec = stream_spec();
        assert_eq!(
            spec.ty().cloned(),
            Some(Type::fun(Type::nat(), Type::tfree("a"))),
        );
    }

    #[test]
    fn stream_at_returns_carrier_application() {
        // stream_at : stream α → nat → α
        let alpha = Type::tfree("a");
        let f = stream_at(alpha.clone());
        assert_eq!(
            f.type_of().unwrap(),
            Type::fun(stream(alpha.clone()), Type::fun(Type::nat(), alpha),),
        );
    }

    #[test]
    fn stream_mk_returns_stream_from_function() {
        // stream_mk : (nat → α) → stream α
        let alpha = Type::tfree("a");
        let f = stream_mk(alpha.clone());
        assert_eq!(
            f.type_of().unwrap(),
            Type::fun(Type::fun(Type::nat(), alpha.clone()), stream(alpha),),
        );
    }

    #[test]
    fn finite_is_typed_at_stream_option_to_bool() {
        // finite α : stream (option α) → bool
        let alpha = Type::tfree("a");
        let f = finite(alpha.clone());
        assert_eq!(
            f.type_of().unwrap(),
            Type::fun(stream(option(alpha)), Type::bool()),
        );
    }

    #[test]
    fn option_is_opaque_typespec_over_coprod() {
        // `option α` is a TypeKind::Spec leaf (opaque), with
        // carrier `coprod α unit` and trivially-true predicate.
        let alpha = Type::tfree("a");
        let opt = option(alpha.clone());
        match opt.kind() {
            TypeKind::Spec(spec, args) => {
                assert_eq!(spec.symbol().label(), "option");
                assert_eq!(args.len(), 1);
                assert_eq!(&args[0], &alpha);
            }
            _ => panic!("expected TypeKind::Spec, got {opt:?}"),
        }
        let spec = option_spec();
        assert_eq!(spec.ty().cloned(), Some(coprod(alpha, Type::unit())));
    }

    #[test]
    fn cond_is_polymorphic_conditional() {
        // cond α : bool → α → α → α
        let alpha = Type::tfree("a");
        let c = cond(alpha.clone());
        assert_eq!(
            c.type_of().unwrap(),
            Type::fun(
                Type::bool(),
                Type::fun(alpha.clone(), Type::fun(alpha.clone(), alpha)),
            ),
        );
    }

    #[test]
    fn option_case_is_double_polymorphic_eliminator() {
        // optionCase α β : β → (α → β) → option α → β
        let alpha = Type::tfree("a");
        let beta = Type::tfree("b");
        let elim = option_case(alpha.clone(), beta.clone());
        assert_eq!(
            elim.type_of().unwrap(),
            Type::fun(
                beta.clone(),
                Type::fun(
                    Type::fun(alpha.clone(), beta.clone()),
                    Type::fun(option(alpha), beta),
                ),
            ),
        );
    }

    #[test]
    fn is_some_and_unwrap_typed_correctly() {
        let alpha = Type::tfree("a");
        let is_s = is_some(alpha.clone());
        let from_s = unwrap(alpha.clone());
        assert_eq!(
            is_s.type_of().unwrap(),
            Type::fun(option(alpha.clone()), Type::bool()),
        );
        assert_eq!(
            from_s.type_of().unwrap(),
            Type::fun(option(alpha.clone()), alpha),
        );
    }

    #[test]
    fn bytes_carrier_is_list_u8() {
        // `bytes := list u8`. We pull the carrier out of the spec
        // and assert it matches the canonical `list u8` build (using
        // the catalogue's list spec, not a raw stream-of-option).
        let spec = bytes_spec();
        assert_eq!(spec.ty().cloned(), Some(list(u8_ty())));
    }

    #[test]
    fn char_is_nat_subtype() {
        // char := { c : nat | c < 0x110000 } — a subtype of nat.
        assert_eq!(char_spec().ty().unwrap(), &Type::nat());
        // The selector predicate is `nat → bool`.
        let spec = char_spec();
        let tm = spec.tm().expect("char has a selector predicate");
        assert_eq!(tm.type_of().unwrap(), Type::fun(Type::nat(), Type::bool()),);
        // The type leaf is 0-ary.
        assert!(matches!(char_ty().kind(), TypeKind::Spec(_, args) if args.is_empty()));
    }

    #[test]
    fn char_code_and_mk_typed() {
        // char.code : char → nat ; char.mk : nat → char
        assert_eq!(
            char_code().type_of().unwrap(),
            Type::fun(char_ty(), Type::nat()),
        );
        assert_eq!(
            char_mk().type_of().unwrap(),
            Type::fun(Type::nat(), char_ty()),
        );
    }

    #[test]
    fn string_is_list_char_newtype() {
        // string := list char — a newtype over `list char`.
        assert_eq!(string_spec().ty().unwrap(), &list(char_ty()));
        assert!(matches!(string_ty().kind(), TypeKind::Spec(_, args) if args.is_empty()));
    }

    #[test]
    fn canonical_labels_match_doc_text() {
        assert_eq!(Canonical::Set.label(), "set");
        assert_eq!(Canonical::Coprod.label(), "coprod");
        assert_eq!(Canonical::Option.label(), "option");
        assert_eq!(Canonical::Rat.label(), "rat");
    }

    #[test]
    fn termspec_construction_round_trips() {
        let spec = TermSpec::new(Canonical::List, Some(Type::tfree("a")), None);
        assert_eq!(spec.symbol().label(), "list");
    }
}
