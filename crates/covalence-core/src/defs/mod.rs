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
//! `natAdd : nat → nat → nat` will be a `TermSpec` that the
//! reduction mechanism recognises by pointer identity — so an
//! incorrect definition here would let the kernel reduce a closed
//! arithmetic expression to the wrong value. We treat it as
//! audit-required even though it's "below" `thm`.
//!
//! ## Current scope (in-flight)
//!
//! This first cut just lays the scaffolding:
//!
//! - [`Symbol`] / [`Opacity`] — symbol trait + opacity tagging.
//! - [`Canonical`] — the non-exhaustive symbol enum for kernel
//!   derived types.
//! - [`TypeSpec`] / [`TermSpec`] — the data structures themselves.
//!
//! Wiring the catalogue into `TypeKind` / `TermKind`, populating
//! the lazy statics for each `Canonical` variant, and teaching
//! `Thm::reduce_prim` to dispatch on `TermSpec` pointer identity
//! all land in follow-up commits.

mod canonical;
mod catalogue;
mod spec;
mod symbol;

pub use canonical::Canonical;
pub use catalogue::{
    coprod, coprod_spec, int_add, int_add_spec, int_le, int_le_spec, int_lt, int_lt_spec, int_mul,
    int_mul_spec, int_sub, int_sub_spec, nat_add, nat_add_spec, nat_le, nat_le_spec, nat_lt,
    nat_lt_spec, nat_mul, nat_mul_spec, nat_sub, nat_sub_spec, option, option_spec, prod, prod_spec,
    rel, rel_spec, set, set_spec, stream, stream_spec,
};
pub use spec::{TermSpec, TermSpecHandle, TypeSpec, TypeSpecHandle};
pub use symbol::{Opacity, Symbol};

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Type, TypeKind};

    #[test]
    fn set_alpha_round_trip() {
        let s_nat = set(Type::nat());
        // Carrier should be `'a -> bool` after substitution.
        match s_nat.kind() {
            TypeKind::Spec(spec, args) => {
                assert_eq!(spec.symbol(), Canonical::Set);
                assert_eq!(args.len(), 1);
                assert_eq!(&args[0], &Type::nat());
            }
            _ => panic!("expected TypeKind::Spec, got {s_nat:?}"),
        }
    }

    #[test]
    fn set_lazy_static_is_shared() {
        // Two `set_spec()` calls give pointer-equal handles.
        assert!(set_spec().ptr_eq(&set_spec()));
    }

    #[test]
    fn rel_two_args() {
        let r = rel(Type::nat(), Type::int());
        match r.kind() {
            TypeKind::Spec(spec, args) => {
                assert_eq!(spec.symbol(), Canonical::Rel);
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
        // Repeated calls return pointer-equal handles via LazyLock.
        assert!(nat_add_spec().ptr_eq(&nat_add_spec()));
    }

    #[test]
    fn nat_add_term_display() {
        // Zero-arg spec displays as just the label.
        assert_eq!(format!("{}", nat_add()), "natAdd");
    }

    #[test]
    fn coprod_type_builds() {
        let c = coprod(Type::nat(), Type::int());
        match c.kind() {
            TypeKind::Spec(spec, args) => {
                assert_eq!(spec.symbol(), Canonical::Coprod);
                assert_eq!(args.len(), 2);
                assert_eq!(&args[0], &Type::nat());
                assert_eq!(&args[1], &Type::int());
            }
            _ => panic!("expected TypeKind::Spec, got {c:?}"),
        }
    }

    #[test]
    fn coprod_predicate_well_typed() {
        // The cached coprod predicate term should be a closed
        // function `(rel α β) → bool` over the spec's type variables.
        let spec = coprod_spec();
        let tm = spec.as_spec().tm.as_ref().expect("coprod has predicate");
        let ty = tm
            .type_of()
            .unwrap_or_else(|e| panic!("coprod predicate type-of: {e:?}"));
        // Carrier: α → β → bool; predicate type: (carrier) → bool.
        let alpha = Type::tfree("a");
        let beta = Type::tfree("b");
        let carrier = Type::fun(alpha, Type::fun(beta, Type::bool()));
        let expected = Type::fun(carrier, Type::bool());
        assert_eq!(ty, expected);
    }

    #[test]
    fn prod_predicate_well_typed() {
        let spec = prod_spec();
        let tm = spec.as_spec().tm.as_ref().expect("prod has predicate");
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
                assert_eq!(spec.symbol(), Canonical::Option);
                assert_eq!(args.len(), 1);
                assert_eq!(&args[0], &Type::nat());
            }
            _ => panic!("expected TypeKind::Spec, got {o:?}"),
        }
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
                assert_eq!(spec.symbol(), Canonical::Stream);
                assert_eq!(args.len(), 1);
                assert_eq!(&args[0], &Type::nat());
            }
            _ => panic!("expected TypeKind::Spec, got {s:?}"),
        }
    }

    #[test]
    fn canonical_labels_match_doc_text() {
        // Spot-check a few — the full set is exercised by Display.
        assert_eq!(Canonical::Set.label(), "set");
        assert_eq!(Canonical::Coprod.label(), "coprod");
        assert_eq!(Canonical::Option.label(), "option");
        assert_eq!(Canonical::FieldOfFractions.label(), "fieldOfFractions");
        assert_eq!(Canonical::Real.label(), "real");
    }

    #[test]
    fn canonical_is_transparent() {
        assert_eq!(<Canonical as Symbol>::OPACITY, Opacity::Transparent);
    }

    #[test]
    fn smolstr_is_opaque() {
        assert_eq!(<smol_str::SmolStr as Symbol>::OPACITY, Opacity::Opaque);
    }

    #[test]
    fn typespec_construction_round_trips() {
        let spec = TypeSpec {
            symbol: Canonical::Set,
            ty: Some(Type::fun(Type::tfree("a"), Type::bool())),
            tm: None,
        };
        assert_eq!(spec.symbol, Canonical::Set);
        assert!(spec.ty.is_some());
        assert!(spec.tm.is_none());
    }

    #[test]
    fn termspec_construction_round_trips() {
        let spec = TermSpec {
            symbol: Canonical::List,
            ty: Some(Type::tfree("a")),
            tm: None,
        };
        assert_eq!(spec.symbol, Canonical::List);
    }
}
