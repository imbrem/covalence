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
mod spec;
mod symbol;

pub use canonical::Canonical;
pub use spec::{TermSpec, TypeSpec};
pub use symbol::{Opacity, Symbol};

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Type;

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
