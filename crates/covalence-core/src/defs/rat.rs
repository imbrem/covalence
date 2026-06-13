//! `rat`, `fieldOfFractions`, and the `ratLe` order constant.
//!
//! `rat` is a placeholder — once `fieldOfFractions int` is fleshed
//! out (with a real quotient by the proportionality relation),
//! `rat` will become `fieldOfFractions int`. For now it's an
//! opaque TypeSpec over `int` with the trivially-true selector.
//!
//! `ratLe : rat → rat → bool` is the order on rationals. It's
//! declaration-only at the kernel level; the standard order axioms
//! (reflexivity, transitivity, antisymmetry, totality, plus
//! compatibility with `+` / `*`) live downstream in
//! `covalence-hol`, where they're postulated as theorems and later
//! discharged once `rat` has its real construction.
//!
//! `ratLe` exists in `defs/` because it's needed *here* to define
//! `real := { rat } close ratLe` (Dedekind cuts).

use std::sync::LazyLock;

use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::helpers::any;
use super::prod::prod;
use super::spec::{TermSpec, TypeSpec};

/// `rat` — placeholder; will become `fieldOfFractions int`.
pub fn rat_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> = LazyLock::new(|| {
        let carrier = Type::int();
        TypeSpec::new(Canonical::Rat, Some(carrier.clone()), Some(any(&carrier)))
    });
    LAZY.clone()
}
pub fn rat_ty() -> Type {
    static LAZY: LazyLock<Type> = LazyLock::new(|| Type::spec(rat_spec(), vec![]));
    LAZY.clone()
}

/// `fieldOfFractions 'a` — placeholder.
pub fn field_of_fractions_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let carrier = prod(alpha.clone(), alpha);
        TypeSpec::new(
            Canonical::FieldOfFractions,
            Some(carrier.clone()),
            Some(any(&carrier)),
        )
    });
    LAZY.clone()
}
pub fn field_of_fractions(alpha: Type) -> Type {
    Type::spec(field_of_fractions_spec(), vec![alpha])
}

/// `ratLe : rat → rat → bool` — the order on `rat`. Declaration-only.
/// Used as the cutting relation in `real := { rat } close ratLe`.
pub fn rat_le_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let ty = Type::fun(rat_ty(), Type::fun(rat_ty(), Type::bool()));
        TermSpec::new(Canonical::RatLe, Some(ty), None)
    });
    LAZY.clone()
}
/// `ratLe : rat → rat → bool`.
pub fn rat_le() -> Term {
    Term::term_spec(rat_le_spec(), vec![])
}
