//! `real` — placeholder for Dedekind cuts of rationals.
//!
//! The intended definition (per `docs/type-hierarchy.md`) is
//!
//! ```text
//! def real := { rat } close ratLe
//! ```
//!
//! That is: a `real` is a `rat → bool` (a set of rationals) that's
//! downward-closed under the rational order and non-empty. Both
//! `rat` and `ratLe` need to land as usable catalogue entries first;
//! for now we ship `real` with the `any` predicate so the catalogue
//! is name-complete (and float specs can refer to it) while we work
//! on the proper definition.

use std::sync::LazyLock;

use crate::term::Type;

use super::canonical::Canonical;
use super::spec::{TypeSpec, TypeSpecHandle};
use super::helpers::any;
use super::rat::rat_ty;

static REAL_LAZY: LazyLock<TypeSpecHandle> = LazyLock::new(|| {
    let rat = rat_ty();
    let carrier = Type::fun(rat, Type::bool());
    let carrier_for_pred = carrier.clone();
    TypeSpecHandle::new(TypeSpec {
        symbol: Canonical::Real,
        ty: Some(carrier),
        // TODO: replace with close_predicate(rat_ty(), ratLe()) once
        // ratLe is a usable term-spec.
        tm: Some(any(&carrier_for_pred)),
    })
});

/// `real` — placeholder; will become `{ rat } close ratLe`.
pub fn real_spec() -> TypeSpecHandle {
    REAL_LAZY.clone()
}
/// `real` as a 0-ary Type.
pub fn real_ty() -> Type {
    Type::spec(real_spec(), vec![])
}
