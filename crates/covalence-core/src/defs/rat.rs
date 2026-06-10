//! `rat` and `fieldOfFractions` — currently placeholders.
//!
//! Intended definitions:
//!
//! ```text
//! def fieldOfFractions[mul, zero] 'a := prod 'a 'a quot (standard equiv)
//! def rat := fieldOfFractions int
//! ```
//!
//! The cross-multiplication equivalence (p, q) ∼ (p', q') iff
//! p*q' = p'*q needs `intMul` as a usable term-spec to build; for
//! now both ship with the `any` predicate so the catalogue is
//! name-complete. `real` lives in [`super::real`].

use std::sync::LazyLock;

use crate::term::Type;

use super::canonical::Canonical;
use super::spec::{TypeSpec, TypeSpecHandle};
use super::helpers::any;
use super::prod::prod;

static RAT_LAZY: LazyLock<TypeSpecHandle> = LazyLock::new(|| {
    // TODO: quot_spec over prod int int with cross-mult equivalence.
    let carrier = Type::int();
    let carrier_for_pred = carrier.clone();
    TypeSpecHandle::new(TypeSpec {
        symbol: Canonical::Rat,
        ty: Some(carrier),
        tm: Some(any(&carrier_for_pred)),
    })
});

/// `rat` — placeholder; will become `fieldOfFractions int`.
pub fn rat_spec() -> TypeSpecHandle {
    RAT_LAZY.clone()
}
pub fn rat_ty() -> Type {
    Type::spec(rat_spec(), vec![])
}

static FIELD_OF_FRACTIONS_LAZY: LazyLock<TypeSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    let carrier = prod(alpha.clone(), alpha);
    let carrier_for_pred = carrier.clone();
    TypeSpecHandle::new(TypeSpec {
        symbol: Canonical::FieldOfFractions,
        ty: Some(carrier),
        tm: Some(any(&carrier_for_pred)),
    })
});

/// `fieldOfFractions 'a` — placeholder; will become a `quot_spec` over
/// `prod 'a 'a` with the cross-multiplication equivalence.
pub fn field_of_fractions_spec() -> TypeSpecHandle {
    FIELD_OF_FRACTIONS_LAZY.clone()
}
pub fn field_of_fractions(alpha: Type) -> Type {
    Type::spec(field_of_fractions_spec(), vec![alpha])
}
