//! `rat` and `fieldOfFractions` — currently placeholders.

use std::sync::LazyLock;

use crate::term::Type;

use super::canonical::Canonical;
use super::helpers::any;
use super::prod::prod;
use super::spec::TypeSpec;

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
