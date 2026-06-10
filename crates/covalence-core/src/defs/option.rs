//! `option 'a := coprod 'a unit` + `some` / `none` constructors.

use std::sync::LazyLock;

use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::coprod::coprod_predicate_at;
use super::spec::{TermSpec, TypeSpec};

/// `option 'a := coprod 'a unit`.
pub fn option_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let carrier = Type::fun(alpha.clone(), Type::fun(Type::unit(), Type::bool()));
        TypeSpec::new(
            Canonical::Option,
            Some(carrier),
            Some(coprod_predicate_at(alpha, Type::unit())),
        )
    });
    LAZY.clone()
}
pub fn option(alpha: Type) -> Type {
    Type::spec(option_spec(), vec![alpha])
}

/// `none : option 'a`.
pub fn none_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        TermSpec::new(Canonical::None, Some(option(alpha)), None)
    });
    LAZY.clone()
}
pub fn none(alpha: Type) -> Term {
    Term::term_spec(none_spec(), vec![alpha])
}

/// `some : 'a → option 'a`.
pub fn some_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        TermSpec::new(
            Canonical::Some,
            Some(Type::fun(alpha.clone(), option(alpha))),
            None,
        )
    });
    LAZY.clone()
}
pub fn some(alpha: Type) -> Term {
    Term::term_spec(some_spec(), vec![alpha])
}
