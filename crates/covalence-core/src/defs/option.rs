//! `option 'a := coprod 'a unit` + `some` / `none` constructors.

use std::sync::LazyLock;

use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::spec::{TermSpec, TermSpecHandle, TypeSpec, TypeSpecHandle};
use super::coprod::coprod_predicate_at;

static OPTION_LAZY: LazyLock<TypeSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    let carrier = Type::fun(alpha.clone(), Type::fun(Type::unit(), Type::bool()));
    TypeSpecHandle::new(TypeSpec {
        symbol: Canonical::Option,
        ty: Some(carrier),
        // TODO: properly instantiate β := unit at static init.
        tm: Some(coprod_predicate_at(alpha, Type::unit())),
    })
});

/// `option 'a := coprod 'a unit`.
pub fn option_spec() -> TypeSpecHandle {
    OPTION_LAZY.clone()
}
pub fn option(alpha: Type) -> Type {
    Type::spec(option_spec(), vec![alpha])
}

// ---- Constructors ----

static NONE_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    TermSpecHandle::new(TermSpec {
        symbol: Canonical::None,
        ty: Some(option(alpha)),
        tm: None,
    })
});

static SOME_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    TermSpecHandle::new(TermSpec {
        symbol: Canonical::Some,
        ty: Some(Type::fun(alpha.clone(), option(alpha))),
        tm: None,
    })
});

/// `none : option 'a`.
pub fn none_spec() -> TermSpecHandle {
    NONE_LAZY.clone()
}
pub fn none(alpha: Type) -> Term {
    Term::term_spec(none_spec(), vec![alpha])
}
/// `some : 'a → option 'a`.
pub fn some_spec() -> TermSpecHandle {
    SOME_LAZY.clone()
}
pub fn some(alpha: Type) -> Term {
    Term::term_spec(some_spec(), vec![alpha])
}
