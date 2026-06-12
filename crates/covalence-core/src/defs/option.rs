//! `option 'a := coprod 'a unit` + `some` / `none` constructors.
//!
//! Option is a thin transparent alias for `coprod α unit` — its
//! carrier IS the spec'd coprod, and the selector predicate is
//! trivially true. So `option α` and `coprod α unit` are extensionally
//! the same type (same inhabitants); structurally they're distinct
//! TypeKind::Spec leaves because the Canonical label differs (one
//! prints as "option α", the other as "(coprod α unit)").

use std::sync::LazyLock;

use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::coprod::coprod;
use super::helpers::any;
use super::spec::{TermSpec, TypeSpec};

/// `option 'a := coprod 'a unit`. Implemented as a trivially-true
/// predicate over the spec'd carrier `coprod 'a unit` — the
/// selector accepts every value in coprod, so `option α` has
/// exactly the same inhabitants as `coprod α unit`.
pub fn option_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let carrier = coprod(alpha, Type::unit());
        TypeSpec::new(
            Canonical::Option,
            Some(carrier.clone()),
            Some(any(&carrier)),
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
