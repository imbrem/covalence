//! `option 'a := coprod 'a unit` + constructors + eliminator.
//!
//! `option α` is an opaque TypeSpec wrapper. Its carrier is the
//! spec'd `coprod α unit` (also opaque), and the selector
//! predicate is trivially true (so option α and coprod α unit are
//! extensionally the same — option just adds a distinct name and
//! identity). Values of `option α` can only be constructed by
//! the kernel-shipped constructors `some` / `none`, and inspected
//! via the eliminator `option_case` (or the convenience accessors
//! `is_some` / `from_some`).
//!
//! All of `some` / `none` / `option_case` / `is_some` / `from_some`
//! are declaration-only TermSpecs. Their semantics:
//!
//! ```text
//!     option_case default f none      = default
//!     option_case default f (some x)  = f x
//!     is_some none                    = F
//!     is_some (some x)                = T
//!     from_some (some x)              = x          (from_some none = ε, unspecified)
//! ```
//!
//! …are postulated downstream in `covalence-hol` (or proved from
//! Hilbert ε once a derivation lands). At the kernel level these
//! are opaque atoms; the type-level signatures are committed
//! at the model level.

use std::sync::LazyLock;

use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::coprod::coprod;
use super::spec::{TermSpec, TypeSpec};

/// `option 'a := coprod 'a unit`. Opaque TypeSpec wrapper. Its
/// carrier is `coprod α unit` and the predicate is trivially true,
/// so option α and coprod α unit have the same inhabitants — but
/// they are distinct types at the kernel-rule level (different
/// `Canonical` labels, different Arc identity, distinct Spec
/// leaves). Use the constructors `some` / `none` and the eliminator
/// `option_case` to interact with option values.
pub fn option_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let carrier = coprod(alpha, Type::unit());
        TypeSpec::newtype(Canonical::Option, carrier)
    });
    LAZY.clone()
}
pub fn option(alpha: Type) -> Type {
    Type::spec(option_spec(), vec![alpha])
}

// ============================================================================
// Constructors
// ============================================================================

/// `none : option 'a`. Declaration-only.
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

/// `some : 'a → option 'a`. Declaration-only.
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

// ============================================================================
// Eliminator + accessors
// ============================================================================

/// `optionCase : 'b → ('a → 'b) → option 'a → 'b`. The
/// fundamental eliminator. Declaration-only.
///
/// Spec is parametric in two type variables; the accessor takes
/// `α` then `β` (alphabetical order, matching the spec's
/// `free_tvars()` enumeration).
pub fn option_case_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let beta = Type::tfree("b");
        TermSpec::new(
            Canonical::OptionCase,
            Some(Type::fun(
                beta.clone(),
                Type::fun(
                    Type::fun(alpha.clone(), beta.clone()),
                    Type::fun(option(alpha), beta),
                ),
            )),
            None,
        )
    });
    LAZY.clone()
}
/// `optionCase α β : β → (α → β) → option α → β`.
pub fn option_case(alpha: Type, beta: Type) -> Term {
    Term::term_spec(option_case_spec(), vec![alpha, beta])
}

/// `isSome : option 'a → bool`. True iff the option is `some _`.
/// Declaration-only.
pub fn is_some_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        TermSpec::new(
            Canonical::IsSome,
            Some(Type::fun(option(alpha), Type::bool())),
            None,
        )
    });
    LAZY.clone()
}
pub fn is_some(alpha: Type) -> Term {
    Term::term_spec(is_some_spec(), vec![alpha])
}

/// `fromSome : option 'a → 'a`. Extract the wrapped value if
/// `some _`; for `none`, returns the canonical Hilbert-ε value
/// (unspecified at the kernel level). Declaration-only.
pub fn from_some_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        TermSpec::new(
            Canonical::FromSome,
            Some(Type::fun(option(alpha.clone()), alpha)),
            None,
        )
    });
    LAZY.clone()
}
pub fn from_some(alpha: Type) -> Term {
    Term::term_spec(from_some_spec(), vec![alpha])
}
