//! `set 'a := 'a → bool` + set operations.

use std::sync::LazyLock;

use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::list::list;
use super::spec::{TermSpec, TypeSpec};

/// `set 'a := 'a → bool` — predicate-style sets.
pub fn set_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let carrier = Type::fun(alpha, Type::bool());
        TypeSpec::newtype(Canonical::Set, carrier)
    });
    LAZY.clone()
}
pub fn set(alpha: Type) -> Type {
    Type::spec(set_spec(), vec![alpha])
}

/// `setUnion : set 'a → set 'a → set 'a`.
pub fn set_union_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let sa = set(alpha);
        TermSpec::new(
            Canonical::SetUnion,
            Some(Type::fun(sa.clone(), Type::fun(sa.clone(), sa))),
            None,
        )
    });
    LAZY.clone()
}
pub fn set_union(alpha: Type) -> Term {
    Term::term_spec(set_union_spec(), vec![alpha])
}

/// `setIntersect : set 'a → set 'a → set 'a`.
pub fn set_intersect_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let sa = set(alpha);
        TermSpec::new(
            Canonical::SetIntersect,
            Some(Type::fun(sa.clone(), Type::fun(sa.clone(), sa))),
            None,
        )
    });
    LAZY.clone()
}
pub fn set_intersect(alpha: Type) -> Term {
    Term::term_spec(set_intersect_spec(), vec![alpha])
}

/// `setDiff : set 'a → set 'a → set 'a`.
pub fn set_diff_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let sa = set(alpha);
        TermSpec::new(
            Canonical::SetDiff,
            Some(Type::fun(sa.clone(), Type::fun(sa.clone(), sa))),
            None,
        )
    });
    LAZY.clone()
}
pub fn set_diff(alpha: Type) -> Term {
    Term::term_spec(set_diff_spec(), vec![alpha])
}

/// `setSubset : set 'a → set 'a → bool`.
pub fn set_subset_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let sa = set(alpha);
        TermSpec::new(
            Canonical::SetSubset,
            Some(Type::fun(sa.clone(), Type::fun(sa, Type::bool()))),
            None,
        )
    });
    LAZY.clone()
}
pub fn set_subset(alpha: Type) -> Term {
    Term::term_spec(set_subset_spec(), vec![alpha])
}

/// `setCard : set 'a → nat`.
pub fn set_card_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let sa = set(alpha);
        TermSpec::new(Canonical::SetCard, Some(Type::fun(sa, Type::nat())), None)
    });
    LAZY.clone()
}
pub fn set_card(alpha: Type) -> Term {
    Term::term_spec(set_card_spec(), vec![alpha])
}

/// `listToSet : list 'a → set 'a`.
pub fn list_to_set_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        TermSpec::new(
            Canonical::ListToSet,
            Some(Type::fun(list(alpha.clone()), set(alpha))),
            None,
        )
    });
    LAZY.clone()
}
pub fn list_to_set(alpha: Type) -> Term {
    Term::term_spec(list_to_set_spec(), vec![alpha])
}
