//! `set 'a := 'a → bool` + set operations.

use std::sync::LazyLock;

use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::spec::{TermSpec, TermSpecHandle, TypeSpec, TypeSpecHandle};
use super::helpers::any;
use super::list::list;

static SET_LAZY: LazyLock<TypeSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    let carrier = Type::fun(alpha, Type::bool());
    TypeSpecHandle::new(TypeSpec {
        symbol: Canonical::Set,
        ty: Some(carrier.clone()),
        tm: Some(any(&carrier)),
    })
});

/// `set 'a := 'a → bool` — predicate-style sets.
pub fn set_spec() -> TypeSpecHandle {
    SET_LAZY.clone()
}
/// `set α` at carrier α.
pub fn set(alpha: Type) -> Type {
    Type::spec(set_spec(), vec![alpha])
}

// ---- Set operations ----

fn poly_set_op(symbol: Canonical, ty: Type) -> TermSpecHandle {
    TermSpecHandle::new(TermSpec {
        symbol,
        ty: Some(ty),
        tm: None,
    })
}

static SET_UNION_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    let sa = set(alpha);
    poly_set_op(
        Canonical::SetUnion,
        Type::fun(sa.clone(), Type::fun(sa.clone(), sa)),
    )
});
static SET_INTERSECT_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    let sa = set(alpha);
    poly_set_op(
        Canonical::SetIntersect,
        Type::fun(sa.clone(), Type::fun(sa.clone(), sa)),
    )
});
static SET_DIFF_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    let sa = set(alpha);
    poly_set_op(
        Canonical::SetDiff,
        Type::fun(sa.clone(), Type::fun(sa.clone(), sa)),
    )
});
static SET_SUBSET_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    let sa = set(alpha);
    poly_set_op(
        Canonical::SetSubset,
        Type::fun(sa.clone(), Type::fun(sa, Type::bool())),
    )
});
static SET_CARD_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    let sa = set(alpha);
    poly_set_op(Canonical::SetCard, Type::fun(sa, Type::nat()))
});
static LIST_TO_SET_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    poly_set_op(
        Canonical::ListToSet,
        Type::fun(list(alpha.clone()), set(alpha)),
    )
});

/// `setUnion : set 'a → set 'a → set 'a`.
pub fn set_union_spec() -> TermSpecHandle {
    SET_UNION_LAZY.clone()
}
pub fn set_union(alpha: Type) -> Term {
    Term::term_spec(set_union_spec(), vec![alpha])
}
/// `setIntersect : set 'a → set 'a → set 'a`.
pub fn set_intersect_spec() -> TermSpecHandle {
    SET_INTERSECT_LAZY.clone()
}
pub fn set_intersect(alpha: Type) -> Term {
    Term::term_spec(set_intersect_spec(), vec![alpha])
}
/// `setDiff : set 'a → set 'a → set 'a`.
pub fn set_diff_spec() -> TermSpecHandle {
    SET_DIFF_LAZY.clone()
}
pub fn set_diff(alpha: Type) -> Term {
    Term::term_spec(set_diff_spec(), vec![alpha])
}
/// `setSubset : set 'a → set 'a → bool`.
pub fn set_subset_spec() -> TermSpecHandle {
    SET_SUBSET_LAZY.clone()
}
pub fn set_subset(alpha: Type) -> Term {
    Term::term_spec(set_subset_spec(), vec![alpha])
}
/// `setCard : set 'a → nat`.
pub fn set_card_spec() -> TermSpecHandle {
    SET_CARD_LAZY.clone()
}
pub fn set_card(alpha: Type) -> Term {
    Term::term_spec(set_card_spec(), vec![alpha])
}
/// `listToSet : list 'a → set 'a`.
pub fn list_to_set_spec() -> TermSpecHandle {
    LIST_TO_SET_LAZY.clone()
}
pub fn list_to_set(alpha: Type) -> Term {
    Term::term_spec(list_to_set_spec(), vec![alpha])
}
