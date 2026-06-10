//! `list 'a` type + constructors + list operations.

use std::sync::LazyLock;

use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::spec::{TermSpec, TermSpecHandle, TypeSpec, TypeSpecHandle};
use super::helpers::any;
use super::option::option;

// ============================================================================
// list 'a := stream (option 'a) where (eventually-none)
//
// TODO: the predicate is currently `any`; the proper
// eventually-none selector requires `natLt`/`some`/`none` as
// usable term builders (this is a known overreach).
// ============================================================================

static LIST_LAZY: LazyLock<TypeSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    let carrier = Type::fun(Type::nat(), option(alpha));
    let carrier_for_pred = carrier.clone();
    TypeSpecHandle::new(TypeSpec {
        symbol: Canonical::List,
        ty: Some(carrier),
        tm: Some(any(&carrier_for_pred)),
    })
});

/// `list 'a := stream (option 'a) where (eventually-none)`.
pub fn list_spec() -> TypeSpecHandle {
    LIST_LAZY.clone()
}
pub fn list(alpha: Type) -> Type {
    Type::spec(list_spec(), vec![alpha])
}

// ============================================================================
// Constructors / destructors
// ============================================================================

static NIL_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    TermSpecHandle::new(TermSpec {
        symbol: Canonical::Nil,
        ty: Some(list(alpha)),
        tm: None,
    })
});

static CONS_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    let list_a = list(alpha.clone());
    TermSpecHandle::new(TermSpec {
        symbol: Canonical::Cons,
        ty: Some(Type::fun(alpha, Type::fun(list_a.clone(), list_a))),
        tm: None,
    })
});

static HEAD_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    let list_a = list(alpha.clone());
    TermSpecHandle::new(TermSpec {
        symbol: Canonical::Head,
        ty: Some(Type::fun(list_a, option(alpha))),
        tm: None,
    })
});

static TAIL_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    let list_a = list(alpha);
    TermSpecHandle::new(TermSpec {
        symbol: Canonical::Tail,
        ty: Some(Type::fun(list_a.clone(), list_a)),
        tm: None,
    })
});

/// `nil : list 'a`.
pub fn nil_spec() -> TermSpecHandle {
    NIL_LAZY.clone()
}
pub fn nil(alpha: Type) -> Term {
    Term::term_spec(nil_spec(), vec![alpha])
}
/// `cons : 'a → list 'a → list 'a`.
pub fn cons_spec() -> TermSpecHandle {
    CONS_LAZY.clone()
}
pub fn cons(alpha: Type) -> Term {
    Term::term_spec(cons_spec(), vec![alpha])
}
/// `head : list 'a → option 'a`.
pub fn head_spec() -> TermSpecHandle {
    HEAD_LAZY.clone()
}
pub fn head(alpha: Type) -> Term {
    Term::term_spec(head_spec(), vec![alpha])
}
/// `tail : list 'a → list 'a`.
pub fn tail_spec() -> TermSpecHandle {
    TAIL_LAZY.clone()
}
pub fn tail(alpha: Type) -> Term {
    Term::term_spec(tail_spec(), vec![alpha])
}

// ============================================================================
// List operations
// ============================================================================

fn poly_list_op(symbol: Canonical, ty: Type) -> TermSpecHandle {
    TermSpecHandle::new(TermSpec {
        symbol,
        ty: Some(ty),
        tm: None,
    })
}

static LIST_LENGTH_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    poly_list_op(Canonical::ListLength, Type::fun(list(alpha), Type::nat()))
});
static LIST_CAT_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    let la = list(alpha);
    poly_list_op(
        Canonical::ListCat,
        Type::fun(la.clone(), Type::fun(la.clone(), la)),
    )
});
static LIST_MAP_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    let beta = Type::tfree("b");
    let f_ty = Type::fun(alpha.clone(), beta.clone());
    poly_list_op(
        Canonical::ListMap,
        Type::fun(f_ty, Type::fun(list(alpha), list(beta))),
    )
});
static LIST_FILTER_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    let p_ty = Type::fun(alpha.clone(), Type::bool());
    let la = list(alpha);
    poly_list_op(
        Canonical::ListFilter,
        Type::fun(p_ty, Type::fun(la.clone(), la)),
    )
});
static LIST_FOLDR_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    let beta = Type::tfree("b");
    let f_ty = Type::fun(alpha.clone(), Type::fun(beta.clone(), beta.clone()));
    poly_list_op(
        Canonical::ListFoldr,
        Type::fun(f_ty, Type::fun(beta.clone(), Type::fun(list(alpha), beta))),
    )
});
static LIST_FOLDL_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    let beta = Type::tfree("b");
    let f_ty = Type::fun(beta.clone(), Type::fun(alpha.clone(), beta.clone()));
    poly_list_op(
        Canonical::ListFoldl,
        Type::fun(f_ty, Type::fun(beta.clone(), Type::fun(list(alpha), beta))),
    )
});
static LIST_TAKE_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    let la = list(alpha);
    poly_list_op(
        Canonical::ListTake,
        Type::fun(Type::nat(), Type::fun(la.clone(), la)),
    )
});
static LIST_SKIP_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    let la = list(alpha);
    poly_list_op(
        Canonical::ListSkip,
        Type::fun(Type::nat(), Type::fun(la.clone(), la)),
    )
});
static LIST_INDEX_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    poly_list_op(
        Canonical::ListIndex,
        Type::fun(Type::nat(), Type::fun(list(alpha.clone()), option(alpha))),
    )
});
static LIST_REPEAT_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    poly_list_op(
        Canonical::ListRepeat,
        Type::fun(Type::nat(), Type::fun(alpha.clone(), list(alpha))),
    )
});
static LIST_FLATTEN_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    poly_list_op(
        Canonical::ListFlatten,
        Type::fun(list(list(alpha.clone())), list(alpha)),
    )
});

/// `listLength : list 'a → nat`.
pub fn list_length_spec() -> TermSpecHandle {
    LIST_LENGTH_LAZY.clone()
}
pub fn list_length(alpha: Type) -> Term {
    Term::term_spec(list_length_spec(), vec![alpha])
}
/// `listCat : list 'a → list 'a → list 'a`.
pub fn list_cat_spec() -> TermSpecHandle {
    LIST_CAT_LAZY.clone()
}
pub fn list_cat(alpha: Type) -> Term {
    Term::term_spec(list_cat_spec(), vec![alpha])
}
/// `listMap : ('a → 'b) → list 'a → list 'b`.
pub fn list_map_spec() -> TermSpecHandle {
    LIST_MAP_LAZY.clone()
}
pub fn list_map(alpha: Type, beta: Type) -> Term {
    Term::term_spec(list_map_spec(), vec![alpha, beta])
}
/// `listFilter : ('a → bool) → list 'a → list 'a`.
pub fn list_filter_spec() -> TermSpecHandle {
    LIST_FILTER_LAZY.clone()
}
pub fn list_filter(alpha: Type) -> Term {
    Term::term_spec(list_filter_spec(), vec![alpha])
}
/// `listFoldr : ('a → 'b → 'b) → 'b → list 'a → 'b`.
pub fn list_foldr_spec() -> TermSpecHandle {
    LIST_FOLDR_LAZY.clone()
}
pub fn list_foldr(alpha: Type, beta: Type) -> Term {
    Term::term_spec(list_foldr_spec(), vec![alpha, beta])
}
/// `listFoldl : ('b → 'a → 'b) → 'b → list 'a → 'b`.
pub fn list_foldl_spec() -> TermSpecHandle {
    LIST_FOLDL_LAZY.clone()
}
pub fn list_foldl(alpha: Type, beta: Type) -> Term {
    Term::term_spec(list_foldl_spec(), vec![alpha, beta])
}
/// `listTake : nat → list 'a → list 'a`.
pub fn list_take_spec() -> TermSpecHandle {
    LIST_TAKE_LAZY.clone()
}
pub fn list_take(alpha: Type) -> Term {
    Term::term_spec(list_take_spec(), vec![alpha])
}
/// `listSkip : nat → list 'a → list 'a`.
pub fn list_skip_spec() -> TermSpecHandle {
    LIST_SKIP_LAZY.clone()
}
pub fn list_skip(alpha: Type) -> Term {
    Term::term_spec(list_skip_spec(), vec![alpha])
}
/// `listIndex : nat → list 'a → option 'a`.
pub fn list_index_spec() -> TermSpecHandle {
    LIST_INDEX_LAZY.clone()
}
pub fn list_index(alpha: Type) -> Term {
    Term::term_spec(list_index_spec(), vec![alpha])
}
/// `listRepeat : nat → 'a → list 'a`.
pub fn list_repeat_spec() -> TermSpecHandle {
    LIST_REPEAT_LAZY.clone()
}
pub fn list_repeat(alpha: Type) -> Term {
    Term::term_spec(list_repeat_spec(), vec![alpha])
}
/// `listFlatten : list (list 'a) → list 'a`. Combined with
/// `list_repeat`, repeats a *list* n times.
pub fn list_flatten_spec() -> TermSpecHandle {
    LIST_FLATTEN_LAZY.clone()
}
pub fn list_flatten(alpha: Type) -> Term {
    Term::term_spec(list_flatten_spec(), vec![alpha])
}
