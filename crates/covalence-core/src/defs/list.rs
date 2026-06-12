//! `list 'a` type + constructors + list operations.

use std::sync::LazyLock;

use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::helpers::any;
use super::option::option;
use super::spec::{TermSpec, TypeSpec};

/// `list 'a := stream (option 'a) where (eventually-none)`.
pub fn list_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let carrier = Type::fun(Type::nat(), option(alpha));
        TypeSpec::new(Canonical::List, Some(carrier.clone()), Some(any(&carrier)))
    });
    LAZY.clone()
}
pub fn list(alpha: Type) -> Type {
    Type::spec(list_spec(), vec![alpha])
}

/// `nil : list 'a`.
pub fn nil_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        TermSpec::new(Canonical::Nil, Some(list(alpha)), None)
    });
    LAZY.clone()
}
pub fn nil(alpha: Type) -> Term {
    Term::term_spec(nil_spec(), vec![alpha])
}

/// `cons : 'a → list 'a → list 'a`.
pub fn cons_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let list_a = list(alpha.clone());
        TermSpec::new(
            Canonical::Cons,
            Some(Type::fun(alpha, Type::fun(list_a.clone(), list_a))),
            None,
        )
    });
    LAZY.clone()
}
pub fn cons(alpha: Type) -> Term {
    Term::term_spec(cons_spec(), vec![alpha])
}

/// `head : list 'a → option 'a`.
pub fn head_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let list_a = list(alpha.clone());
        TermSpec::new(
            Canonical::Head,
            Some(Type::fun(list_a, option(alpha))),
            None,
        )
    });
    LAZY.clone()
}
pub fn head(alpha: Type) -> Term {
    Term::term_spec(head_spec(), vec![alpha])
}

/// `tail : list 'a → list 'a`.
pub fn tail_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let list_a = list(alpha);
        TermSpec::new(
            Canonical::Tail,
            Some(Type::fun(list_a.clone(), list_a)),
            None,
        )
    });
    LAZY.clone()
}
pub fn tail(alpha: Type) -> Term {
    Term::term_spec(tail_spec(), vec![alpha])
}

/// `listLength : list 'a → nat`.
pub fn list_length_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        TermSpec::new(
            Canonical::ListLength,
            Some(Type::fun(list(alpha), Type::nat())),
            None,
        )
    });
    LAZY.clone()
}
pub fn list_length(alpha: Type) -> Term {
    Term::term_spec(list_length_spec(), vec![alpha])
}

/// `listCat : list 'a → list 'a → list 'a`.
pub fn list_cat_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let la = list(alpha);
        TermSpec::new(
            Canonical::ListCat,
            Some(Type::fun(la.clone(), Type::fun(la.clone(), la))),
            None,
        )
    });
    LAZY.clone()
}
pub fn list_cat(alpha: Type) -> Term {
    Term::term_spec(list_cat_spec(), vec![alpha])
}

/// `listMap : ('a → 'b) → list 'a → list 'b`.
pub fn list_map_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let beta = Type::tfree("b");
        let f_ty = Type::fun(alpha.clone(), beta.clone());
        TermSpec::new(
            Canonical::ListMap,
            Some(Type::fun(f_ty, Type::fun(list(alpha), list(beta)))),
            None,
        )
    });
    LAZY.clone()
}
pub fn list_map(alpha: Type, beta: Type) -> Term {
    Term::term_spec(list_map_spec(), vec![alpha, beta])
}

/// `listFilter : ('a → bool) → list 'a → list 'a`.
pub fn list_filter_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let p_ty = Type::fun(alpha.clone(), Type::bool());
        let la = list(alpha);
        TermSpec::new(
            Canonical::ListFilter,
            Some(Type::fun(p_ty, Type::fun(la.clone(), la))),
            None,
        )
    });
    LAZY.clone()
}
pub fn list_filter(alpha: Type) -> Term {
    Term::term_spec(list_filter_spec(), vec![alpha])
}

/// `listFoldr : ('a → 'b → 'b) → 'b → list 'a → 'b`.
pub fn list_foldr_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let beta = Type::tfree("b");
        let f_ty = Type::fun(alpha.clone(), Type::fun(beta.clone(), beta.clone()));
        TermSpec::new(
            Canonical::ListFoldr,
            Some(Type::fun(
                f_ty,
                Type::fun(beta.clone(), Type::fun(list(alpha), beta)),
            )),
            None,
        )
    });
    LAZY.clone()
}
pub fn list_foldr(alpha: Type, beta: Type) -> Term {
    Term::term_spec(list_foldr_spec(), vec![alpha, beta])
}

/// `listFoldl : ('b → 'a → 'b) → 'b → list 'a → 'b`.
pub fn list_foldl_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let beta = Type::tfree("b");
        let f_ty = Type::fun(beta.clone(), Type::fun(alpha.clone(), beta.clone()));
        TermSpec::new(
            Canonical::ListFoldl,
            Some(Type::fun(
                f_ty,
                Type::fun(beta.clone(), Type::fun(list(alpha), beta)),
            )),
            None,
        )
    });
    LAZY.clone()
}
pub fn list_foldl(alpha: Type, beta: Type) -> Term {
    Term::term_spec(list_foldl_spec(), vec![alpha, beta])
}

/// `listTake : nat → list 'a → list 'a`.
pub fn list_take_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let la = list(alpha);
        TermSpec::new(
            Canonical::ListTake,
            Some(Type::fun(Type::nat(), Type::fun(la.clone(), la))),
            None,
        )
    });
    LAZY.clone()
}
pub fn list_take(alpha: Type) -> Term {
    Term::term_spec(list_take_spec(), vec![alpha])
}

/// `listSkip : nat → list 'a → list 'a`.
pub fn list_skip_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let la = list(alpha);
        TermSpec::new(
            Canonical::ListSkip,
            Some(Type::fun(Type::nat(), Type::fun(la.clone(), la))),
            None,
        )
    });
    LAZY.clone()
}
pub fn list_skip(alpha: Type) -> Term {
    Term::term_spec(list_skip_spec(), vec![alpha])
}

/// `listIndex : nat → list 'a → option 'a`.
pub fn list_index_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        TermSpec::new(
            Canonical::ListIndex,
            Some(Type::fun(
                Type::nat(),
                Type::fun(list(alpha.clone()), option(alpha)),
            )),
            None,
        )
    });
    LAZY.clone()
}
pub fn list_index(alpha: Type) -> Term {
    Term::term_spec(list_index_spec(), vec![alpha])
}

/// `listRepeat : nat → 'a → list 'a`.
pub fn list_repeat_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        TermSpec::new(
            Canonical::ListRepeat,
            Some(Type::fun(
                Type::nat(),
                Type::fun(alpha.clone(), list(alpha)),
            )),
            None,
        )
    });
    LAZY.clone()
}
pub fn list_repeat(alpha: Type) -> Term {
    Term::term_spec(list_repeat_spec(), vec![alpha])
}

/// `listFlatten : list (list 'a) → list 'a`.
pub fn list_flatten_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        TermSpec::new(
            Canonical::ListFlatten,
            Some(Type::fun(list(list(alpha.clone())), list(alpha))),
            None,
        )
    });
    LAZY.clone()
}
pub fn list_flatten(alpha: Type) -> Term {
    Term::term_spec(list_flatten_spec(), vec![alpha])
}
