//! `list 'a := stream (option 'a) where finite` + constructors +
//! list operations.
//!
//! The selector predicate is `finite` from
//! [`crate::defs::stream::finite`]:
//! `λs:stream(option α). ∃N. ∀n. nat_le N n ⟹ s n = none`.
//! So `list α` is exactly the subset of `stream (option α)` that's
//! eventually `none` — i.e. has finite "real" content.
//!
//! `nil`/`cons`/`head`/`tail`/`listIndex` are *defined* here in terms
//! of the `stream` carrier (via the `abs`/`rep` bridge — see below).
//! The remaining higher-order operations (`listLength`, `listCat`,
//! `listMap`, `listFilter`, `listFoldr`/`listFoldl`, `listTake`/
//! `listSkip`, `listRepeat`, `listFlatten`) stay **declaration-only**:
//! a clean structural definition needs a `list` recursor (fold over
//! the finite prefix), which the kernel does not yet expose. They have
//! committed type signatures; their bodies are tracked in
//! `docs/roadmap.md`.

use std::sync::LazyLock;

use crate::hol;
use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::nat::nat_rec;
use super::option::{none, option, some};
use super::spec::{TermSpec, TypeSpec};
use super::stream::{
    finite, stream, stream_at, stream_const, stream_head, stream_make, stream_tail,
};

/// `list 'a := stream (option 'a) where finite`. The carrier is
/// the spec'd `stream (option α)`; the selector predicate is
/// `finite α`, which restricts to streams that are eventually
/// `none`.
pub fn list_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let carrier = stream(option(alpha.clone()));
        TypeSpec::subtype(Canonical::List, carrier, finite(alpha))
    });
    LAZY.clone()
}
pub fn list(alpha: Type) -> Type {
    Type::spec(list_spec(), vec![alpha])
}

// ============================================================================
// Constructors / destructors, defined via the `stream` carrier bridge
// (`abs`/`rep` cross between `list α` and `stream (option α)`).
//
//   nil       ≔ abs (streamConst none)
//   cons x xs ≔ abs (streamMake (λn. natRec (some x)
//                                      (λk _. streamAt (rep xs) k) n))
//   head xs   ≔ streamHead (rep xs)
//   tail xs   ≔ abs (streamTail (rep xs))
//
// The cons stream is `some x` at index 0 and `(rep xs)` shifted by one
// afterwards. Finiteness of the results (so they really land in
// `list α`) is a downstream proof.
// ============================================================================

fn nil_body() -> Term {
    let alpha = Type::tfree("a");
    let opt = option(alpha.clone());
    let all_none = Term::app(stream_const(opt), none(alpha.clone()));
    Term::app(Term::spec_abs(list_spec(), vec![alpha]), all_none)
}

poly_let_term! {
    /// `nil : list 'a` ≡ `abs (streamConst none)` — the empty list as
    /// the everywhere-`none` stream.
    nil_spec, nil(alpha), Canonical::Nil, nil_body()
}

fn cons_body() -> Term {
    let alpha = Type::tfree("a");
    let opt = option(alpha.clone());
    let list_a = list(alpha.clone());

    let x = Term::free("x", alpha.clone());
    let xs = Term::free("xs", list_a.clone());
    let rep_xs = Term::app(Term::spec_rep(list_spec(), vec![alpha.clone()]), xs);

    // f = λk:nat. λ_:option α. streamAt (rep xs) k  (the value at k+1)
    let k = Term::free("k", Type::nat());
    let at_k = Term::app(Term::app(stream_at(opt.clone()), rep_xs), k);
    let f = hol::pub_abs("k", Type::nat(), Term::abs("_", opt.clone(), at_k));

    // λn. natRec[option α] (some x) f n
    let n = Term::free("n", Type::nat());
    let some_x = Term::app(some(alpha.clone()), x.clone());
    let rec = Term::app(Term::app(Term::app(nat_rec(opt.clone()), some_x), f), n);
    let stream_fn = hol::pub_abs("n", Type::nat(), rec);

    let made = Term::app(stream_make(opt), stream_fn);
    let consed = Term::app(Term::spec_abs(list_spec(), vec![alpha.clone()]), made);
    let lam_xs = hol::pub_abs("xs", list_a, consed);
    hol::pub_abs("x", alpha, lam_xs)
}

poly_let_term! {
    /// `cons : 'a → list 'a → list 'a` — prepend, via `natRec` over the
    /// underlying `stream (option α)`.
    cons_spec, cons(alpha), Canonical::Cons, cons_body()
}

fn head_body() -> Term {
    let alpha = Type::tfree("a");
    let opt = option(alpha.clone());
    let xs = Term::free("xs", list(alpha.clone()));
    let rep_xs = Term::app(Term::spec_rep(list_spec(), vec![alpha.clone()]), xs);
    let h = Term::app(stream_head(opt), rep_xs);
    hol::pub_abs("xs", list(alpha), h)
}

poly_let_term! {
    /// `head : list 'a → option 'a` ≡ `λxs. streamHead (rep xs)`. The
    /// first element (`none` for the empty list).
    head_spec, head(alpha), Canonical::Head, head_body()
}

fn tail_body() -> Term {
    let alpha = Type::tfree("a");
    let opt = option(alpha.clone());
    let xs = Term::free("xs", list(alpha.clone()));
    let rep_xs = Term::app(Term::spec_rep(list_spec(), vec![alpha.clone()]), xs);
    let t = Term::app(stream_tail(opt), rep_xs);
    let tailed = Term::app(Term::spec_abs(list_spec(), vec![alpha.clone()]), t);
    hol::pub_abs("xs", list(alpha), tailed)
}

poly_let_term! {
    /// `tail : list 'a → list 'a` ≡ `λxs. abs (streamTail (rep xs))`.
    /// Drop the first element.
    tail_spec, tail(alpha), Canonical::Tail, tail_body()
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

fn list_index_body() -> Term {
    let alpha = Type::tfree("a");
    let opt = option(alpha.clone());
    let n = Term::free("n", Type::nat());
    let xs = Term::free("xs", list(alpha.clone()));
    let rep_xs = Term::app(Term::spec_rep(list_spec(), vec![alpha.clone()]), xs);
    let at = Term::app(Term::app(stream_at(opt), rep_xs), n);
    let lam_xs = hol::pub_abs("xs", list(alpha), at);
    hol::pub_abs("n", Type::nat(), lam_xs)
}

poly_let_term! {
    /// `listIndex : nat → list 'a → option 'a` ≡
    /// `λn xs. streamAt (rep xs) n`. The `n`th element, or `none` past
    /// the end (the underlying stream is `none` there).
    list_index_spec, list_index(alpha), Canonical::ListIndex, list_index_body()
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
