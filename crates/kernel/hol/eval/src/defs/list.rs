//! The higher-order / derived `list` ops (moved from the core `defs/`
//! catalogue): `head`, `tail`, `listCat`, `listMap`, `listFilter`,
//! `listFoldl`, `listTake`, `listSkip`, `listIndex`, `listRepeat`,
//! `listFlatten`.
//!
//! The `list` TYPE spec and the ops its selector predicate / the
//! fixed-width type chain need (`nil`, `cons`, `listFoldr`,
//! `listLength`) are D3 residue in `covalence_core::defs::list`.

use std::sync::LazyLock;

use covalence_core::hol;
use covalence_core::term::{Term, Type};

use crate::defs::{
    Canonical, TermSpec, cons, list, list_foldr, list_spec, nat_add, nat_lt, nil, none, option,
    option_case, some, stream_at, stream_head, stream_mk, stream_tail,
};

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

fn list_cat_body() -> Term {
    // listCat ≔ λxs ys. listFoldr cons ys xs
    let alpha = Type::tfree("a");
    let la = list(alpha.clone());
    let xs = Term::free("xs", la.clone());
    let ys = Term::free("ys", la.clone());
    let folded = Term::app(
        Term::app(
            Term::app(list_foldr(alpha.clone(), la.clone()), cons(alpha.clone())),
            ys,
        ),
        xs,
    );
    let lam_ys = hol::pub_abs("ys", la.clone(), folded);
    hol::pub_abs("xs", la, lam_ys)
}

/// `listCat : list 'a → list 'a → list 'a` ≡ `λxs ys. foldr cons ys xs`.
pub fn list_cat_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let la = list(alpha);
        TermSpec::new(
            Canonical::ListCat,
            Some(Type::fun(la.clone(), Type::fun(la.clone(), la))),
            Some(list_cat_body()),
        )
    });
    LAZY.clone()
}
pub fn list_cat(alpha: Type) -> Term {
    Term::term_spec(list_cat_spec(), vec![alpha])
}

fn list_map_body() -> Term {
    // listMap ≔ λf xs. abs (streamMk (λi. optionCase none (λx. some (f x))
    //                                       (streamAt (rep xs) i)))
    // Pointwise over the carrier stream: map the `option α` at each index.
    let alpha = Type::tfree("a");
    let beta = Type::tfree("b");
    let opt_a = option(alpha.clone());
    let opt_b = option(beta.clone());
    let f_ty = Type::fun(alpha.clone(), beta.clone());

    let f = Term::free("f", f_ty.clone());
    let xs = Term::free("xs", list(alpha.clone()));
    let i = Term::free("i", Type::nat());

    // streamAt (rep xs) i : option α
    let rep_xs = Term::app(Term::spec_rep(list_spec(), vec![alpha.clone()]), xs);
    let elem = Term::app(Term::app(stream_at(opt_a.clone()), rep_xs), i);

    // some-branch: λx:α. some (f x) : α → option β
    let x = Term::free("x", alpha.clone());
    let some_fx = Term::app(some(beta.clone()), Term::app(f.clone(), x));
    let some_branch = hol::pub_abs("x", alpha.clone(), some_fx);

    // optionCase none (λx. some (f x)) elem : option β
    let case = option_case(alpha.clone(), opt_b.clone());
    let mapped = Term::app(
        Term::app(Term::app(case, none(beta.clone())), some_branch),
        elem,
    );

    // abs (streamMk (λi. mapped)) : list β
    let made = Term::app(stream_mk(opt_b), hol::pub_abs("i", Type::nat(), mapped));
    let result = Term::app(Term::spec_abs(list_spec(), vec![beta.clone()]), made);

    let lam_xs = hol::pub_abs("xs", list(alpha), result);
    hol::pub_abs("f", f_ty, lam_xs)
}

poly_let_term! {
    /// `listMap : ('a → 'b) → list 'a → list 'b` — map pointwise over
    /// the carrier stream's `option` elements.
    list_map_spec, list_map(alpha, beta), Canonical::ListMap, list_map_body()
}

fn list_filter_body() -> Term {
    // listFilter ≔ λp xs. listFoldr (λx acc. cond (p x) (cons x acc) acc) nil xs
    let alpha = Type::tfree("a");
    let la = list(alpha.clone());
    let p_ty = Type::fun(alpha.clone(), Type::bool());

    let p = Term::free("p", p_ty.clone());
    let xs = Term::free("xs", la.clone());

    // step: λx:α. λacc:list α. cond (p x) (cons x acc) acc
    let x = Term::free("x", alpha.clone());
    let acc = Term::free("acc", la.clone());
    let p_x = Term::app(p.clone(), x.clone());
    let cons_x_acc = Term::app(Term::app(cons(alpha.clone()), x.clone()), acc.clone());
    let chosen = Term::cond(p_x, cons_x_acc, acc);
    let step = hol::pub_abs("x", alpha.clone(), hol::pub_abs("acc", la.clone(), chosen));

    let folded = Term::app(
        Term::app(
            Term::app(list_foldr(alpha.clone(), la.clone()), step),
            nil(alpha.clone()),
        ),
        xs,
    );
    let lam_xs = hol::pub_abs("xs", la, folded);
    hol::pub_abs("p", p_ty, lam_xs)
}

/// `listFilter : ('a → bool) → list 'a → list 'a` ≡
/// `λp xs. foldr (λx acc. cond (p x) (cons x acc) acc) nil xs`.
pub fn list_filter_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let p_ty = Type::fun(alpha.clone(), Type::bool());
        let la = list(alpha);
        TermSpec::new(
            Canonical::ListFilter,
            Some(Type::fun(p_ty, Type::fun(la.clone(), la))),
            Some(list_filter_body()),
        )
    });
    LAZY.clone()
}
pub fn list_filter(alpha: Type) -> Term {
    Term::term_spec(list_filter_spec(), vec![alpha])
}

/// Selector predicate for `listFoldl` — the left-fold defining
/// equations: `λfl. ∀f z. fl f z nil = z ∧
/// ∀x xs. fl f z (cons x xs) = fl f (f z x) xs`.
fn list_foldl_predicate() -> Term {
    let alpha = Type::tfree("a");
    let beta = Type::tfree("b");
    let la = list(alpha.clone());
    let f_ty = Type::fun(beta.clone(), Type::fun(alpha.clone(), beta.clone()));
    let fl_ty = Type::fun(
        f_ty.clone(),
        Type::fun(beta.clone(), Type::fun(la.clone(), beta.clone())),
    );

    let fl = Term::free("fl", fl_ty.clone());
    let f = Term::free("f", f_ty.clone());
    let z = Term::free("z", beta.clone());

    // fl f : β → list α → β
    let fl_f = Term::app(fl, f.clone());

    // base: fl f z nil = z
    let base = hol::hol_eq(
        Term::app(Term::app(fl_f.clone(), z.clone()), nil(alpha.clone())),
        z.clone(),
    );

    // step: ∀x xs. fl f z (cons x xs) = fl f (f z x) xs
    let x = Term::free("x", alpha.clone());
    let xs = Term::free("xs", la.clone());
    let cons_x_xs = Term::app(Term::app(cons(alpha.clone()), x.clone()), xs.clone());
    let lhs = Term::app(Term::app(fl_f.clone(), z.clone()), cons_x_xs);
    let f_z_x = Term::app(Term::app(f.clone(), z.clone()), x.clone());
    let rhs = Term::app(Term::app(fl_f, f_z_x), xs.clone());
    let step_eq = hol::hol_eq(lhs, rhs);
    let step = hol::hol_forall("x", alpha, hol::hol_forall("xs", la, step_eq));

    let body = hol::hol_and(base, step);
    let body_fz = hol::hol_forall("f", f_ty, hol::hol_forall("z", beta, body));
    hol::pub_abs("fl", fl_ty, body_fz)
}

/// `listFoldl : ('b → 'a → 'b) → 'b → list 'a → 'b`. The left-fold
/// recursor; pinned by `list_foldl_predicate` (Hilbert ε).
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
            Some(list_foldl_predicate()),
        )
    });
    LAZY.clone()
}
pub fn list_foldl(alpha: Type, beta: Type) -> Term {
    Term::term_spec(list_foldl_spec(), vec![alpha, beta])
}

fn list_take_body() -> Term {
    // listTake ≔ λn xs. abs (streamMk (λi. cond (natLt i n)
    //                                        (streamAt (rep xs) i) none))
    let alpha = Type::tfree("a");
    let opt_a = option(alpha.clone());
    let n = Term::free("n", Type::nat());
    let xs = Term::free("xs", list(alpha.clone()));
    let i = Term::free("i", Type::nat());

    let rep_xs = Term::app(Term::spec_rep(list_spec(), vec![alpha.clone()]), xs);
    let elem = Term::app(Term::app(stream_at(opt_a.clone()), rep_xs), i.clone());
    let lt = Term::app(Term::app(nat_lt(), i), n.clone());
    let chosen = Term::cond(lt, elem, none(alpha.clone()));

    let made = Term::app(stream_mk(opt_a), hol::pub_abs("i", Type::nat(), chosen));
    let result = Term::app(Term::spec_abs(list_spec(), vec![alpha.clone()]), made);
    let lam_xs = hol::pub_abs("xs", list(alpha), result);
    hol::pub_abs("n", Type::nat(), lam_xs)
}

/// `listTake : nat → list 'a → list 'a` — keep the first `n` elements
/// (positions `≥ n` become `none`), pointwise on the carrier stream.
pub fn list_take_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let la = list(alpha);
        TermSpec::new(
            Canonical::ListTake,
            Some(Type::fun(Type::nat(), Type::fun(la.clone(), la))),
            Some(list_take_body()),
        )
    });
    LAZY.clone()
}
pub fn list_take(alpha: Type) -> Term {
    Term::term_spec(list_take_spec(), vec![alpha])
}

fn list_skip_body() -> Term {
    // listSkip ≔ λn xs. abs (streamMk (λi. streamAt (rep xs) (natAdd i n)))
    let alpha = Type::tfree("a");
    let opt_a = option(alpha.clone());
    let n = Term::free("n", Type::nat());
    let xs = Term::free("xs", list(alpha.clone()));
    let i = Term::free("i", Type::nat());

    let rep_xs = Term::app(Term::spec_rep(list_spec(), vec![alpha.clone()]), xs);
    let idx = Term::app(Term::app(nat_add(), i), n.clone());
    let elem = Term::app(Term::app(stream_at(opt_a.clone()), rep_xs), idx);

    let made = Term::app(stream_mk(opt_a), hol::pub_abs("i", Type::nat(), elem));
    let result = Term::app(Term::spec_abs(list_spec(), vec![alpha.clone()]), made);
    let lam_xs = hol::pub_abs("xs", list(alpha), result);
    hol::pub_abs("n", Type::nat(), lam_xs)
}

/// `listSkip : nat → list 'a → list 'a` — drop the first `n` elements
/// by shifting the carrier stream's indices up by `n`.
pub fn list_skip_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let la = list(alpha);
        TermSpec::new(
            Canonical::ListSkip,
            Some(Type::fun(Type::nat(), Type::fun(la.clone(), la))),
            Some(list_skip_body()),
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

fn list_repeat_body() -> Term {
    // listRepeat ≔ λn x. abs (streamMk (λi. cond (natLt i n) (some x) none))
    let alpha = Type::tfree("a");
    let opt_a = option(alpha.clone());
    let n = Term::free("n", Type::nat());
    let x = Term::free("x", alpha.clone());
    let i = Term::free("i", Type::nat());

    let lt = Term::app(Term::app(nat_lt(), i), n.clone());
    let some_x = Term::app(some(alpha.clone()), x.clone());
    let chosen = Term::cond(lt, some_x, none(alpha.clone()));

    let made = Term::app(stream_mk(opt_a), hol::pub_abs("i", Type::nat(), chosen));
    let result = Term::app(Term::spec_abs(list_spec(), vec![alpha.clone()]), made);
    let lam_x = hol::pub_abs("x", alpha.clone(), result);
    hol::pub_abs("n", Type::nat(), lam_x)
}

/// `listRepeat : nat → 'a → list 'a` — the list of `n` copies of `x`,
/// built pointwise on the carrier stream.
pub fn list_repeat_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        TermSpec::new(
            Canonical::ListRepeat,
            Some(Type::fun(
                Type::nat(),
                Type::fun(alpha.clone(), list(alpha)),
            )),
            Some(list_repeat_body()),
        )
    });
    LAZY.clone()
}
pub fn list_repeat(alpha: Type) -> Term {
    Term::term_spec(list_repeat_spec(), vec![alpha])
}

fn list_flatten_body() -> Term {
    // listFlatten ≔ λxss. listFoldr listCat nil xss
    let alpha = Type::tfree("a");
    let la = list(alpha.clone());
    let lla = list(la.clone());
    let xss = Term::free("xss", lla.clone());
    let folded = Term::app(
        Term::app(
            Term::app(list_foldr(la.clone(), la.clone()), list_cat(alpha.clone())),
            nil(alpha.clone()),
        ),
        xss,
    );
    hol::pub_abs("xss", lla, folded)
}

/// `listFlatten : list (list 'a) → list 'a` ≡
/// `λxss. foldr cat nil xss`.
pub fn list_flatten_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        TermSpec::new(
            Canonical::ListFlatten,
            Some(Type::fun(list(list(alpha.clone())), list(alpha))),
            Some(list_flatten_body()),
        )
    });
    LAZY.clone()
}
pub fn list_flatten(alpha: Type) -> Term {
    Term::term_spec(list_flatten_spec(), vec![alpha])
}
