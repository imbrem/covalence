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
//!
//! The higher-order operations are all defined too. The two structural
//! recursors are `listFoldr` / `listFoldl`, given Hilbert-ε selector
//! predicates by their defining equations (`fr f z nil = z`,
//! `fr f z (cons x xs) = f x (fr f z xs)`, and the left-fold mirror) —
//! the same shape as `natRec` in [`crate::defs::nat`]. Everything else
//! is a `let` definition: the *positional* ops (`listTake`, `listSkip`,
//! `listRepeat`, `listMap`, `listIndex`) work pointwise on the carrier
//! stream, while the *structural* ops (`listLength`, `listCat`,
//! `listFilter`, `listFlatten`) factor through `listFoldr`.

use std::sync::LazyLock;

use crate::hol;
use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::nat::{nat_rec, nat_succ};
use super::option::{none, option, some};
use super::spec::{TermSpec, TypeSpec};
use super::stream::{finite, stream, stream_at, stream_const, stream_mk};

/// The **list selector predicate** at element type `α`:
/// `λs. finite s ∧ (∀i. stream_at s i = none ⟹ stream_at s (succ i) =
/// none)` — a finite, *contiguous* stream of options (a `some`-prefix
/// followed by all `none`, no interior holes).
///
/// The contiguity conjunct is what makes the `nil` / `cons` constructors
/// **exhaustive**: without it, a finite stream like `[none, some a, none,
/// …]` would be a `list α` value reachable by neither constructor (its
/// head is `none`, so it is not a `cons`, but it is not `nil` either), and
/// structural induction over `nil` / `cons` would be *false*. With it,
/// every list is `nil` (the empty prefix) or `cons x xs` (a `some` head
/// over a shorter contiguous tail). Matches the design in
/// `notes/vibes/type-hierarchy.md` (`∃n. ∀i. (i<n → ∃a. s i = some a) ∧
/// (n≤i → s i = none)`); contiguity + finiteness is the equivalent,
/// proof-friendlier phrasing.
fn list_predicate() -> Term {
    let alpha = Type::tfree("a");
    let opt = option(alpha.clone());
    let stream_opt = stream(opt.clone());

    let s = Term::free("s", stream_opt.clone());
    // finite s
    let fin = Term::app(finite(alpha.clone()), s.clone());
    // ∀i. stream_at s i = none ⟹ stream_at s (succ i) = none
    let i = Term::free("i", Type::nat());
    let at_i = Term::app(Term::app(stream_at(opt.clone()), s.clone()), i.clone());
    let at_si = Term::app(
        Term::app(stream_at(opt), s.clone()),
        Term::app(nat_succ(), i.clone()),
    );
    let contig_step = hol::hol_imp(
        hol::hol_eq(at_i, none(alpha.clone())),
        hol::hol_eq(at_si, none(alpha.clone())),
    );
    let contig = hol::hol_forall("i", Type::nat(), contig_step);

    hol::pub_abs("s", stream_opt, hol::hol_and(fin, contig))
}

/// `list 'a := stream (option 'a) where (finite ∧ contiguous)`. The
/// carrier is the spec'd `stream (option α)`; the selector predicate is
/// `list_predicate` — finite *and* hole-free, so `nil` / `cons` cover
/// every value (see `list_predicate` for why contiguity is required).
pub fn list_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let carrier = stream(option(alpha.clone()));
        let _ = &alpha;
        TypeSpec::subtype(Canonical::List, carrier, list_predicate())
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
//   cons x xs ≔ abs (streamMk (λn. natRec (some x)
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
    let f = hol::pub_abs("k", Type::nat(), Term::abs(opt.clone(), at_k));

    // λn. natRec[option α] (some x) f n
    let n = Term::free("n", Type::nat());
    let some_x = Term::app(some(alpha.clone()), x.clone());
    let rec = Term::app(Term::app(Term::app(nat_rec(opt.clone()), some_x), f), n);
    let stream_fn = hol::pub_abs("n", Type::nat(), rec);

    let made = Term::app(stream_mk(opt), stream_fn);
    let consed = Term::app(Term::spec_abs(list_spec(), vec![alpha.clone()]), made);
    let lam_xs = hol::pub_abs("xs", list_a, consed);
    hol::pub_abs("x", alpha, lam_xs)
}

poly_let_term! {
    /// `cons : 'a → list 'a → list 'a` — prepend, via `natRec` over the
    /// underlying `stream (option α)`.
    cons_spec, cons(alpha), Canonical::Cons, cons_body()
}

fn list_length_body() -> Term {
    // listLength ≔ λxs. listFoldr (λ_:α. λacc:nat. succ acc) 0 xs
    let alpha = Type::tfree("a");
    let acc = Term::free("acc", Type::nat());
    let succ_acc = Term::app(hol::succ_fn(), acc);
    // λ_:α. λacc:nat. succ acc  (the element is ignored)
    let step = Term::abs(alpha.clone(), hol::pub_abs("acc", Type::nat(), succ_acc));
    let xs = Term::free("xs", list(alpha.clone()));
    let folded = Term::app(
        Term::app(
            Term::app(list_foldr(alpha.clone(), Type::nat()), step),
            hol::zero(),
        ),
        xs,
    );
    hol::pub_abs("xs", list(alpha), folded)
}

/// `listLength : list 'a → nat` ≡ `λxs. foldr (λ_ acc. succ acc) 0 xs`.
pub fn list_length_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        TermSpec::new(
            Canonical::ListLength,
            Some(Type::fun(list(alpha), Type::nat())),
            Some(list_length_body()),
        )
    });
    LAZY.clone()
}
pub fn list_length(alpha: Type) -> Term {
    Term::term_spec(list_length_spec(), vec![alpha])
}

/// Selector predicate for `listFoldr` — the right-fold defining
/// equations: `λfr. ∀f z. fr f z nil = z ∧
/// ∀x xs. fr f z (cons x xs) = f x (fr f z xs)`.
fn list_foldr_predicate() -> Term {
    let alpha = Type::tfree("a");
    let beta = Type::tfree("b");
    let la = list(alpha.clone());
    let f_ty = Type::fun(alpha.clone(), Type::fun(beta.clone(), beta.clone()));
    let fr_ty = Type::fun(
        f_ty.clone(),
        Type::fun(beta.clone(), Type::fun(la.clone(), beta.clone())),
    );

    let fr = Term::free("fr", fr_ty.clone());
    let f = Term::free("f", f_ty.clone());
    let z = Term::free("z", beta.clone());

    // fr f z : list α → β
    let fr_f_z = Term::app(Term::app(fr, f.clone()), z.clone());

    // base: fr f z nil = z
    let base = hol::hol_eq(Term::app(fr_f_z.clone(), nil(alpha.clone())), z.clone());

    // step: ∀x xs. fr f z (cons x xs) = f x (fr f z xs)
    let x = Term::free("x", alpha.clone());
    let xs = Term::free("xs", la.clone());
    let cons_x_xs = Term::app(Term::app(cons(alpha.clone()), x.clone()), xs.clone());
    let lhs = Term::app(fr_f_z.clone(), cons_x_xs);
    let rhs = Term::app(
        Term::app(f.clone(), x.clone()),
        Term::app(fr_f_z, xs.clone()),
    );
    let step_eq = hol::hol_eq(lhs, rhs);
    let step = hol::hol_forall("x", alpha, hol::hol_forall("xs", la, step_eq));

    let body = hol::hol_and(base, step);
    let body_fz = hol::hol_forall("f", f_ty, hol::hol_forall("z", beta, body));
    hol::pub_abs("fr", fr_ty, body_fz)
}

/// `listFoldr : ('a → 'b → 'b) → 'b → list 'a → 'b`. The right-fold
/// recursor; pinned by `list_foldr_predicate` (Hilbert ε).
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
            Some(list_foldr_predicate()),
        )
    });
    LAZY.clone()
}
pub fn list_foldr(alpha: Type, beta: Type) -> Term {
    Term::term_spec(list_foldr_spec(), vec![alpha, beta])
}
