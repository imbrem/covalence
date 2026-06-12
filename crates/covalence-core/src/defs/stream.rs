//! `stream 'a := nat → 'a` + stream-level operations + the
//! `finite` predicate.
//!
//! `stream α` is an opaque TypeSpec wrapper over the carrier
//! `nat → α`. The selector predicate is trivially true (`λ_. T`)
//! — every function `nat → α` IS a stream. But the wrapper is
//! still useful: it gives streams their own Canonical label and
//! makes them a distinct type at the kernel-rule level.
//!
//! Because the type is opaque, you can't directly apply a value
//! `s : stream α` as a function. The bridge is `stream_at`:
//!
//! ```text
//!     stream_at   : stream 'a → nat → 'a       (extract an element)
//!     stream_make : (nat → 'a) → stream 'a     (build from a function)
//! ```
//!
//! These are declaration-only TermSpecs — the kernel commits to
//! their meaning at the model level (stream_at ∘ stream_make = id
//! and stream_make ∘ stream_at = id under η). All other
//! stream operations (head/tail/cons/const/iterate/nth) are
//! defined in terms of `stream_at` + `stream_make`.
//!
//! `list α` is the subset of `stream (option α)` satisfying the
//! `finite` predicate at the bottom of this module:
//! `λs. ∃N. ∀n. nat_le N n ⟹ stream_at s n = none`.

use std::sync::LazyLock;

use crate::hol;
use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::helpers::any;
use super::nat::{iter, nat_le};
use super::option::{none, option};
use super::spec::{TermSpec, TypeSpec};

/// `stream 'a := nat → 'a`. The selector predicate is trivially
/// true — every function from `nat` to `α` is a stream — but the
/// wrapper still introduces `stream α` as a distinct TypeKind::Spec
/// leaf. Cross from "stream α" to "nat → α" (and back) via
/// `stream_at` / `stream_make`.
pub fn stream_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let carrier = Type::fun(Type::nat(), alpha);
        TypeSpec::new(Canonical::Stream, Some(carrier.clone()), Some(any(&carrier)))
    });
    LAZY.clone()
}
/// `stream α`.
pub fn stream(alpha: Type) -> Type {
    Type::spec(stream_spec(), vec![alpha])
}

// ============================================================================
// stream_at / stream_make — the abs/rep bridge
//
// `stream α` is opaque to the type-checker (a Spec leaf), so we
// expose declaration-only TermSpecs to convert between the opaque
// `stream α` and its underlying carrier `nat → α`. Semantically:
//
//     ∀(s : stream α), n : nat. stream_at s n  ≜  the nth element
//     ∀(f : nat → α). stream_make f             ≜  the stream whose nth
//                                                  element is f n
//
// Under η + the trivially-true selector predicate:
//
//     stream_at  ∘ stream_make  = id            (rep ∘ abs = id)
//     stream_make ∘ stream_at   = id            (abs ∘ rep = id)
//
// These equations are postulated downstream until a derivation
// using `Thm::new_type_definition`'s `abs_rep` / `rep_abs_*`
// landings replaces them. (Same pattern as `nat_axioms` in
// `covalence-hol`.)
// ============================================================================

/// `streamAt : stream 'a → nat → 'a`. Extract the nth element.
/// Declaration-only — semantics is "apply the underlying
/// `nat → α` function representation".
pub fn stream_at_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let stream_a = stream(alpha.clone());
        TermSpec::new(
            Canonical::StreamAt,
            Some(Type::fun(stream_a, Type::fun(Type::nat(), alpha))),
            None,
        )
    });
    LAZY.clone()
}
pub fn stream_at(alpha: Type) -> Term {
    Term::term_spec(stream_at_spec(), vec![alpha])
}

/// `streamMake : (nat → 'a) → stream 'a`. Build a stream from a
/// function representation. Declaration-only — semantics is the
/// canonical injection from the carrier into the opaque stream
/// type. Inverse of `stream_at` (under η).
pub fn stream_make_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let f_ty = Type::fun(Type::nat(), alpha.clone());
        TermSpec::new(
            Canonical::StreamMake,
            Some(Type::fun(f_ty, stream(alpha))),
            None,
        )
    });
    LAZY.clone()
}
pub fn stream_make(alpha: Type) -> Term {
    Term::term_spec(stream_make_spec(), vec![alpha])
}

// ============================================================================
// Stream operations
//
// Each is a let-style TermSpec whose body uses `stream_at` to
// reach into the opaque stream type, and `stream_make` to build
// the result when it's also a stream.
// ============================================================================

/// Body of `streamHead := λs:stream α. stream_at s 0`.
fn stream_head_body() -> Term {
    let alpha = Type::tfree("a");
    let stream_a = stream(alpha.clone());
    let s = Term::free("s", stream_a.clone());
    let body = Term::app(Term::app(stream_at(alpha), s), hol::zero());
    hol::pub_abs("s", stream_a, body)
}

poly_let_term! {
    /// `streamHead : stream 'a → 'a` — `λs. stream_at s 0`. The
    /// first element of the stream.
    stream_head_spec, stream_head(alpha), Canonical::StreamHead, stream_head_body()
}

/// Body of `streamTail := λs:stream α. stream_make (λn:nat. stream_at s (succ n))`.
fn stream_tail_body() -> Term {
    let alpha = Type::tfree("a");
    let stream_a = stream(alpha.clone());
    let s = Term::free("s", stream_a.clone());
    let n = Term::free("n", Type::nat());
    let succ_n = Term::app(hol::succ_fn(), n.clone());
    // stream_at s (succ n)
    let elem = Term::app(Term::app(stream_at(alpha.clone()), s.clone()), succ_n);
    let lam_n = hol::pub_abs("n", Type::nat(), elem);
    // stream_make (λn. stream_at s (succ n))
    let body = Term::app(stream_make(alpha), lam_n);
    hol::pub_abs("s", stream_a, body)
}

poly_let_term! {
    /// `streamTail : stream 'a → stream 'a` —
    /// `λs. stream_make (λn. stream_at s (succ n))`. Drop the
    /// first element.
    stream_tail_spec, stream_tail(alpha), Canonical::StreamTail, stream_tail_body()
}

/// Body of `streamConst := λx:α. stream_make (λ_:nat. x)`.
fn stream_const_body() -> Term {
    let alpha = Type::tfree("a");
    let x = Term::free("x", alpha.clone());
    let n_lambda = Term::abs("_", Type::nat(), x.clone());
    let body = Term::app(stream_make(alpha.clone()), n_lambda);
    hol::pub_abs("x", alpha, body)
}

poly_let_term! {
    /// `streamConst : 'a → stream 'a` —
    /// `λx. stream_make (λ_. x)`. The constant stream `x, x, x, …`.
    stream_const_spec, stream_const(alpha), Canonical::StreamConst, stream_const_body()
}

/// Body of `streamIterate := λx:α. λf:α→α. stream_make (λn:nat. iter n f x)`.
fn stream_iterate_body() -> Term {
    let alpha = Type::tfree("a");
    let alpha_to_alpha = Type::fun(alpha.clone(), alpha.clone());
    let x = Term::free("x", alpha.clone());
    let f = Term::free("f", alpha_to_alpha.clone());
    let n = Term::free("n", Type::nat());

    // iter n f x
    let iter_at_alpha = iter(alpha.clone());
    let app1 = Term::app(iter_at_alpha, n.clone());
    let app2 = Term::app(app1, f.clone());
    let iter_body = Term::app(app2, x.clone());

    // stream_make (λn. iter n f x)
    let lam_n = hol::pub_abs("n", Type::nat(), iter_body);
    let body = Term::app(stream_make(alpha.clone()), lam_n);

    let lam_f = hol::pub_abs("f", alpha_to_alpha, body);
    hol::pub_abs("x", alpha, lam_f)
}

poly_let_term! {
    /// `streamIterate : 'a → ('a → 'a) → stream 'a` —
    /// `λx f. stream_make (λn. iter n f x)`. The stream
    /// `x, f x, f (f x), …`.
    stream_iterate_spec, stream_iterate(alpha), Canonical::StreamIterate, stream_iterate_body()
}

// `streamNth` was originally the function-application bridge;
// now that role is filled by `stream_at` directly. `streamNth n s`
// reduces to `stream_at s n` (arg-flipped). We keep it as a
// convenience wrapper.

/// Body of `streamNth := λn:nat. λs:stream α. stream_at s n`.
fn stream_nth_body() -> Term {
    let alpha = Type::tfree("a");
    let stream_a = stream(alpha.clone());
    let n = Term::free("n", Type::nat());
    let s = Term::free("s", stream_a.clone());
    let body = Term::app(Term::app(stream_at(alpha), s.clone()), n.clone());
    let lam_s = hol::pub_abs("s", stream_a, body);
    hol::pub_abs("n", Type::nat(), lam_s)
}

poly_let_term! {
    /// `streamNth : nat → stream 'a → 'a` —
    /// `λn s. stream_at s n`. Convenience wrapper for
    /// `stream_at` with arguments flipped.
    stream_nth_spec, stream_nth(alpha), Canonical::StreamNth, stream_nth_body()
}

// ============================================================================
// finite — the selector predicate for `list α`
//
//     finite ≔ λs:stream(option α).
//                  ∃N:nat. ∀n:nat. nat_le N n ⟹ stream_at s n = none
//
// A stream is "finite" iff there's some bound N after which every
// position holds `none`. Used as the selector predicate for
// `list α := stream (option α) where finite α`.
// ============================================================================

/// Body of
/// `finite := λs:stream(option α). ∃N. ∀n. nat_le N n ⟹ stream_at s n = none`.
fn finite_body() -> Term {
    let alpha = Type::tfree("a");
    let opt_a = option(alpha.clone());
    let stream_opt_a = stream(opt_a.clone());

    let s = Term::free("s", stream_opt_a.clone());
    let big_n = Term::free("N", Type::nat());
    let n_inner = Term::free("n", Type::nat());

    // stream_at s n  (at carrier α-of-option = option α)
    let stream_at_at_opt = stream_at(opt_a);
    let s_n = Term::app(Term::app(stream_at_at_opt, s.clone()), n_inner.clone());
    // stream_at s n = none
    let eq_none = hol::hol_eq(s_n, none(alpha));
    // nat_le N n
    let le = Term::app(Term::app(nat_le(), big_n.clone()), n_inner.clone());
    // nat_le N n ⟹ stream_at s n = none
    let imp = hol::hol_imp(le, eq_none);
    // ∀n:nat. ...
    let all_n = hol::hol_forall("n", Type::nat(), imp);
    // ∃N:nat. ...
    let ex_n = hol::hol_exists("N", Type::nat(), all_n);
    // λs:stream(option α). ...
    hol::pub_abs("s", stream_opt_a, ex_n)
}

poly_let_term! {
    /// `finite : stream (option 'a) → bool` —
    /// `λs. ∃N. ∀n. nat_le N n ⟹ stream_at s n = none`. The
    /// predicate that characterizes finite-list-shaped streams
    /// (eventually all `none`). Selector predicate for
    /// `list 'a`.
    finite_spec, finite(alpha), Canonical::Finite, finite_body()
}
