//! HOL term constructors used by the kernel's inference rules.
//!
//! Everything here is pure term-building over the kernel atoms. No
//! `Thm` machinery is touched. The `pub(crate)` exports are consumed
//! by `thm.rs` (the inference rules need `hol_eq` / `hol_imp` /
//! `hol_forall` / `hol_not` to build their conclusions — including
//! [`crate::Thm::nat_induct`]) and by `defs/*.rs`'s spec carriers
//! (which need `pub_abs` and the `zero` / `succ_fn` / `pred_fn`
//! building blocks).

use covalence_types::Nat;

use crate::defs;
use crate::subst::close;
use crate::term::{Term, Type};

// ============================================================================
// HOL connective constructors
// ============================================================================
//
// `=` is the primitive `TermKind::Eq`; every connective below is the
// defined constant from `crate::defs::logic` (a `Spec` leaf). The
// `hol_*` builders just spell the application chains.

/// HOL `p ⟹ q : bool` — `imp` applied to `p` and `q`.
pub(crate) fn hol_imp(p: Term, q: Term) -> Term {
    Term::app(Term::app(defs::imp(), p), q)
}

/// HOL `p ∧ q : bool`.
pub(crate) fn hol_and(p: Term, q: Term) -> Term {
    Term::app(Term::app(defs::and(), p), q)
}

/// HOL `p ∨ q : bool`.
pub(crate) fn hol_or(p: Term, q: Term) -> Term {
    Term::app(Term::app(defs::or(), p), q)
}

/// HOL `¬ p : bool` — `not` applied to `p`.
pub(crate) fn hol_not(p: Term) -> Term {
    Term::app(defs::not(), p)
}

/// HOL `∃x:α. body[x]` — `exists[α] (λx:α. body[Bound 0])`.
pub(crate) fn hol_exists(hint: &str, alpha: Type, body: Term) -> Term {
    let closed = close(&body, hint);
    let lambda = Term::abs(alpha.clone(), closed);
    Term::app(defs::exists(alpha), lambda)
}

/// HOL `∀` at `(α → bool) → bool` — the `forall` spec at `α`.
pub(crate) fn forall_at(alpha: Type) -> Term {
    defs::forall(alpha)
}

/// HOL `∀x:α. body[x]` — `forall[α] (λx:α. body[Bound 0])`. The free
/// variable `Free(hint, α)` in `body` is closed into `Bound(0)`.
pub(crate) fn hol_forall(hint: &str, alpha: Type, body: Term) -> Term {
    let closed = close(&body, hint);
    let lambda = Term::abs(alpha.clone(), closed);
    Term::app(forall_at(alpha), lambda)
}

/// HOL `=` at `α → α → bool` — the primitive `TermKind::Eq`.
fn eq_at(alpha: Type) -> Term {
    Term::eq_op(alpha)
}

/// HOL `lhs = rhs : bool`, types inferred from `lhs`.
///
/// **Panics** if `lhs` is not well-typed (an open term, an ill-typed
/// application, etc.). Callers in inference-rule paths must
/// pre-validate `lhs.type_of()?` before invoking — see e.g.
/// [`crate::Thm::mk_comb`]. Callers in trusted spec-build paths
/// (`defs/*.rs`'s LazyLock initialisers) construct `lhs` from
/// fully-typed atoms, so the panic is unreachable there.
pub(crate) fn hol_eq(lhs: Term, rhs: Term) -> Term {
    let alpha = lhs.type_of().expect("hol::hol_eq: lhs must be well-typed");
    hol_eq_at(alpha, lhs, rhs)
}

/// HOL `lhs = rhs : bool` with the element type `alpha` supplied by the
/// caller — no `type_of` walk. Use this in inference-rule paths that
/// already know `alpha` (e.g. it can be read straight off an input
/// theorem's `Eq(alpha)` node). The result is still fully re-validated by
/// [`crate::Thm`]'s `build`, so a wrong `alpha` is rejected, never
/// trusted — this is purely a way to avoid recomputing what we already
/// know.
pub(crate) fn hol_eq_at(alpha: Type, lhs: Term, rhs: Term) -> Term {
    Term::app(Term::app(eq_at(alpha), lhs), rhs)
}

/// `λx:α. body[x]` — kernel abstraction that closes the named free
/// var into `Bound(0)` first. Exposed to `defs/` for building
/// predicate lambdas inside `TypeSpec.tm`.
pub(crate) fn pub_abs(hint: &str, alpha: Type, body: Term) -> Term {
    Term::abs(alpha, close(&body, hint))
}

// ============================================================================
// Nat building blocks (used by `defs/nat.rs` selector predicates +
// the `nat_induction` axiom term)
// ============================================================================

/// `0 : nat`.
pub(crate) fn zero() -> Term {
    Term::nat_lit(Nat::zero())
}

/// `succ : nat → nat` — the user-facing `defs::nat_succ` TermSpec
/// constant. Closed forms reduce via `builtins::reduce_spec`. Used by
/// `defs/nat.rs` selector predicates and by [`crate::Thm::nat_induct`].
pub(crate) fn succ_fn() -> Term {
    crate::defs::nat_succ()
}

/// `pred : nat → nat` — saturating predecessor, the `defs::nat_pred`
/// TermSpec. Exposed for `defs/nat.rs` selector-predicate construction.
pub(crate) fn pred_fn() -> Term {
    crate::defs::nat_pred()
}
