//! HOL term constructors used by the kernel's inference rules and
//! by the single kernel axiom ([`crate::Thm::nat_induction`]).
//!
//! Everything here is pure term-building over `TermKind::HolOp`,
//! `TermKind::Bool`, and `TermKind::Nat` atoms. No `Thm` machinery
//! is touched. The `pub(crate)` exports are consumed by `thm.rs`
//! (the HOL-Light primitive + derived inference rules need
//! `hol_eq` / `hol_imp` / `hol_forall` to build their conclusions)
//! and by `defs/*.rs`'s spec carriers (which need `pub_abs` and the
//! `zero` / `succ_fn` / `pred_fn` building blocks).

use std::sync::LazyLock;

use covalence_types::Nat;

use crate::defs;
use crate::subst::close;
use crate::term::{Term, Type};

// ============================================================================
// Bool, HOL connective constructors
// ============================================================================
//
// `=` is the primitive `TermKind::Eq`; every connective below is the
// defined constant from `crate::defs::logic` (a `Spec` leaf). The
// `hol_*` builders just spell the application chains.

/// The HOL formula type — `bool`.
fn bool_ty() -> Type {
    Type::bool()
}

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

/// HOL `∃x:α. body[x]` — `exists[α] (λx:α. body[Bound 0])`.
pub(crate) fn hol_exists(hint: &str, alpha: Type, body: Term) -> Term {
    let closed = close(&body, hint);
    let lambda = Term::abs(hint, alpha.clone(), closed);
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
    let lambda = Term::abs(hint, alpha.clone(), closed);
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
    Term::app(Term::app(eq_at(alpha), lhs), rhs)
}

/// `λx:α. body[x]` — kernel abstraction that closes the named free
/// var into `Bound(0)` first. Exposed to `defs/` for building
/// predicate lambdas inside `TypeSpec.tm`.
pub(crate) fn pub_abs(hint: &str, alpha: Type, body: Term) -> Term {
    Term::abs(hint, alpha, close(&body, hint))
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
/// constant. Closed forms reduce via `builtins::reduce_spec`.
pub(crate) fn succ_fn() -> Term {
    crate::defs::nat_succ()
}

/// `succ n : nat`.
fn succ(n: Term) -> Term {
    Term::app(succ_fn(), n)
}

/// `pred : nat → nat` — saturating predecessor, the `defs::nat_pred`
/// TermSpec. Exposed for `defs/nat.rs` selector-predicate construction.
pub(crate) fn pred_fn() -> Term {
    crate::defs::nat_pred()
}

// ============================================================================
// The single kernel axiom — Peano induction on `nat`
// ============================================================================
//
// Cached once at module-load time. Consumed by `Thm::nat_induction`,
// the only non-computational axiom in the TCB.

static NAT_INDUCTION_TERM: LazyLock<Term> = LazyLock::new(|| {
    // ⊢ ∀P:nat→bool. P 0 ∧ (∀n:nat. P n ⟹ P (succ n)) ⟹ ∀n:nat. P n
    let nat = Type::nat();
    let pred_ty = Type::fun(nat.clone(), bool_ty());
    let p = Term::free("P", pred_ty.clone());

    let p_zero = Term::app(p.clone(), zero());

    let n = Term::free("n", nat.clone());
    let p_n = Term::app(p.clone(), n.clone());
    let p_succ_n = Term::app(p.clone(), succ(n));
    let step_body = hol_imp(p_n, p_succ_n);
    let step = hol_forall("n", nat.clone(), step_body);

    let antecedent = hol_and(p_zero, step);

    let n2 = Term::free("n", nat.clone());
    let p_n2 = Term::app(p.clone(), n2);
    let consequent = hol_forall("n", nat.clone(), p_n2);

    let imp = hol_imp(antecedent, consequent);
    hol_forall("P", pred_ty, imp)
});

/// Conclusion of [`crate::Thm::nat_induction`]:
/// `⊢ ∀P:nat→bool. P 0 ∧ (∀n. P n ⟹ P (succ n)) ⟹ ∀n. P n`.
pub(crate) fn nat_induction_term() -> Term {
    NAT_INDUCTION_TERM.clone()
}
