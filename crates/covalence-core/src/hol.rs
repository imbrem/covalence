//! HOL term constructors used by core's bona-fide axioms.
//!
//! These build the standard HOL forms (`∀`, `∧`, `⟹`, `Trueprop`,
//! `succ`, `0`, `Eq`, …) directly from kernel atoms (`TermKind::Bool`,
//! `TermKind::HolOp`, `TermKind::Nat`, `TermKind::Prim`). The kernel's
//! axiom rules ([`crate::Thm::nat_induction`] et al.) call into here
//! to produce the canonical conclusions.
//!
//! Nothing in this module touches `Thm` — everything is pure term
//! building. The `pub(crate)` exports below are consumed only by
//! `thm.rs`'s axiom methods.

use covalence_types::Nat;

use crate::term::{Arith, HolOp, Prim, Term, Type};

/// HOL `T` and `F` are kernel literals; this helper gives us the
/// canonical bool type.
fn bool_ty() -> Type {
    Type::bool()
}

/// `Trueprop` constant at `bool → prop`.
fn trueprop_op() -> Term {
    Term::hol_op(HolOp::Trueprop, Type::fun(bool_ty(), Type::prop()))
}

/// `Trueprop p` — wrap a bool term as a Pure prop.
fn trueprop(p: Term) -> Term {
    Term::app(trueprop_op(), p)
}

/// HOL `==>` at `bool → bool → bool`.
fn hol_imp_op() -> Term {
    let b = bool_ty();
    Term::hol_op(HolOp::Imp, Type::fun(b.clone(), Type::fun(b.clone(), b)))
}

/// HOL `p ⟹ q : bool`.
fn hol_imp(p: Term, q: Term) -> Term {
    Term::app(Term::app(hol_imp_op(), p), q)
}

/// HOL `/\` at `bool → bool → bool`.
fn hol_and_op() -> Term {
    let b = bool_ty();
    Term::hol_op(HolOp::And, Type::fun(b.clone(), Type::fun(b.clone(), b)))
}

/// HOL `p ∧ q : bool`.
fn hol_and(p: Term, q: Term) -> Term {
    Term::app(Term::app(hol_and_op(), p), q)
}

/// HOL `∀` at `(α → bool) → bool`.
fn forall_at(alpha: Type) -> Term {
    let pred = Type::fun(alpha, bool_ty());
    Term::hol_op(HolOp::Forall, Type::fun(pred, bool_ty()))
}

/// HOL `∀x:α. body` — `Forall (λx:α. body)`.
fn hol_forall(hint: &str, alpha: Type, body: Term) -> Term {
    let lambda = Term::abs(hint, alpha.clone(), body);
    Term::app(forall_at(alpha), lambda)
}

/// HOL `=` at `α → α → bool`.
fn eq_at(alpha: Type) -> Term {
    Term::hol_op(
        HolOp::Eq,
        Type::fun(alpha.clone(), Type::fun(alpha, bool_ty())),
    )
}

/// HOL `lhs = rhs : bool`, types inferred from `lhs`.
fn hol_eq(lhs: Term, rhs: Term) -> Term {
    let alpha = lhs.type_of().expect("hol::hol_eq: lhs typed");
    Term::app(Term::app(eq_at(alpha), lhs), rhs)
}

/// `0 : nat`.
fn zero() -> Term {
    Term::nat_lit(Nat::zero())
}

/// `succ : nat → nat`.
fn succ_fn() -> Term {
    Term::prim(Prim::NatArith(Arith::Succ))
}

/// `succ n : nat`.
fn succ(n: Term) -> Term {
    Term::app(succ_fn(), n)
}

// ============================================================================
// Public-to-crate axiom-conclusion constructors
// ============================================================================

/// Build the conclusion of [`crate::Thm::nat_induction`]:
/// `Trueprop (∀P:nat→bool. P 0 ∧ (∀n. P n ⟹ P (succ n)) ⟹ ∀n. P n)`.
pub(crate) fn nat_induction_term() -> Term {
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
    let body = hol_forall("P", pred_ty, imp);
    trueprop(body)
}

/// Build the conclusion of [`crate::Thm::eq_reflection`]:
/// `⋀x y:'a. Trueprop (x = y) ≡ (x ≡ y)`.
pub(crate) fn eq_reflection_term() -> Term {
    let alpha = Type::tfree("a");
    let x = Term::free("x", alpha.clone());
    let y = Term::free("y", alpha.clone());

    let lhs = trueprop(hol_eq(x.clone(), y.clone()));
    let rhs = Term::eq(x, y);
    let body = Term::eq(lhs, rhs);

    let inner = Term::all("y", alpha.clone(), body);
    Term::all("x", alpha, inner)
}

/// Build the conclusion of [`crate::Thm::forall_reflection`]:
/// `⋀P:'a→bool. (⋀x:'a. Trueprop (P x)) ≡ Trueprop (∀x:'a. P x)`.
pub(crate) fn forall_reflection_term() -> Term {
    let alpha = Type::tfree("a");
    let pred_ty = Type::fun(alpha.clone(), bool_ty());
    let p = Term::free("P", pred_ty.clone());

    let x_inner = Term::free("x", alpha.clone());
    let p_x_inner = Term::app(p.clone(), x_inner);
    let left = Term::all("x", alpha.clone(), trueprop(p_x_inner));

    let x_outer = Term::free("x", alpha.clone());
    let p_x_outer = Term::app(p.clone(), x_outer);
    let right = trueprop(hol_forall("x", alpha, p_x_outer));

    let body = Term::eq(left, right);
    Term::all("P", pred_ty, body)
}

/// Build the conclusion of [`crate::Thm::imp_reflection`]:
/// `⋀P Q:bool. (Trueprop P ⟹ Trueprop Q) ≡ Trueprop (P ⟹ Q)`.
pub(crate) fn imp_reflection_term() -> Term {
    let p = Term::free("p", bool_ty());
    let q = Term::free("q", bool_ty());

    let left = Term::imp(trueprop(p.clone()), trueprop(q.clone()));
    let right = trueprop(hol_imp(p, q));

    let body = Term::eq(left, right);
    let inner = Term::all("q", bool_ty(), body);
    Term::all("p", bool_ty(), inner)
}
