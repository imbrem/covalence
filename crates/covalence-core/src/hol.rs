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

use std::sync::LazyLock;

use covalence_types::Nat;

use crate::subst::close;
use crate::term::{Arith, HolOp, Prim, Term, Type};

// ============================================================================
// Term builders for HOL constructs
//
// Each binder helper closes the named free variable into a
// de Bruijn `BoundVar` before wrapping with the binder. The Pure
// kernel's `all_elim` / `beta_conv` rules walk the bound-var
// structure, so failing to close here would make every axiom term
// look "binder-free" at the kernel level.
// ============================================================================

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
pub(crate) fn hol_imp(p: Term, q: Term) -> Term {
    Term::app(Term::app(hol_imp_op(), p), q)
}

/// HOL `~` at `bool → bool`.
fn hol_not_op() -> Term {
    Term::hol_op(HolOp::Not, Type::fun(bool_ty(), bool_ty()))
}

/// HOL `~p : bool`.
fn hol_not(p: Term) -> Term {
    Term::app(hol_not_op(), p)
}

/// HOL `/\` at `bool → bool → bool`.
fn hol_and_op() -> Term {
    let b = bool_ty();
    Term::hol_op(HolOp::And, Type::fun(b.clone(), Type::fun(b.clone(), b)))
}

/// HOL `p ∧ q : bool`.
pub(crate) fn hol_and(p: Term, q: Term) -> Term {
    Term::app(Term::app(hol_and_op(), p), q)
}

/// HOL `\/` at `bool → bool → bool`.
fn hol_or_op() -> Term {
    let b = bool_ty();
    Term::hol_op(HolOp::Or, Type::fun(b.clone(), Type::fun(b.clone(), b)))
}

/// HOL `p ∨ q : bool`.
pub(crate) fn hol_or(p: Term, q: Term) -> Term {
    Term::app(Term::app(hol_or_op(), p), q)
}

/// HOL `∀` at `(α → bool) → bool`.
fn forall_at(alpha: Type) -> Term {
    let pred = Type::fun(alpha, bool_ty());
    Term::hol_op(HolOp::Forall, Type::fun(pred, bool_ty()))
}

/// HOL `∀x:α. body[x]` — `Forall (λx:α. body[Bound 0])`. The free
/// variable `Free(hint, α)` in `body` is closed into `Bound(0)`.
pub(crate) fn hol_forall(hint: &str, alpha: Type, body: Term) -> Term {
    let closed = close(&body, hint);
    let lambda = Term::abs(hint, alpha.clone(), closed);
    Term::app(forall_at(alpha), lambda)
}

/// HOL `∃` at `(α → bool) → bool`.
fn exists_at(alpha: Type) -> Term {
    let pred = Type::fun(alpha, bool_ty());
    Term::hol_op(HolOp::Exists, Type::fun(pred, bool_ty()))
}

/// HOL `∃x:α. body[x]` — `Exists (λx:α. body[Bound 0])`.
pub(crate) fn hol_exists(hint: &str, alpha: Type, body: Term) -> Term {
    let closed = close(&body, hint);
    let lambda = Term::abs(hint, alpha.clone(), closed);
    Term::app(exists_at(alpha), lambda)
}

/// Pure meta-universal `⋀x:α. body[x]` — closes `Free(hint, α)`
/// into `Bound(0)` before wrapping with `Term::all`.
fn pure_all(hint: &str, alpha: Type, body: Term) -> Term {
    Term::all(hint, alpha, close(&body, hint))
}

/// Pure abstraction `λx:α. body[x]` — closes `Free(hint, α)` into
/// `Bound(0)` before wrapping with `Term::abs`. Used for predicate
/// lambdas inside `HolOp(Forall, _)` applications.
fn pure_abs(hint: &str, alpha: Type, body: Term) -> Term {
    Term::abs(hint, alpha, close(&body, hint))
}

/// HOL `=` at `α → α → bool`.
fn eq_at(alpha: Type) -> Term {
    Term::hol_op(
        HolOp::Eq,
        Type::fun(alpha.clone(), Type::fun(alpha, bool_ty())),
    )
}

/// HOL `lhs = rhs : bool`, types inferred from `lhs`.
pub(crate) fn hol_eq(lhs: Term, rhs: Term) -> Term {
    let alpha = lhs.type_of().expect("hol::hol_eq: lhs typed");
    Term::app(Term::app(eq_at(alpha), lhs), rhs)
}

/// `λx:α. body[x]` — kernel abstraction that closes the named free
/// var into `Bound(0)` first. Exposed to `defs/` for building
/// predicate lambdas inside `TypeSpec.tm`.
pub(crate) fn pub_abs(hint: &str, alpha: Type, body: Term) -> Term {
    Term::abs(hint, alpha, close(&body, hint))
}

/// `0 : nat`.
pub(crate) fn zero() -> Term {
    Term::nat_lit(Nat::zero())
}

/// `succ : nat → nat`.
pub(crate) fn succ_fn() -> Term {
    Term::prim(Prim::NatArith(Arith::Succ))
}

/// `succ n : nat`.
fn succ(n: Term) -> Term {
    Term::app(succ_fn(), n)
}

/// `pred : nat → nat`.
fn pred(n: Term) -> Term {
    Term::app(pred_fn(), n)
}

/// `pred : nat → nat` (the curried primitive).
pub(crate) fn pred_fn() -> Term {
    Term::prim(Prim::NatArith(Arith::Pred))
}

fn nat_add_fn() -> Term {
    Term::prim(Prim::NatArith(Arith::Add))
}

fn nat_add(a: Term, b: Term) -> Term {
    Term::app(Term::app(nat_add_fn(), a), b)
}

fn nat_mul_fn() -> Term {
    Term::prim(Prim::NatArith(Arith::Mul))
}

fn nat_mul(a: Term, b: Term) -> Term {
    Term::app(Term::app(nat_mul_fn(), a), b)
}

fn nat_sub_fn() -> Term {
    Term::prim(Prim::NatArith(Arith::Sub))
}

fn nat_sub(a: Term, b: Term) -> Term {
    Term::app(Term::app(nat_sub_fn(), a), b)
}

/// `natrec : β → (β → β) → nat → β` at carrier β. A HOL-level
/// constant (defined in `covalence-hol` via Hilbert's `select`).
/// Referenced by the Pure-prim definitional axioms below.
fn natrec_at(beta: Type) -> Term {
    let step_ty = Type::fun(beta.clone(), beta.clone());
    let ty = Type::fun(
        beta.clone(),
        Type::fun(step_ty, Type::fun(Type::nat(), beta)),
    );
    Term::const_("natrec", ty)
}

fn natrec(base: Term, step: Term, n: Term) -> Term {
    let beta = base.type_of().expect("natrec: base typed");
    Term::app(Term::app(Term::app(natrec_at(beta), base), step), n)
}

/// `int_of_nat : nat → int` — the canonical embedding `n ↦ +n`.
fn int_of_nat_fn() -> Term {
    Term::prim(Prim::NatToInt)
}

fn int_of_nat(n: Term) -> Term {
    Term::app(int_of_nat_fn(), n)
}

/// `(-_) : int → int` — integer negation.
fn int_neg_fn() -> Term {
    Term::prim(Prim::IntNeg)
}

fn int_neg(z: Term) -> Term {
    Term::app(int_neg_fn(), z)
}

// ============================================================================
// Cached axiom-conclusion terms
// ============================================================================
//
// Each axiom term is built once and then shared as a cheap `Arc`
// clone. The kernel rules in `thm.rs` just `Thm::build` over a
// cloned `Term` — `Thm::build`'s validation cost is a single
// `type_of_in` walk, which is fine to pay on every axiom call.

static NAT_INDUCTION_TERM: LazyLock<Term> = LazyLock::new(|| {
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
});

static NAT_INDUCTION_PURE_TERM: LazyLock<Term> = LazyLock::new(|| {
    // ⋀P:nat→bool.
    //   Trueprop (P 0) ⟹
    //   (⋀n:nat. Trueprop (P n) ⟹ Trueprop (P (succ n))) ⟹
    //   (⋀n:nat. Trueprop (P n))
    let nat = Type::nat();
    let pred_ty = Type::fun(nat.clone(), bool_ty());
    let p = Term::free("P", pred_ty.clone());

    let base = trueprop(Term::app(p.clone(), zero()));

    let n_step = Term::free("n", nat.clone());
    let step_inner = Term::imp(
        trueprop(Term::app(p.clone(), n_step.clone())),
        trueprop(Term::app(p.clone(), succ(n_step))),
    );
    let step = pure_all("n", nat.clone(), step_inner);

    let n_concl = Term::free("n", nat.clone());
    let concl_inner = trueprop(Term::app(p.clone(), n_concl));
    let concl = pure_all("n", nat.clone(), concl_inner);

    let chain = Term::imp(base, Term::imp(step, concl));
    pure_all("P", pred_ty, chain)
});

static EQ_REFLECTION_TERM: LazyLock<Term> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    let x = Term::free("x", alpha.clone());
    let y = Term::free("y", alpha.clone());

    let lhs = trueprop(hol_eq(x.clone(), y.clone()));
    let rhs = Term::eq(x, y);
    let body = Term::eq(lhs, rhs);

    let inner = pure_all("y", alpha.clone(), body);
    pure_all("x", alpha, inner)
});

static FORALL_REFLECTION_TERM: LazyLock<Term> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    let pred_ty = Type::fun(alpha.clone(), bool_ty());
    let p = Term::free("P", pred_ty.clone());

    let x_inner = Term::free("x", alpha.clone());
    let p_x_inner = Term::app(p.clone(), x_inner);
    let left = pure_all("x", alpha.clone(), trueprop(p_x_inner));

    let x_outer = Term::free("x", alpha.clone());
    let p_x_outer = Term::app(p.clone(), x_outer);
    let right = trueprop(hol_forall("x", alpha, p_x_outer));

    let body = Term::eq(left, right);
    pure_all("P", pred_ty, body)
});

static IMP_REFLECTION_TERM: LazyLock<Term> = LazyLock::new(|| {
    let p = Term::free("p", bool_ty());
    let q = Term::free("q", bool_ty());

    let left = Term::imp(trueprop(p.clone()), trueprop(q.clone()));
    let right = trueprop(hol_imp(p, q));

    let body = Term::eq(left, right);
    let inner = pure_all("q", bool_ty(), body);
    pure_all("p", bool_ty(), inner)
});

// ---- Definitional axioms: pred ----

static PRED_ZERO_TERM: LazyLock<Term> = LazyLock::new(|| {
    // Trueprop (pred 0 = 0)
    trueprop(hol_eq(pred(zero()), zero()))
});

static PRED_SUCC_TERM: LazyLock<Term> = LazyLock::new(|| {
    // ⋀n:nat. Trueprop (pred (succ n) = n)
    let n = Term::free("n", Type::nat());
    let eq = hol_eq(pred(succ(n.clone())), n);
    pure_all("n", Type::nat(), trueprop(eq))
});

// ---- Definitional axioms: defs::nat_rec ----
//
// natRec is a polymorphic TermSpec whose `tm` field carries the
// uniqueness selector predicate (Hilbert ε form). These two axioms
// expose its primitive-recursion equations directly so downstream
// proofs (in `proofs.rs` and beyond) can use them without rebuilding
// the choice argument.

static NAT_REC_ZERO_TERM: LazyLock<Term> = LazyLock::new(|| {
    // ⋀z:'a. ⋀f:nat→'a→'a. Trueprop (natRec[α] z f 0 = z)
    let alpha = Type::tfree("a");
    let f_ty = Type::fun(Type::nat(), Type::fun(alpha.clone(), alpha.clone()));
    let z = Term::free("z", alpha.clone());
    let f = Term::free("f", f_ty.clone());

    let nat_rec_at_alpha = crate::defs::nat_rec(alpha.clone());
    let lhs = Term::app(
        Term::app(Term::app(nat_rec_at_alpha, z.clone()), f.clone()),
        zero(),
    );
    let eq = hol_eq(lhs, z);
    pure_all("z", alpha, pure_all("f", f_ty, trueprop(eq)))
});

static NAT_REC_SUCC_TERM: LazyLock<Term> = LazyLock::new(|| {
    // ⋀z:'a. ⋀f:nat→'a→'a. ⋀n:nat.
    //   Trueprop (natRec[α] z f (succ n) = f n (natRec[α] z f n))
    let alpha = Type::tfree("a");
    let f_ty = Type::fun(Type::nat(), Type::fun(alpha.clone(), alpha.clone()));
    let z = Term::free("z", alpha.clone());
    let f = Term::free("f", f_ty.clone());
    let n = Term::free("n", Type::nat());

    let nat_rec_at_alpha = crate::defs::nat_rec(alpha.clone());
    let nat_rec_zf = Term::app(Term::app(nat_rec_at_alpha, z.clone()), f.clone());

    let lhs = Term::app(nat_rec_zf.clone(), succ(n.clone()));
    let rec_n = Term::app(nat_rec_zf, n.clone());
    let rhs = Term::app(Term::app(f.clone(), n.clone()), rec_n);

    let eq = hol_eq(lhs, rhs);
    pure_all(
        "z",
        alpha,
        pure_all("f", f_ty, pure_all("n", Type::nat(), trueprop(eq))),
    )
});

pub(crate) fn nat_rec_zero_term() -> Term {
    NAT_REC_ZERO_TERM.clone()
}

pub(crate) fn nat_rec_succ_term() -> Term {
    NAT_REC_SUCC_TERM.clone()
}

// ---- Definitional axioms: defs::nat_le ----

static NAT_LE_REFL_TERM: LazyLock<Term> = LazyLock::new(|| {
    // ⋀n:nat. Trueprop (nat_le n n)
    let n = Term::free("n", Type::nat());
    let body = Term::app(Term::app(crate::defs::nat_le(), n.clone()), n);
    pure_all("n", Type::nat(), trueprop(body))
});

pub(crate) fn nat_le_refl_term() -> Term {
    NAT_LE_REFL_TERM.clone()
}

// ---- Definitional axioms: defs::nat_div ----
//
// nat_div is declared (no body). The three axioms below pin its
// Euclidean recursion. Sound because the standard mathematical
// division uniquely satisfies them.

static NAT_DIV_ZERO_RIGHT_TERM: LazyLock<Term> = LazyLock::new(|| {
    // ⋀n:nat. Trueprop (nat_div n 0 = 0)
    let n = Term::free("n", Type::nat());
    let lhs = Term::app(Term::app(crate::defs::nat_div(), n), zero());
    let eq = hol_eq(lhs, zero());
    pure_all("n", Type::nat(), trueprop(eq))
});

static NAT_DIV_LESS_TERM: LazyLock<Term> = LazyLock::new(|| {
    // ⋀n m:nat. Trueprop (nat_lt n m) ⟹ Trueprop (nat_div n m = 0)
    let n = Term::free("n", Type::nat());
    let m = Term::free("m", Type::nat());
    let n_lt_m = Term::app(Term::app(crate::defs::nat_lt(), n.clone()), m.clone());
    let lhs = Term::app(Term::app(crate::defs::nat_div(), n), m);
    let eq = hol_eq(lhs, zero());
    let body = Term::imp(trueprop(n_lt_m), trueprop(eq));
    pure_all("n", Type::nat(), pure_all("m", Type::nat(), body))
});

static NAT_DIV_RECURSION_TERM: LazyLock<Term> = LazyLock::new(|| {
    // ⋀n m:nat.
    //   Trueprop (nat_lt 0 m)
    //   ⟹ Trueprop (nat_le m n)
    //   ⟹ Trueprop (nat_div n m = succ (nat_div (nat_sub n m) m))
    let n = Term::free("n", Type::nat());
    let m = Term::free("m", Type::nat());

    let zero_lt_m = Term::app(Term::app(crate::defs::nat_lt(), zero()), m.clone());
    let m_le_n = Term::app(Term::app(crate::defs::nat_le(), m.clone()), n.clone());

    let nat_div_nm = Term::app(Term::app(crate::defs::nat_div(), n.clone()), m.clone());
    let n_minus_m = Term::app(Term::app(crate::defs::nat_sub(), n.clone()), m.clone());
    let recursive = Term::app(Term::app(crate::defs::nat_div(), n_minus_m), m.clone());
    let rhs = Term::app(succ_fn(), recursive);
    let conclusion = trueprop(hol_eq(nat_div_nm, rhs));

    let body = Term::imp(trueprop(zero_lt_m), Term::imp(trueprop(m_le_n), conclusion));
    pure_all("n", Type::nat(), pure_all("m", Type::nat(), body))
});

pub(crate) fn nat_div_zero_right_term() -> Term {
    NAT_DIV_ZERO_RIGHT_TERM.clone()
}

pub(crate) fn nat_div_less_term() -> Term {
    NAT_DIV_LESS_TERM.clone()
}

pub(crate) fn nat_div_recursion_term() -> Term {
    NAT_DIV_RECURSION_TERM.clone()
}

// ---- Definitional axioms tying Pure prims to natrec ----
//
// Each equation defines a Pure `Prim::NatArith(_)` operator in
// terms of HOL `natrec`. Sound because the closed-form behaviour
// of these prims (`Thm::reduce_prim`) and the natrec-fold
// behaviour agree at every literal n: both unfold to the same
// value.

static NAT_ADD_DEF_TERM: LazyLock<Term> = LazyLock::new(|| {
    // ⋀m n. Trueprop (m + n = natrec m succ n)
    let m = Term::free("m", Type::nat());
    let n = Term::free("n", Type::nat());
    let lhs = nat_add(m.clone(), n.clone());
    let rhs = natrec(m.clone(), succ_fn(), n.clone());
    let eq = hol_eq(lhs, rhs);
    pure_all("m", Type::nat(), pure_all("n", Type::nat(), trueprop(eq)))
});

static NAT_MUL_DEF_TERM: LazyLock<Term> = LazyLock::new(|| {
    // ⋀m n. Trueprop (m * n = natrec 0 (λx. x + m) n)
    let m = Term::free("m", Type::nat());
    let n = Term::free("n", Type::nat());
    let lhs = nat_mul(m.clone(), n.clone());
    // step = λx:nat. x + m
    let x = Term::free("x", Type::nat());
    let step_body = nat_add(x, m.clone());
    let step = pure_abs("x", Type::nat(), step_body);
    let rhs = natrec(zero(), step, n.clone());
    let eq = hol_eq(lhs, rhs);
    pure_all("m", Type::nat(), pure_all("n", Type::nat(), trueprop(eq)))
});

static NAT_SUB_DEF_TERM: LazyLock<Term> = LazyLock::new(|| {
    // ⋀m n. Trueprop (m - n = natrec m pred n)
    let m = Term::free("m", Type::nat());
    let n = Term::free("n", Type::nat());
    let lhs = nat_sub(m.clone(), n.clone());
    let rhs = natrec(m.clone(), pred_fn(), n.clone());
    let eq = hol_eq(lhs, rhs);
    pure_all("m", Type::nat(), pure_all("n", Type::nat(), trueprop(eq)))
});

// ---- HOL connective definitions ----

static NOT_DEF_TERM: LazyLock<Term> = LazyLock::new(|| {
    // ⋀p:bool. Trueprop (¬p = (p ⟹ F))
    let p = Term::free("p", bool_ty());
    let lhs = hol_not(p.clone());
    let rhs = hol_imp(p, Term::bool_lit(false));
    let eq = hol_eq(lhs, rhs);
    pure_all("p", bool_ty(), trueprop(eq))
});

static AND_INTRO_TERM: LazyLock<Term> = LazyLock::new(|| {
    // ⋀p q:bool. Trueprop p ⟹ Trueprop q ⟹ Trueprop (p ∧ q)
    let p = Term::free("p", bool_ty());
    let q = Term::free("q", bool_ty());
    let chain = Term::imp(
        trueprop(p.clone()),
        Term::imp(trueprop(q.clone()), trueprop(hol_and(p, q))),
    );
    pure_all("p", bool_ty(), pure_all("q", bool_ty(), chain))
});

// ---- Integer induction ----

static INT_INDUCTION_TERM: LazyLock<Term> = LazyLock::new(|| {
    // ⋀P:int→bool.
    //   Trueprop ((∀n:nat. P (int_of_nat n))
    //          ∧ (∀n:nat. P (-(int_of_nat n)))
    //          ⟹ ∀z:int. P z)
    let pred_ty = Type::fun(Type::int(), bool_ty());
    let p = Term::free("P", pred_ty.clone());

    let n_pos = Term::free("n", Type::nat());
    let p_pos = Term::app(p.clone(), int_of_nat(n_pos));
    let positive = hol_forall("n", Type::nat(), p_pos);

    let n_neg = Term::free("n", Type::nat());
    let p_neg = Term::app(p.clone(), int_neg(int_of_nat(n_neg)));
    let negative = hol_forall("n", Type::nat(), p_neg);

    let antecedent = hol_and(positive, negative);

    let z = Term::free("z", Type::int());
    let p_z = Term::app(p.clone(), z);
    let consequent = hol_forall("z", Type::int(), p_z);

    let body = hol_imp(antecedent, consequent);
    pure_all("P", pred_ty, trueprop(body))
});

/// Conclusion of [`crate::Thm::nat_induction`]:
/// `Trueprop (∀P:nat→bool. P 0 ∧ (∀n. P n ⟹ P (succ n)) ⟹ ∀n. P n)`.
pub(crate) fn nat_induction_term() -> Term {
    NAT_INDUCTION_TERM.clone()
}

pub(crate) fn nat_induction_pure_term() -> Term {
    NAT_INDUCTION_PURE_TERM.clone()
}

pub(crate) fn pred_zero_term() -> Term {
    PRED_ZERO_TERM.clone()
}

pub(crate) fn pred_succ_term() -> Term {
    PRED_SUCC_TERM.clone()
}

pub(crate) fn nat_add_def_term() -> Term {
    NAT_ADD_DEF_TERM.clone()
}

pub(crate) fn nat_mul_def_term() -> Term {
    NAT_MUL_DEF_TERM.clone()
}

pub(crate) fn nat_sub_def_term() -> Term {
    NAT_SUB_DEF_TERM.clone()
}

pub(crate) fn int_induction_term() -> Term {
    INT_INDUCTION_TERM.clone()
}

pub(crate) fn not_def_term() -> Term {
    NOT_DEF_TERM.clone()
}

pub(crate) fn and_intro_term() -> Term {
    AND_INTRO_TERM.clone()
}

/// Conclusion of [`crate::Thm::eq_reflection`]:
/// `⋀x y:'a. Trueprop (x = y) ≡ (x ≡ y)`.
pub(crate) fn eq_reflection_term() -> Term {
    EQ_REFLECTION_TERM.clone()
}

/// Conclusion of [`crate::Thm::forall_reflection`]:
/// `⋀P:'a→bool. (⋀x:'a. Trueprop (P x)) ≡ Trueprop (∀x:'a. P x)`.
pub(crate) fn forall_reflection_term() -> Term {
    FORALL_REFLECTION_TERM.clone()
}

/// Conclusion of [`crate::Thm::imp_reflection`]:
/// `⋀P Q:bool. (Trueprop P ⟹ Trueprop Q) ≡ Trueprop (P ⟹ Q)`.
pub(crate) fn imp_reflection_term() -> Term {
    IMP_REFLECTION_TERM.clone()
}
