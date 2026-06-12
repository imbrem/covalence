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
use crate::term::{HolOp, Term, Type};

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

/// HOL `=` at `α → α → bool`.
fn eq_at(alpha: Type) -> Term {
    Term::hol_op(
        HolOp::Eq,
        Type::fun(alpha.clone(), Type::fun(alpha, bool_ty())),
    )
}

/// HOL `lhs = rhs : bool`, types inferred from `lhs`.
///
/// **Panics** if `lhs` is not well-typed (an open term, an ill-typed
/// application, etc.). Callers in inference-rule paths must
/// pre-validate `lhs.type_of()?` before invoking — see e.g.
/// [`crate::Thm::hol_mk_comb`]. Callers in trusted spec-build paths
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

/// `pred n : nat`.
fn pred(n: Term) -> Term {
    Term::app(pred_fn(), n)
}

/// `pred : nat → nat` — saturating predecessor, the `defs::nat_pred`
/// TermSpec.
pub(crate) fn pred_fn() -> Term {
    crate::defs::nat_pred()
}

fn nat_add_fn() -> Term {
    crate::defs::nat_add()
}

fn nat_add(a: Term, b: Term) -> Term {
    Term::app(Term::app(nat_add_fn(), a), b)
}

fn nat_mul_fn() -> Term {
    crate::defs::nat_mul()
}

fn nat_mul(a: Term, b: Term) -> Term {
    Term::app(Term::app(nat_mul_fn(), a), b)
}

fn nat_sub_fn() -> Term {
    crate::defs::nat_sub()
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

/// `int_of_nat : nat → int` — the canonical embedding `n ↦ +n`,
/// via the `defs::nat_to_int` TermSpec.
fn int_of_nat_fn() -> Term {
    crate::defs::nat_to_int()
}

fn int_of_nat(n: Term) -> Term {
    Term::app(int_of_nat_fn(), n)
}

/// `(-_) : int → int` — integer negation, via the `defs::int_neg`
/// TermSpec.
fn int_neg_fn() -> Term {
    crate::defs::int_neg()
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

// ---- Definitional axioms: pred ----

static PRED_ZERO_TERM: LazyLock<Term> = LazyLock::new(|| {
    // ⊢ pred 0 = 0
    hol_eq(pred(zero()), zero())
});

static PRED_SUCC_TERM: LazyLock<Term> = LazyLock::new(|| {
    // ⊢ ∀n:nat. pred (succ n) = n
    let n = Term::free("n", Type::nat());
    let eq = hol_eq(pred(succ(n.clone())), n);
    hol_forall("n", Type::nat(), eq)
});

// ---- Definitional axioms: defs::nat_rec ----
//
// natRec is a polymorphic TermSpec whose `tm` field carries the
// uniqueness selector predicate (Hilbert ε form). These two axioms
// expose its primitive-recursion equations directly so downstream
// proofs (in `proofs.rs` and beyond) can use them without rebuilding
// the choice argument.

static NAT_REC_ZERO_TERM: LazyLock<Term> = LazyLock::new(|| {
    // ⊢ ∀z:'a. ∀f:nat→'a→'a. natRec[α] z f 0 = z
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
    hol_forall("z", alpha, hol_forall("f", f_ty, eq))
});

static NAT_REC_SUCC_TERM: LazyLock<Term> = LazyLock::new(|| {
    // ⊢ ∀z:'a. ∀f:nat→'a→'a. ∀n:nat.
    //     natRec[α] z f (succ n) = f n (natRec[α] z f n)
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
    hol_forall(
        "z",
        alpha,
        hol_forall("f", f_ty, hol_forall("n", Type::nat(), eq)),
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
    // ⊢ ∀n:nat. nat_le n n
    let n = Term::free("n", Type::nat());
    let body = Term::app(Term::app(crate::defs::nat_le(), n.clone()), n);
    hol_forall("n", Type::nat(), body)
});

pub(crate) fn nat_le_refl_term() -> Term {
    NAT_LE_REFL_TERM.clone()
}

// ---- Definitional axioms: defs::int_add (minimal pair) ----
//
// These two axioms uniquely characterise int_add on the
// non-negative range, which is what nat_to_int produces. They're
// stated in terms of the user-facing TermSpec defs::int_add and
// defs::int_succ — no Prim::IntArith references.

static INT_ADD_ZERO_RIGHT_TERM: LazyLock<Term> = LazyLock::new(|| {
    // ⊢ ∀z:int. int_add z 0 = z
    let z = Term::free("z", Type::int());
    let zero_int = crate::defs::int_zero();
    let int_add = crate::defs::int_add();
    let lhs = Term::app(Term::app(int_add, z.clone()), zero_int);
    let eq = hol_eq(lhs, z);
    hol_forall("z", Type::int(), eq)
});

static INT_ADD_SUCC_RIGHT_TERM: LazyLock<Term> = LazyLock::new(|| {
    // ⊢ ∀a b:int. int_add a (intSucc b) = intSucc (int_add a b)
    let a = Term::free("a", Type::int());
    let b = Term::free("b", Type::int());
    let int_succ = crate::defs::int_succ();
    let int_add = crate::defs::int_add();
    let succ_b = Term::app(int_succ.clone(), b.clone());
    let lhs = Term::app(Term::app(int_add.clone(), a.clone()), succ_b);
    let a_plus_b = Term::app(Term::app(int_add, a.clone()), b.clone());
    let rhs = Term::app(int_succ, a_plus_b);
    let eq = hol_eq(lhs, rhs);
    hol_forall("a", Type::int(), hol_forall("b", Type::int(), eq))
});

pub(crate) fn int_add_zero_right_term() -> Term {
    INT_ADD_ZERO_RIGHT_TERM.clone()
}

pub(crate) fn int_add_succ_right_term() -> Term {
    INT_ADD_SUCC_RIGHT_TERM.clone()
}

// ---- Definitional axioms: defs::nat_div ----
//
// nat_div is declared (no body). The three axioms below pin its
// Euclidean recursion. Sound because the standard mathematical
// division uniquely satisfies them.

static NAT_DIV_ZERO_RIGHT_TERM: LazyLock<Term> = LazyLock::new(|| {
    // ⊢ ∀n:nat. nat_div n 0 = 0
    let n = Term::free("n", Type::nat());
    let lhs = Term::app(Term::app(crate::defs::nat_div(), n), zero());
    let eq = hol_eq(lhs, zero());
    hol_forall("n", Type::nat(), eq)
});

static NAT_DIV_LESS_TERM: LazyLock<Term> = LazyLock::new(|| {
    // ⊢ ∀n m:nat. nat_lt n m ⟹ nat_div n m = 0
    let n = Term::free("n", Type::nat());
    let m = Term::free("m", Type::nat());
    let n_lt_m = Term::app(Term::app(crate::defs::nat_lt(), n.clone()), m.clone());
    let lhs = Term::app(Term::app(crate::defs::nat_div(), n), m);
    let eq = hol_eq(lhs, zero());
    let body = hol_imp(n_lt_m, eq);
    hol_forall("n", Type::nat(), hol_forall("m", Type::nat(), body))
});

static NAT_DIV_RECURSION_TERM: LazyLock<Term> = LazyLock::new(|| {
    // ⊢ ∀n m:nat.
    //     nat_lt 0 m ⟹ nat_le m n
    //     ⟹ nat_div n m = succ (nat_div (nat_sub n m) m)
    let n = Term::free("n", Type::nat());
    let m = Term::free("m", Type::nat());

    let zero_lt_m = Term::app(Term::app(crate::defs::nat_lt(), zero()), m.clone());
    let m_le_n = Term::app(Term::app(crate::defs::nat_le(), m.clone()), n.clone());

    let nat_div_nm = Term::app(Term::app(crate::defs::nat_div(), n.clone()), m.clone());
    let n_minus_m = Term::app(Term::app(crate::defs::nat_sub(), n.clone()), m.clone());
    let recursive = Term::app(Term::app(crate::defs::nat_div(), n_minus_m), m.clone());
    let rhs = Term::app(succ_fn(), recursive);
    let conclusion = hol_eq(nat_div_nm, rhs);

    let body = hol_imp(zero_lt_m, hol_imp(m_le_n, conclusion));
    hol_forall("n", Type::nat(), hol_forall("m", Type::nat(), body))
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
    // ⊢ ∀m n. m + n = natrec m succ n
    let m = Term::free("m", Type::nat());
    let n = Term::free("n", Type::nat());
    let lhs = nat_add(m.clone(), n.clone());
    let rhs = natrec(m.clone(), succ_fn(), n.clone());
    let eq = hol_eq(lhs, rhs);
    hol_forall("m", Type::nat(), hol_forall("n", Type::nat(), eq))
});

static NAT_MUL_DEF_TERM: LazyLock<Term> = LazyLock::new(|| {
    // ⊢ ∀m n. m * n = natrec 0 (λx. x + m) n
    let m = Term::free("m", Type::nat());
    let n = Term::free("n", Type::nat());
    let lhs = nat_mul(m.clone(), n.clone());
    // step = λx:nat. x + m
    let x = Term::free("x", Type::nat());
    let step_body = nat_add(x, m.clone());
    let step = pub_abs("x", Type::nat(), step_body);
    let rhs = natrec(zero(), step, n.clone());
    let eq = hol_eq(lhs, rhs);
    hol_forall("m", Type::nat(), hol_forall("n", Type::nat(), eq))
});

static NAT_SUB_DEF_TERM: LazyLock<Term> = LazyLock::new(|| {
    // ⊢ ∀m n. m - n = natrec m pred n
    let m = Term::free("m", Type::nat());
    let n = Term::free("n", Type::nat());
    let lhs = nat_sub(m.clone(), n.clone());
    let rhs = natrec(m.clone(), pred_fn(), n.clone());
    let eq = hol_eq(lhs, rhs);
    hol_forall("m", Type::nat(), hol_forall("n", Type::nat(), eq))
});

// ---- HOL connective definitions ----

static NOT_DEF_TERM: LazyLock<Term> = LazyLock::new(|| {
    // ⊢ ∀p:bool. ¬p = (p ⟹ F)
    let p = Term::free("p", bool_ty());
    let lhs = hol_not(p.clone());
    let rhs = hol_imp(p, Term::bool_lit(false));
    let eq = hol_eq(lhs, rhs);
    hol_forall("p", bool_ty(), eq)
});

static AND_INTRO_TERM: LazyLock<Term> = LazyLock::new(|| {
    // ⊢ ∀p q:bool. p ⟹ q ⟹ p ∧ q
    let p = Term::free("p", bool_ty());
    let q = Term::free("q", bool_ty());
    let chain = hol_imp(p.clone(), hol_imp(q.clone(), hol_and(p, q)));
    hol_forall("p", bool_ty(), hol_forall("q", bool_ty(), chain))
});

// ---- Integer induction ----

static INT_INDUCTION_TERM: LazyLock<Term> = LazyLock::new(|| {
    // ⊢ ∀P:int→bool.
    //     (∀n:nat. P (int_of_nat n))
    //   ∧ (∀n:nat. P (-(int_of_nat n)))
    //   ⟹ ∀z:int. P z
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
    hol_forall("P", pred_ty, body)
});

/// Conclusion of [`crate::Thm::nat_induction`]:
/// `⊢ ∀P:nat→bool. P 0 ∧ (∀n. P n ⟹ P (succ n)) ⟹ ∀n. P n`.
pub(crate) fn nat_induction_term() -> Term {
    NAT_INDUCTION_TERM.clone()
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
