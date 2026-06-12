//! Foundational HOL axioms about Pure's primitive `int` type.
//!
//! Unlike `nat` (which has a single-direction recursor `natrec` so
//! every arithmetic op is `op ≡ natrec base step n`), `int` does not
//! admit a single primitive-recursion combinator that uniformly
//! defines all of `+`, `-`, `*`, and unary `-`. The natural
//! definitional layout for `int` instead leans on the universal
//! property of `Z` as the free commutative ring on one generator:
//! the eight ring axioms (additive identity / commutativity /
//! associativity / inverse + multiplicative commutativity /
//! associativity / distributivity) collectively *characterise* the
//! operations up to isomorphism.
//!
//! Today this module postulates those ring axioms directly. A
//! future refactor will replace them with a finer definitional
//! layer (likely: `int_of_nat` + `int_neg` as the canonical
//! generators, with operations defined by case analysis on
//! `sign(x)` and `nat_of_int(|x|)`); the ring laws then become
//! derived theorems. The `LazyLock<Thm>` surface here stays stable
//! across that swap.
//!
//! See [`crate::nat_axioms`] for the cleanly-definitional sibling.

use std::sync::LazyLock;

use covalence_core::{defs, Term, Thm, Type};

use crate::HolLightCtx;

fn ctx() -> HolLightCtx {
    HolLightCtx::new()
}

fn int_ty() -> Type {
    Type::int()
}

fn zero() -> Term {
    Term::int_lit(covalence_types::Int::zero())
}

fn neg(t: Term) -> Term {
    Term::app(defs::int_neg(), t)
}

fn add(a: Term, b: Term) -> Term {
    Term::app(Term::app(defs::int_add(), a), b)
}

fn mul(a: Term, b: Term) -> Term {
    Term::app(Term::app(defs::int_mul(), a), b)
}

fn assume_hol(body: Term) -> Thm {
        Thm::assume(body).expect("int_axioms: Thm::assume on a closed Trueprop cannot fail")
}

// ============================================================================
// Bidirectional induction (bona-fide kernel axiom)
// ============================================================================

/// `⊢ ∀P:int→bool. (∀n:nat. P (int_of_nat n)) ∧ (∀n:nat. P (-(int_of_nat n)))
///                ⟹ ∀z:int. P z` — bidirectional integer induction.
///
/// Derivable from `Thm::nat_induction` once `int` becomes a
/// genuinely derived TypeSpec with a constructive case-split
/// (positive / negative on the `int := signed2 nat` carrier).
/// Until that derivation lands, postulated via `Thm::assume`.
pub fn int_induction() -> Thm {
    let pred_ty = Type::fun(int_ty(), Type::bool());
    let p = Term::free("P", pred_ty.clone());
    let nat = Type::nat();
    let int_of_nat = defs::nat_to_int();

    let n_pos = Term::free("n", nat.clone());
    let p_pos = Term::app(p.clone(), Term::app(int_of_nat.clone(), n_pos));
    let positive = ctx().mk_forall("n", nat.clone(), p_pos);

    let n_neg = Term::free("n", nat.clone());
    let p_neg = Term::app(p.clone(), neg(Term::app(int_of_nat, n_neg)));
    let negative = ctx().mk_forall("n", nat, p_neg);

    let antecedent = ctx().mk_and(positive, negative);

    let z = Term::free("z", int_ty());
    let p_z = Term::app(p.clone(), z);
    let consequent = ctx().mk_forall("z", int_ty(), p_z);

    let body = ctx().mk_imp(antecedent, consequent);
    let outer = ctx().mk_forall("P", pred_ty, body);
    assume_hol(outer)
}

// ============================================================================
// Ring characterisation — currently postulated as the definitional
// layer (see module-level docs); to be replaced with derivations
// from a `int_of_nat` + `int_neg` case-analysis decomposition.
// ============================================================================

/// `⊢ ∀n:int. n + 0 = n`.
pub fn int_add_zero_r() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let n = Term::free("n", int_ty());
        let eq = ctx
            .mk_eq(add(n.clone(), zero()), n)
            .expect("int_add_zero_r: mk_eq");
        let body = ctx.mk_forall("n", int_ty(), eq);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀m n:int. m + n = n + m`.
pub fn int_add_comm() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let m = Term::free("m", int_ty());
        let n = Term::free("n", int_ty());
        let eq = ctx
            .mk_eq(add(m.clone(), n.clone()), add(n, m))
            .expect("int_add_comm: mk_eq");
        let inner = ctx.mk_forall("n", int_ty(), eq);
        let outer = ctx.mk_forall("m", int_ty(), inner);
        assume_hol(outer)
    });
    AX.clone()
}

/// `⊢ ∀a b c. (a + b) + c = a + (b + c)`.
pub fn int_add_assoc() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let a = Term::free("a", int_ty());
        let b = Term::free("b", int_ty());
        let c = Term::free("c", int_ty());
        let lhs = add(add(a.clone(), b.clone()), c.clone());
        let rhs = add(a, add(b, c));
        let eq = ctx.mk_eq(lhs, rhs).expect("int_add_assoc: mk_eq");
        let inner1 = ctx.mk_forall("c", int_ty(), eq);
        let inner2 = ctx.mk_forall("b", int_ty(), inner1);
        let outer = ctx.mk_forall("a", int_ty(), inner2);
        assume_hol(outer)
    });
    AX.clone()
}

/// `⊢ ∀n:int. n + (- n) = 0` — additive inverse.
pub fn int_add_neg_r() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let n = Term::free("n", int_ty());
        let eq = ctx
            .mk_eq(add(n.clone(), neg(n)), zero())
            .expect("int_add_neg_r: mk_eq");
        let body = ctx.mk_forall("n", int_ty(), eq);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀m n. m * n = n * m`.
pub fn int_mul_comm() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let m = Term::free("m", int_ty());
        let n = Term::free("n", int_ty());
        let eq = ctx
            .mk_eq(mul(m.clone(), n.clone()), mul(n, m))
            .expect("int_mul_comm: mk_eq");
        let inner = ctx.mk_forall("n", int_ty(), eq);
        let outer = ctx.mk_forall("m", int_ty(), inner);
        assume_hol(outer)
    });
    AX.clone()
}

/// `⊢ ∀a b c. (a * b) * c = a * (b * c)`.
pub fn int_mul_assoc() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let a = Term::free("a", int_ty());
        let b = Term::free("b", int_ty());
        let c = Term::free("c", int_ty());
        let lhs = mul(mul(a.clone(), b.clone()), c.clone());
        let rhs = mul(a, mul(b, c));
        let eq = ctx.mk_eq(lhs, rhs).expect("int_mul_assoc: mk_eq");
        let inner1 = ctx.mk_forall("c", int_ty(), eq);
        let inner2 = ctx.mk_forall("b", int_ty(), inner1);
        let outer = ctx.mk_forall("a", int_ty(), inner2);
        assume_hol(outer)
    });
    AX.clone()
}

/// `⊢ ∀a b c. a * (b + c) = a*b + a*c` — distributivity.
pub fn int_mul_add_distrib_l() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let a = Term::free("a", int_ty());
        let b = Term::free("b", int_ty());
        let c = Term::free("c", int_ty());
        let lhs = mul(a.clone(), add(b.clone(), c.clone()));
        let rhs = add(mul(a.clone(), b), mul(a, c));
        let eq = ctx
            .mk_eq(lhs, rhs)
            .expect("int_mul_add_distrib_l: mk_eq");
        let inner1 = ctx.mk_forall("c", int_ty(), eq);
        let inner2 = ctx.mk_forall("b", int_ty(), inner1);
        let outer = ctx.mk_forall("a", int_ty(), inner2);
        assume_hol(outer)
    });
    AX.clone()
}

/// `⊢ ∀n:int. - (- n) = n`.
pub fn int_neg_involutive() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let n = Term::free("n", int_ty());
        let eq = ctx
            .mk_eq(neg(neg(n.clone())), n)
            .expect("int_neg_involutive: mk_eq");
        let body = ctx.mk_forall("n", int_ty(), eq);
        assume_hol(body)
    });
    AX.clone()
}

// ============================================================================
// Nat ↔ Int bridge
// ============================================================================

/// `⊢ ∀n:nat. natToInt n + 0 = natToInt n` (a sample fact connecting
/// nat embedding to int arithmetic — the basic embedding morphism
/// laws follow from this + nat_axioms.).
///
/// More foundationally: `natToInt` is a ring-monomorphism. We
/// postulate the most-used facts.
pub fn nat_to_int_add() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let nat_ty = Type::nat();
        let n = Term::free("n", nat_ty.clone());
        let m = Term::free("m", nat_ty.clone());
        let nat_add = Term::app(
            Term::app(defs::nat_add(), m.clone()),
            n.clone(),
        );
        let to_int = |t: Term| Term::app(defs::nat_to_int(), t);
        // ⊢ ∀m n. natToInt (m + n) = natToInt m + natToInt n
        let lhs = to_int(nat_add);
        let rhs = add(to_int(m), to_int(n));
        let eq = ctx.mk_eq(lhs, rhs).expect("nat_to_int_add: mk_eq");
        let inner = ctx.mk_forall("n", nat_ty.clone(), eq);
        let outer = ctx.mk_forall("m", nat_ty, inner);
        assume_hol(outer)
    });
    AX.clone()
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn check(ax: Thm) {
        assert!(ax.concl().type_of().unwrap().is_bool());
        assert_eq!(ax.hyps().len(), 1);
        assert_eq!(ax.hyps().iter().next().unwrap(), ax.concl());
    }

    #[test]
    fn ring_axioms_well_formed() {
        check(int_add_zero_r());
        check(int_add_comm());
        check(int_add_assoc());
        check(int_add_neg_r());
        check(int_mul_comm());
        check(int_mul_assoc());
        check(int_mul_add_distrib_l());
        check(int_neg_involutive());
        check(nat_to_int_add());
    }
}
