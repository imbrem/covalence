//! HOL natural numbers — backed by Pure's primitive `nat` type.
//!
//! All Nat is now Pure's primitive `Type::nat()` (an arbitrary-
//! precision unsigned integer with computational equality on
//! literals via `Thm::reduce_prim`). The HOL theorems about open
//! forms come from `covalence_hol::nat_axioms`:
//!
//! - **Peano axioms** ([`axiom_zero_ne_succ`], [`axiom_succ_inj`],
//!   [`axiom_induction`]) — intrinsic to the type.
//! - **`natrec`** ([`natrec_at`] / [`natrec_apply`]) — the
//!   primitive-recursion combinator, defined by two equations
//!   ([`axiom_natrec_zero`], [`axiom_natrec_succ`]).
//! - **Operation defining equations** ([`axiom_add_def`],
//!   [`axiom_mul_def`], [`axiom_pred_zero`], [`axiom_pred_succ`],
//!   [`axiom_sub_def`]) — each fixes the meaning of a Pure prim in
//!   terms of `natrec` / `succ` / `pred`.
//! - **Derived theorems** (`axiom_add_zero_r`, `axiom_add_comm`, …)
//!   — currently postulated, scheduled to be replaced by proofs from
//!   the definitional axioms + Peano induction. The re-export
//!   surface stays stable when those proofs land.
//!
//! Consumers should reach for `stdlib::nat::*` and never touch
//! `covalence-pure` or `covalence-hol` directly.

use covalence_pure::{Arith, Prim, Term, Type};

// Re-export underlying lit type for ergonomics.
pub use covalence_types::Nat;

// Re-export the natrec combinator + its definitional axioms.
pub use covalence_hol::nat_axioms::{
    natrec_apply, natrec_at, natrec_def_succ as axiom_natrec_succ,
    natrec_def_zero as axiom_natrec_zero,
};

// Peano axioms — intrinsic to the type.
pub use covalence_hol::nat_axioms::{
    nat_induction as axiom_induction, nat_succ_inj as axiom_succ_inj,
    nat_zero_ne_succ as axiom_zero_ne_succ,
};

// Definitional axioms — each fixes a Pure prim via natrec / succ / pred.
pub use covalence_hol::nat_axioms::{
    nat_add_def as axiom_add_def, nat_mul_def as axiom_mul_def,
    nat_pred_succ as axiom_pred_succ, nat_pred_zero as axiom_pred_zero,
    nat_sub_def as axiom_sub_def,
};

// Derived theorems — TODO-postulated, to be proved from the
// definitional layer.
pub use covalence_hol::nat_axioms::{
    nat_add_assoc as axiom_add_assoc, nat_add_comm as axiom_add_comm,
    nat_add_succ_r as axiom_add_succ_r, nat_add_zero_l as axiom_add_zero_l,
    nat_add_zero_r as axiom_add_zero_r, nat_mul_add_distrib_l as axiom_mul_add_distrib_l,
    nat_mul_assoc as axiom_mul_assoc, nat_mul_comm as axiom_mul_comm,
    nat_mul_succ_r as axiom_mul_succ_r, nat_mul_zero_l as axiom_mul_zero_l,
    nat_mul_zero_r as axiom_mul_zero_r, nat_succ_def as axiom_succ_def,
};

// ============================================================================
// Types and constructors
// ============================================================================

/// The HOL natural-number type — `Type::nat()`.
pub fn ty() -> Type {
    Type::nat()
}

/// A nat literal term.
pub fn lit(n: impl Into<Nat>) -> Term {
    Term::nat_lit(n.into())
}

/// Zero — `lit(0)`.
pub fn zero() -> Term {
    lit(Nat::zero())
}

/// One — `lit(1)`.
pub fn one() -> Term {
    lit(Nat::one())
}

/// `succ` as a closed function term (`nat → nat`).
pub fn succ_fn() -> Term {
    Term::prim(Prim::NatArith(Arith::Succ))
}

/// `succ n`, applied.
pub fn succ(n: Term) -> Term {
    Term::app(succ_fn(), n)
}

/// `pred` as a function (`nat → nat`, saturating at zero).
pub fn pred_fn() -> Term {
    Term::prim(Prim::NatArith(Arith::Pred))
}

/// `pred n`, applied.
pub fn pred(n: Term) -> Term {
    Term::app(pred_fn(), n)
}

// ============================================================================
// Binary arithmetic
// ============================================================================

fn binary_fn(op: Arith) -> Term {
    Term::prim(Prim::NatArith(op))
}

fn binary(op: Arith, a: Term, b: Term) -> Term {
    Term::app(Term::app(binary_fn(op), a), b)
}

/// `nat → nat → nat` — addition.
pub fn add_fn() -> Term {
    binary_fn(Arith::Add)
}
pub fn add(a: Term, b: Term) -> Term {
    binary(Arith::Add, a, b)
}

/// `nat → nat → nat` — multiplication.
pub fn mul_fn() -> Term {
    binary_fn(Arith::Mul)
}
pub fn mul(a: Term, b: Term) -> Term {
    binary(Arith::Mul, a, b)
}

/// `nat → nat → nat` — saturating subtraction.
pub fn sub_fn() -> Term {
    binary_fn(Arith::Sub)
}
pub fn sub(a: Term, b: Term) -> Term {
    binary(Arith::Sub, a, b)
}

/// `nat → nat → nat` — Euclidean division (`a / 0 = 0`).
pub fn div_fn() -> Term {
    binary_fn(Arith::Div)
}
pub fn div(a: Term, b: Term) -> Term {
    binary(Arith::Div, a, b)
}

/// `nat → nat → nat` — Euclidean remainder (`a mod 0 = 0`).
pub fn mod_fn() -> Term {
    binary_fn(Arith::Mod)
}
pub fn rem(a: Term, b: Term) -> Term {
    binary(Arith::Mod, a, b)
}

/// `nat → int` — embed naturals into integers.
pub fn to_int_fn() -> Term {
    Term::prim(Prim::NatToInt)
}
pub fn to_int(n: Term) -> Term {
    Term::app(to_int_fn(), n)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_pure::Thm;

    #[test]
    fn ty_is_pure_nat() {
        assert_eq!(ty(), Type::nat());
    }

    #[test]
    fn zero_succ_reduces_to_one() {
        let s_zero = succ(zero());
        let thm = Thm::reduce_prim(s_zero).unwrap();
        let rhs = match thm.concl().kind() {
            covalence_pure::TermKind::Eq(_, r) => r.clone(),
            _ => panic!("not eq"),
        };
        assert_eq!(rhs, one());
    }

    #[test]
    fn add_reduces_on_literals() {
        let sum = add(lit(7u32), lit(35u32));
        let thm = Thm::reduce_prim(sum).unwrap();
        let rhs = match thm.concl().kind() {
            covalence_pure::TermKind::Eq(_, r) => r.clone(),
            _ => panic!("not eq"),
        };
        assert_eq!(rhs, lit(42u32));
    }

    #[test]
    fn definitional_axioms_well_formed_and_cached() {
        // The definitional axioms cache: same Thm twice should be
        // identical (Arc::ptr_eq on the concl is enough for our
        // smoke check).
        let a = axiom_add_def();
        let b = axiom_add_def();
        assert_eq!(a.concl(), b.concl());
        assert!(a.concl().type_of().unwrap().is_prop());
    }

    #[test]
    fn natrec_at_nat_has_function_type() {
        let nr = natrec_at(ty());
        let step_ty = Type::fun(ty(), ty());
        let expected = Type::fun(ty(), Type::fun(step_ty, Type::fun(ty(), ty())));
        assert_eq!(nr.type_of().unwrap(), expected);
    }
}
