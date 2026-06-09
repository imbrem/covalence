//! HOL integers — backed by Pure's primitive `int` type.
//!
//! Same architecture as `stdlib::nat`: Pure provides the type and
//! closed-form computation; the open-form HOL ring axioms come from
//! `covalence_hol::int_axioms` and are re-exported here.

use covalence_core::{Arith, Prim, Term, Type};

pub use covalence_types::Int;

pub use covalence_hol::int_axioms::{
    int_add_assoc as axiom_add_assoc, int_add_comm as axiom_add_comm,
    int_add_neg_r as axiom_add_neg_r, int_add_zero_r as axiom_add_zero_r,
    int_mul_add_distrib_l as axiom_mul_add_distrib_l, int_mul_assoc as axiom_mul_assoc,
    int_mul_comm as axiom_mul_comm, int_neg_involutive as axiom_neg_involutive,
    nat_to_int_add as axiom_nat_to_int_add,
};

/// The HOL integer type — `Type::int()`.
pub fn ty() -> Type {
    Type::int()
}

/// An int literal term.
pub fn lit(n: impl Into<Int>) -> Term {
    Term::int_lit(n.into())
}

pub fn zero() -> Term {
    lit(Int::zero())
}

pub fn one() -> Term {
    lit(Int::one())
}

/// `succ : int → int`.
pub fn succ_fn() -> Term {
    Term::prim(Prim::IntArith(Arith::Succ))
}
pub fn succ(n: Term) -> Term {
    Term::app(succ_fn(), n)
}

/// `pred : int → int`.
pub fn pred_fn() -> Term {
    Term::prim(Prim::IntArith(Arith::Pred))
}
pub fn pred(n: Term) -> Term {
    Term::app(pred_fn(), n)
}

/// `neg : int → int`.
pub fn neg_fn() -> Term {
    Term::prim(Prim::IntNeg)
}
pub fn neg(n: Term) -> Term {
    Term::app(neg_fn(), n)
}

fn binary_fn(op: Arith) -> Term {
    Term::prim(Prim::IntArith(op))
}
fn binary(op: Arith, a: Term, b: Term) -> Term {
    Term::app(Term::app(binary_fn(op), a), b)
}

pub fn add_fn() -> Term {
    binary_fn(Arith::Add)
}
pub fn add(a: Term, b: Term) -> Term {
    binary(Arith::Add, a, b)
}
pub fn mul_fn() -> Term {
    binary_fn(Arith::Mul)
}
pub fn mul(a: Term, b: Term) -> Term {
    binary(Arith::Mul, a, b)
}
pub fn sub_fn() -> Term {
    binary_fn(Arith::Sub)
}
pub fn sub(a: Term, b: Term) -> Term {
    binary(Arith::Sub, a, b)
}
pub fn div_fn() -> Term {
    binary_fn(Arith::Div)
}
pub fn div(a: Term, b: Term) -> Term {
    binary(Arith::Div, a, b)
}
pub fn mod_fn() -> Term {
    binary_fn(Arith::Mod)
}
pub fn rem(a: Term, b: Term) -> Term {
    binary(Arith::Mod, a, b)
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_core::Thm;

    #[test]
    fn ty_is_pure_int() {
        assert_eq!(ty(), Type::int());
    }

    #[test]
    fn neg_reduces() {
        let n = neg(lit(Int::from_sign_nat(
            covalence_types::Sign::Positive,
            covalence_types::Nat::from_inner(7u32.into()),
        )));
        let thm = Thm::reduce_prim(n).unwrap();
        let rhs = match thm.concl().kind() {
            covalence_core::TermKind::Eq(_, r) => r.clone(),
            _ => panic!(),
        };
        assert_eq!(
            rhs,
            lit(Int::from_sign_nat(
                covalence_types::Sign::Negative,
                covalence_types::Nat::from_inner(7u32.into())
            ))
        );
    }

    #[test]
    fn axioms_well_formed() {
        for ax in [
            axiom_add_zero_r(),
            axiom_add_comm(),
            axiom_add_assoc(),
            axiom_add_neg_r(),
            axiom_mul_comm(),
            axiom_mul_assoc(),
            axiom_mul_add_distrib_l(),
            axiom_neg_involutive(),
            axiom_nat_to_int_add(),
        ] {
            assert!(ax.concl().type_of().unwrap().is_prop());
        }
    }
}
