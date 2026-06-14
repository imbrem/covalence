//! HOL integers — backed by the kernel's primitive `int` type.
//!
//! Same architecture as `stdlib::nat`: the kernel provides the type
//! and closed-form computation; the open-form HOL ring axioms come
//! from `crate::int_axioms` and are re-exported here.

use covalence_core::{defs, Term, Type};

pub use covalence_types::Int;

pub use crate::int_axioms::{
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

/// `succ : int → int` — TermSpec constant.
pub fn succ_fn() -> Term {
    defs::int_succ()
}
pub fn succ(n: Term) -> Term {
    Term::app(succ_fn(), n)
}

/// `pred : int → int` — TermSpec constant.
pub fn pred_fn() -> Term {
    defs::int_pred()
}
pub fn pred(n: Term) -> Term {
    Term::app(pred_fn(), n)
}

/// `neg : int → int` — TermSpec constant.
pub fn neg_fn() -> Term {
    defs::int_neg()
}
pub fn neg(n: Term) -> Term {
    Term::app(neg_fn(), n)
}

fn binary(f: Term, a: Term, b: Term) -> Term {
    Term::app(Term::app(f, a), b)
}

pub fn add_fn() -> Term {
    defs::int_add()
}
pub fn add(a: Term, b: Term) -> Term {
    binary(add_fn(), a, b)
}
pub fn mul_fn() -> Term {
    defs::int_mul()
}
pub fn mul(a: Term, b: Term) -> Term {
    binary(mul_fn(), a, b)
}
pub fn sub_fn() -> Term {
    defs::int_sub()
}
pub fn sub(a: Term, b: Term) -> Term {
    binary(sub_fn(), a, b)
}
pub fn div_fn() -> Term {
    defs::int_div()
}
pub fn div(a: Term, b: Term) -> Term {
    binary(div_fn(), a, b)
}
pub fn mod_fn() -> Term {
    defs::int_mod()
}
pub fn rem(a: Term, b: Term) -> Term {
    binary(mod_fn(), a, b)
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_core::{TermKind, Thm};

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
        let rhs = {
            let TermKind::App(eq_lhs_app, rhs) = thm.concl().kind() else { panic!() };
            let TermKind::App(_, _) = eq_lhs_app.kind() else { panic!() };
            rhs.clone()
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
            assert!(ax.concl().type_of().unwrap().is_bool());
        }
    }
}
