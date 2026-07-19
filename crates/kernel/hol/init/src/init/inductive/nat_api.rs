//! Native HOL adapter for the logic-agnostic natural-number capabilities.
//!
//! @covalence-api-impl {"api":"A0002","name":"NativeHol","representation":"HOL natural-number leaves and definitions"}

use covalence_core::{Result, Term, Type};
use covalence_logic_api::nat::{
    NatAdditiveLaws, NatArithmetic, NatFreeness, NatMultiplicativeLaws, NatOrder, NatRecursionLaws,
    NatSyntax,
};

use super::hol::{Hol, NativeHol};
use crate::init::nat;

impl NatSyntax for NativeHol {
    fn nat_type(&self) -> Type {
        Type::nat()
    }

    fn nat_zero(&self) -> Term {
        covalence_hol_eval::mk_nat(covalence_types::Nat::zero())
    }

    fn nat_succ(&self, n: Term) -> Result<Term> {
        Hol::app(self, nat::nat_succ(), n)
    }

    fn nat_literal(&self, n: u64) -> Term {
        covalence_hol_eval::mk_nat(covalence_types::Nat::from(n))
    }
}

impl NatArithmetic for NativeHol {
    fn nat_add(&self, a: Term, b: Term) -> Result<Term> {
        Hol::app(self, Hol::app(self, nat::nat_add(), a)?, b)
    }

    fn nat_multiply(&self, a: Term, b: Term) -> Result<Term> {
        Hol::app(self, Hol::app(self, nat::nat_mul(), a)?, b)
    }
}

impl NatOrder for NativeHol {
    fn nat_less_than(&self, a: Term, b: Term) -> Result<Term> {
        Hol::app(self, Hol::app(self, nat::nat_lt(), a)?, b)
    }

    fn nat_less_equal(&self, a: Term, b: Term) -> Result<Term> {
        Hol::app(self, Hol::app(self, nat::nat_le(), a)?, b)
    }
}

impl NatFreeness for NativeHol {
    fn nat_successor_injective(&self) -> Result<Self::Thm> {
        Ok(nat::succ_inj())
    }

    fn nat_zero_not_successor(&self) -> Result<Self::Thm> {
        Ok(nat::zero_ne_succ())
    }
}

impl NatRecursionLaws for NativeHol {
    fn nat_add_base(&self) -> Result<Self::Thm> {
        Ok(nat::add_base())
    }

    fn nat_add_step(&self) -> Result<Self::Thm> {
        Ok(nat::add_step())
    }

    fn nat_multiply_base(&self) -> Result<Self::Thm> {
        Ok(nat::mul_base())
    }

    fn nat_multiply_step(&self) -> Result<Self::Thm> {
        Ok(nat::mul_step())
    }
}

impl NatAdditiveLaws for NativeHol {
    fn nat_add_zero(&self) -> Result<Self::Thm> {
        Ok(nat::add_zero())
    }

    fn nat_add_successor_right(&self) -> Result<Self::Thm> {
        Ok(nat::add_succ_r())
    }

    fn nat_add_commutative(&self) -> Result<Self::Thm> {
        Ok(nat::add_comm())
    }

    fn nat_add_associative(&self) -> Result<Self::Thm> {
        Ok(nat::add_assoc())
    }

    fn nat_add_cancel_right(&self) -> Result<Self::Thm> {
        Ok(nat::add_cancel())
    }
}

impl NatMultiplicativeLaws for NativeHol {
    fn nat_multiply_zero(&self) -> Result<Self::Thm> {
        Ok(nat::mul_zero())
    }

    fn nat_multiply_successor_right(&self) -> Result<Self::Thm> {
        Ok(nat::mul_succ_r())
    }

    fn nat_multiply_commutative(&self) -> Result<Self::Thm> {
        Ok(nat::mul_comm())
    }
}
