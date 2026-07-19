//! Shared native-theory capabilities for Nat representation adapters.

macro_rules! impl_native_nat_theory {
    ($backend:ty) => {
        impl covalence_logic_api::Logic for $backend {
            type Kind = ();
            type Type = covalence_core::Type;
            type Term = covalence_core::Term;
            type Thm = covalence_hol_eval::EvalThm;
            type Error = covalence_core::Error;
        }

        impl covalence_logic_api::nat::NatArithmetic for $backend {
            fn nat_add(
                &self,
                a: covalence_core::Term,
                b: covalence_core::Term,
            ) -> covalence_core::Result<covalence_core::Term> {
                Ok(covalence_core::Term::app(
                    covalence_core::Term::app(crate::init::nat::nat_add(), a),
                    b,
                ))
            }

            fn nat_multiply(
                &self,
                a: covalence_core::Term,
                b: covalence_core::Term,
            ) -> covalence_core::Result<covalence_core::Term> {
                Ok(covalence_core::Term::app(
                    covalence_core::Term::app(crate::init::nat::nat_mul(), a),
                    b,
                ))
            }
        }

        impl covalence_logic_api::nat::NatOrder for $backend {
            fn nat_less_than(
                &self,
                a: covalence_core::Term,
                b: covalence_core::Term,
            ) -> covalence_core::Result<covalence_core::Term> {
                Ok(covalence_core::Term::app(
                    covalence_core::Term::app(crate::init::nat::nat_lt(), a),
                    b,
                ))
            }

            fn nat_less_equal(
                &self,
                a: covalence_core::Term,
                b: covalence_core::Term,
            ) -> covalence_core::Result<covalence_core::Term> {
                Ok(covalence_core::Term::app(
                    covalence_core::Term::app(crate::init::nat::nat_le(), a),
                    b,
                ))
            }
        }

        impl covalence_logic_api::nat::NatFreeness for $backend {
            fn nat_successor_injective(
                &self,
            ) -> covalence_core::Result<covalence_hol_eval::EvalThm> {
                Ok(crate::init::nat::succ_inj())
            }

            fn nat_zero_not_successor(
                &self,
            ) -> covalence_core::Result<covalence_hol_eval::EvalThm> {
                Ok(crate::init::nat::zero_ne_succ())
            }
        }

        impl covalence_logic_api::nat::NatRecursionLaws for $backend {
            fn nat_add_base(&self) -> covalence_core::Result<covalence_hol_eval::EvalThm> {
                Ok(crate::init::nat::add_base())
            }

            fn nat_add_step(&self) -> covalence_core::Result<covalence_hol_eval::EvalThm> {
                Ok(crate::init::nat::add_step())
            }

            fn nat_multiply_base(&self) -> covalence_core::Result<covalence_hol_eval::EvalThm> {
                Ok(crate::init::nat::mul_base())
            }

            fn nat_multiply_step(&self) -> covalence_core::Result<covalence_hol_eval::EvalThm> {
                Ok(crate::init::nat::mul_step())
            }
        }

        impl covalence_logic_api::nat::NatAdditiveLaws for $backend {
            fn nat_add_zero(&self) -> covalence_core::Result<covalence_hol_eval::EvalThm> {
                Ok(crate::init::nat::add_zero())
            }

            fn nat_add_successor_right(
                &self,
            ) -> covalence_core::Result<covalence_hol_eval::EvalThm> {
                Ok(crate::init::nat::add_succ_r())
            }

            fn nat_add_commutative(&self) -> covalence_core::Result<covalence_hol_eval::EvalThm> {
                Ok(crate::init::nat::add_comm())
            }

            fn nat_add_associative(&self) -> covalence_core::Result<covalence_hol_eval::EvalThm> {
                Ok(crate::init::nat::add_assoc())
            }

            fn nat_add_cancel_right(&self) -> covalence_core::Result<covalence_hol_eval::EvalThm> {
                Ok(crate::init::nat::add_cancel())
            }
        }

        impl covalence_logic_api::nat::NatMultiplicativeLaws for $backend {
            fn nat_multiply_zero(&self) -> covalence_core::Result<covalence_hol_eval::EvalThm> {
                Ok(crate::init::nat::mul_zero())
            }

            fn nat_multiply_successor_right(
                &self,
            ) -> covalence_core::Result<covalence_hol_eval::EvalThm> {
                Ok(crate::init::nat::mul_succ_r())
            }

            fn nat_multiply_commutative(
                &self,
            ) -> covalence_core::Result<covalence_hol_eval::EvalThm> {
                Ok(crate::init::nat::mul_comm())
            }
        }
    };
}

pub(super) use impl_native_nat_theory;
