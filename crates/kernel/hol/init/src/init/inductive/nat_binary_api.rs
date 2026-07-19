//! Double/successor construction backend for the logic-agnostic Nat API.
//!
//! [`DoubleSuccNat`] deliberately remains a distinct backend from
//! [`NativeHol`](super::hol::NativeHol): natural literals are assembled from
//! `zero`, [`crate::init::nat_binary::double`], and successor instead of the
//! kernel's nonzero `Nat` leaf.
//!
//! This is a representation stress test, not yet full leaf elimination. Both
//! backends currently share the native HOL `Type`, `Term`, theorem, and error
//! carriers; `zero`, arithmetic, order, and the proved Peano laws still lower
//! to today's native theory. A later leaf-elimination backend can replace
//! those carriers and interpretations while consumers generic over the
//! `covalence-logic-api` capabilities remain unchanged.
//!
//! `nat_bits_iso` was also audited for this adapter. Its proved
//! `nat_of_bits ∘ nat_to_bits = id` supplies a useful representation morphism,
//! but it does not yet make `list bool` a standalone Nat backend: arithmetic,
//! order, constructor freeness, and the complete Nat law surface have not been
//! transported to that carrier. This backend therefore uses the proved
//! double/successor term representation and makes no stronger claim.
//!
//! @covalence-api-impl {"api":"A0002","name":"DoubleSuccNat","representation":"logarithmic-depth double/successor terms over native HOL carriers"}

use covalence_core::{Error, Result, Term, Type};
use covalence_hol_eval::EvalThm as Thm;
use covalence_logic_api::{
    Logic,
    nat::{
        NatAdditiveLaws, NatArithmetic, NatFreeness, NatMultiplicativeLaws, NatOrder,
        NatRecursionLaws, NatSyntax,
    },
};

use crate::init::{nat, nat_binary};

/// Nat terms whose nonzero literals use the binary double/successor encoding.
#[derive(Clone, Copy, Debug, Default)]
pub struct DoubleSuccNat;

impl Logic for DoubleSuccNat {
    type Kind = ();
    type Type = Type;
    type Term = Term;
    type Thm = Thm;
    type Error = Error;
}

impl NatSyntax for DoubleSuccNat {
    fn nat_type(&self) -> Type {
        Type::nat()
    }

    fn nat_zero(&self) -> Term {
        nat::zero()
    }

    fn nat_succ(&self, n: Term) -> Result<Term> {
        Ok(Term::app(nat::nat_succ(), n))
    }

    fn nat_literal(&self, n: u64) -> Term {
        fn encode(n: u64) -> Term {
            if n == 0 {
                return nat::zero();
            }
            let prefix = encode(n / 2);
            if n % 2 == 0 {
                nat_binary::bit0(prefix)
            } else {
                nat_binary::bit1(prefix)
            }
        }

        encode(n)
    }
}

impl NatArithmetic for DoubleSuccNat {
    fn nat_add(&self, a: Term, b: Term) -> Result<Term> {
        Ok(Term::app(Term::app(nat::nat_add(), a), b))
    }

    fn nat_multiply(&self, a: Term, b: Term) -> Result<Term> {
        Ok(Term::app(Term::app(nat::nat_mul(), a), b))
    }
}

impl NatOrder for DoubleSuccNat {
    fn nat_less_than(&self, a: Term, b: Term) -> Result<Term> {
        Ok(Term::app(Term::app(nat::nat_lt(), a), b))
    }

    fn nat_less_equal(&self, a: Term, b: Term) -> Result<Term> {
        Ok(Term::app(Term::app(nat::nat_le(), a), b))
    }
}

impl NatFreeness for DoubleSuccNat {
    fn nat_successor_injective(&self) -> Result<Thm> {
        Ok(nat::succ_inj())
    }

    fn nat_zero_not_successor(&self) -> Result<Thm> {
        Ok(nat::zero_ne_succ())
    }
}

impl NatRecursionLaws for DoubleSuccNat {
    fn nat_add_base(&self) -> Result<Thm> {
        Ok(nat::add_base())
    }

    fn nat_add_step(&self) -> Result<Thm> {
        Ok(nat::add_step())
    }

    fn nat_multiply_base(&self) -> Result<Thm> {
        Ok(nat::mul_base())
    }

    fn nat_multiply_step(&self) -> Result<Thm> {
        Ok(nat::mul_step())
    }
}

impl NatAdditiveLaws for DoubleSuccNat {
    fn nat_add_zero(&self) -> Result<Thm> {
        Ok(nat::add_zero())
    }

    fn nat_add_successor_right(&self) -> Result<Thm> {
        Ok(nat::add_succ_r())
    }

    fn nat_add_commutative(&self) -> Result<Thm> {
        Ok(nat::add_comm())
    }

    fn nat_add_associative(&self) -> Result<Thm> {
        Ok(nat::add_assoc())
    }

    fn nat_add_cancel_right(&self) -> Result<Thm> {
        Ok(nat::add_cancel())
    }
}

impl NatMultiplicativeLaws for DoubleSuccNat {
    fn nat_multiply_zero(&self) -> Result<Thm> {
        Ok(nat::mul_zero())
    }

    fn nat_multiply_successor_right(&self) -> Result<Thm> {
        Ok(nat::mul_succ_r())
    }

    fn nat_multiply_commutative(&self) -> Result<Thm> {
        Ok(nat::mul_comm())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_logic_api::nat::{NatAdditiveLaws, NatArithmetic, NatOrder, NatSyntax};

    use super::super::hol::NativeHol;

    /// One consumer, compiled unchanged for either representation backend.
    fn generic_consumer<N>(
        backend: &N,
    ) -> std::result::Result<(N::Term, N::Term, N::Term, N::Thm), N::Error>
    where
        N: NatArithmetic + NatOrder + NatAdditiveLaws,
    {
        let one = backend.nat_literal(1);
        let two = backend.nat_add(one.clone(), one.clone())?;
        let one_lt_two = backend.nat_less_than(backend.nat_literal(1), two.clone())?;
        let add_commutative = backend.nat_add_commutative()?;
        Ok((one, two, one_lt_two, add_commutative))
    }

    #[test]
    fn generic_consumer_accepts_leaf_and_double_successor_backends() {
        let native = generic_consumer(&NativeHol).unwrap();
        let binary = generic_consumer(&DoubleSuccNat).unwrap();

        for term in [&native.0, &native.1, &binary.0, &binary.1] {
            assert_eq!(term.type_of().unwrap(), Type::nat());
        }
        for proposition in [&native.2, &binary.2] {
            assert!(proposition.type_of().unwrap().is_bool());
        }
        assert_eq!(native.3.concl(), binary.3.concl());
    }

    #[test]
    fn literals_are_binary_double_successor_terms_not_native_nonzero_leaves() {
        let native_five = NativeHol.nat_literal(5);
        let binary_five = DoubleSuccNat.nat_literal(5);
        let expected =
            nat_binary::bit1(nat_binary::bit0(nat_binary::bit1(DoubleSuccNat.nat_zero())));

        assert_eq!(binary_five, expected);
        assert_ne!(binary_five, native_five);
        assert_eq!(binary_five.type_of().unwrap(), Type::nat());
    }
}
