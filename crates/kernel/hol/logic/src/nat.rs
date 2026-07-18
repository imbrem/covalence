//! Logic-agnostic capabilities for natural-number theories.
//!
//! These traits describe syntax and supplied laws over [`Logic`](crate::Logic)
//! carriers. They do not prescribe a representation, computation strategy, or
//! trusted implementation. Consumers should require only the capabilities they
//! use; decision and normalization procedures are optional extensions.
//!
//! @covalence-api {"id":"A0002","title":"Natural numbers","status":"experimental","dependsOn":["A0001"]}

use crate::Logic;

/// The natural-number type and its primitive constructors.
pub trait NatSyntax: Logic {
    /// The object-language type of natural numbers.
    fn nat_type(&self) -> Self::Type;
    /// `0 : nat`.
    fn nat_zero(&self) -> Self::Term;
    /// `S n`.
    fn nat_succ(&self, n: Self::Term) -> Result<Self::Term, Self::Error>;
    /// The numeral `n : nat`.
    fn nat_literal(&self, n: u64) -> Self::Term;
}

/// Natural-number arithmetic term constructors.
pub trait NatArithmetic: NatSyntax {
    /// `a + b`.
    fn nat_add(&self, a: Self::Term, b: Self::Term) -> Result<Self::Term, Self::Error>;
    /// `a * b`.
    fn nat_multiply(&self, a: Self::Term, b: Self::Term) -> Result<Self::Term, Self::Error>;
}

/// Natural-number order term constructors.
pub trait NatOrder: NatSyntax {
    /// `a < b`.
    fn nat_less_than(&self, a: Self::Term, b: Self::Term) -> Result<Self::Term, Self::Error>;
    /// `a ≤ b`.
    fn nat_less_equal(&self, a: Self::Term, b: Self::Term) -> Result<Self::Term, Self::Error>;
}

/// Supplied proofs that zero and successor are free constructors.
pub trait NatFreeness: NatSyntax {
    /// `⊢ ∀m n. (S m = S n) ⟹ (m = n)`.
    fn nat_successor_injective(&self) -> Result<Self::Thm, Self::Error>;
    /// `⊢ ∀n. ¬(0 = S n)`.
    fn nat_zero_not_successor(&self) -> Result<Self::Thm, Self::Error>;
}

/// Supplied defining recursion equations for addition and multiplication.
pub trait NatRecursionLaws: NatArithmetic {
    /// `⊢ ∀b. 0 + b = b`.
    fn nat_add_base(&self) -> Result<Self::Thm, Self::Error>;
    /// `⊢ ∀a b. (S a) + b = S (a + b)`.
    fn nat_add_step(&self) -> Result<Self::Thm, Self::Error>;
    /// `⊢ ∀b. 0 * b = 0`.
    fn nat_multiply_base(&self) -> Result<Self::Thm, Self::Error>;
    /// `⊢ ∀a b. (S a) * b = b + a * b`.
    fn nat_multiply_step(&self) -> Result<Self::Thm, Self::Error>;
}

/// Supplied derived additive laws.
pub trait NatAdditiveLaws: NatArithmetic {
    fn nat_add_zero(&self) -> Result<Self::Thm, Self::Error>;
    fn nat_add_successor_right(&self) -> Result<Self::Thm, Self::Error>;
    fn nat_add_commutative(&self) -> Result<Self::Thm, Self::Error>;
    fn nat_add_associative(&self) -> Result<Self::Thm, Self::Error>;
    fn nat_add_cancel_right(&self) -> Result<Self::Thm, Self::Error>;
}

/// Supplied derived multiplicative laws.
pub trait NatMultiplicativeLaws: NatArithmetic {
    fn nat_multiply_zero(&self) -> Result<Self::Thm, Self::Error>;
    fn nat_multiply_successor_right(&self) -> Result<Self::Thm, Self::Error>;
    fn nat_multiply_commutative(&self) -> Result<Self::Thm, Self::Error>;
}

/// Complete proof-law bundle currently offered by the native HOL adapter.
pub trait NatLaws:
    NatFreeness + NatRecursionLaws + NatAdditiveLaws + NatMultiplicativeLaws
{
}

impl<T> NatLaws for T where
    T: NatFreeness + NatRecursionLaws + NatAdditiveLaws + NatMultiplicativeLaws
{
}

/// Optional equality decision procedure for closed natural-number terms.
pub trait NatEqDecision: NatSyntax {
    /// Prove either `a = b` or its negation.
    fn decide_nat_equal(&self, a: Self::Term, b: Self::Term) -> Result<Self::Thm, Self::Error>;
}

/// Optional normalization procedure for closed natural-number terms.
pub trait NatNormalization: NatSyntax {
    /// Prove that `term` equals a numeral.
    fn normalize_nat(&self, term: Self::Term) -> Result<Self::Thm, Self::Error>;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Debug, PartialEq)]
    enum Term {
        Zero,
        Succ(Box<Term>),
    }

    #[derive(Clone, Debug)]
    struct Theory;

    #[derive(Debug)]
    struct Error;

    impl core::fmt::Display for Error {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            f.write_str("test error")
        }
    }

    impl core::error::Error for Error {}

    impl Logic for Theory {
        type Kind = ();
        type Type = &'static str;
        type Term = Term;
        type Thm = &'static str;
        type Error = Error;
    }

    impl NatSyntax for Theory {
        fn nat_type(&self) -> Self::Type {
            "nat"
        }

        fn nat_zero(&self) -> Self::Term {
            Term::Zero
        }

        fn nat_succ(&self, n: Self::Term) -> Result<Self::Term, Self::Error> {
            Ok(Term::Succ(Box::new(n)))
        }

        fn nat_literal(&self, n: u64) -> Self::Term {
            (0..n).fold(Term::Zero, |term, _| Term::Succ(Box::new(term)))
        }
    }

    #[test]
    fn syntax_uses_logic_carriers_without_a_hol_dependency() {
        let theory = Theory;
        assert_eq!(theory.nat_type(), "nat");
        assert_eq!(
            theory.nat_succ(theory.nat_zero()).unwrap(),
            theory.nat_literal(1)
        );
    }
}
