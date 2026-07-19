//! Logic-agnostic capabilities for mathematical integers.
//!
//! These traits parallel the natural-number capability family without
//! choosing a quotient, sign/magnitude, difference-of-naturals, host, or
//! Native HOL representation.
//!
//! @covalence-api {"id":"A0021","title":"Mathematical integers","status":"experimental","dependsOn":["A0001","A0002"]}

use covalence_logic_api::Logic;

/// Integer carrier and closed literals.
pub trait IntSyntax: Logic {
    fn int_type(&self) -> Self::Type;
    fn int_literal(&self, value: i128) -> Self::Term;
}

/// Integer ring operations.
pub trait IntArithmetic: IntSyntax {
    fn int_add(&self, left: Self::Term, right: Self::Term) -> Result<Self::Term, Self::Error>;
    fn int_multiply(&self, left: Self::Term, right: Self::Term) -> Result<Self::Term, Self::Error>;
    fn int_negate(&self, value: Self::Term) -> Result<Self::Term, Self::Error>;
    fn int_subtract(&self, left: Self::Term, right: Self::Term) -> Result<Self::Term, Self::Error>;
}

/// Integer order propositions.
pub trait IntOrder: IntSyntax {
    fn int_less_than(&self, left: Self::Term, right: Self::Term)
    -> Result<Self::Term, Self::Error>;
    fn int_less_equal(
        &self,
        left: Self::Term,
        right: Self::Term,
    ) -> Result<Self::Term, Self::Error>;
}

/// Supplied additive-group laws.
pub trait IntAdditiveLaws: IntArithmetic {
    fn int_add_commutative(&self) -> Result<Self::Thm, Self::Error>;
    fn int_add_associative(&self) -> Result<Self::Thm, Self::Error>;
    fn int_add_zero(&self) -> Result<Self::Thm, Self::Error>;
    fn int_add_inverse(&self) -> Result<Self::Thm, Self::Error>;
    fn int_subtract_definition(&self) -> Result<Self::Thm, Self::Error>;
}

/// Supplied multiplicative and distributive laws.
pub trait IntMultiplicativeLaws: IntArithmetic {
    fn int_multiply_commutative(&self) -> Result<Self::Thm, Self::Error>;
    fn int_multiply_associative(&self) -> Result<Self::Thm, Self::Error>;
    fn int_multiply_one(&self) -> Result<Self::Thm, Self::Error>;
    fn int_multiply_zero(&self) -> Result<Self::Thm, Self::Error>;
    fn int_distributive(&self) -> Result<Self::Thm, Self::Error>;
}

/// Supplied linear ordered-ring laws.
pub trait IntOrderedRingLaws: IntArithmetic + IntOrder {
    fn int_less_irreflexive(&self) -> Result<Self::Thm, Self::Error>;
    fn int_less_transitive(&self) -> Result<Self::Thm, Self::Error>;
    fn int_less_trichotomy(&self) -> Result<Self::Thm, Self::Error>;
    fn int_less_equal_definition(&self) -> Result<Self::Thm, Self::Error>;
    fn int_less_add_monotone(&self) -> Result<Self::Thm, Self::Error>;
    fn int_less_multiply_positive(&self) -> Result<Self::Thm, Self::Error>;
    fn int_less_successor(&self) -> Result<Self::Thm, Self::Error>;
}

pub trait IntLaws: IntAdditiveLaws + IntMultiplicativeLaws + IntOrderedRingLaws {}

impl<T> IntLaws for T where T: IntAdditiveLaws + IntMultiplicativeLaws + IntOrderedRingLaws {}

/// Optional equality decision for closed integer terms.
pub trait IntDecidableEquality: IntSyntax {
    fn decide_int_equal(
        &self,
        left: Self::Term,
        right: Self::Term,
    ) -> Result<Self::Thm, Self::Error>;
}

/// Optional normalization of a closed integer term to a literal.
pub trait IntNormalization: IntSyntax {
    fn normalize_int(&self, term: Self::Term) -> Result<Self::Thm, Self::Error>;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Debug, PartialEq)]
    enum Term {
        Int(i128),
    }

    #[derive(Clone, Debug)]
    struct Reference;

    #[derive(Debug)]
    struct Error;

    impl core::fmt::Display for Error {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            f.write_str("reference integer error")
        }
    }

    impl core::error::Error for Error {}

    impl Logic for Reference {
        type Kind = ();
        type Type = &'static str;
        type Term = Term;
        type Thm = ();
        type Error = Error;
    }

    impl IntSyntax for Reference {
        fn int_type(&self) -> Self::Type {
            "int"
        }

        fn int_literal(&self, value: i128) -> Self::Term {
            Term::Int(value)
        }
    }

    #[test]
    fn syntax_does_not_choose_an_integer_representation() {
        let backend = Reference;
        assert_eq!(backend.int_type(), "int");
        assert_eq!(backend.int_literal(-42), Term::Int(-42));
    }
}
