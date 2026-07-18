//! Relations and relational algebra.
//!
//! [`Arrow`] is the backend-neutral spelling of a Haskell-style `r a b`: it
//! packages an object-language relation together with its domain and codomain.
//! Operations return `Result` because composition and lattice operations may
//! require type checking or proof obligations.  No method promises executable
//! membership or decidable equality.

use crate::Logic;

/// A typed relation `r : A ↔ B`.
#[derive(Clone, Debug, PartialEq)]
pub struct Arrow<Ty, Rel> {
    /// Domain `A`.
    pub domain: Ty,
    /// Codomain `B`.
    pub codomain: Ty,
    /// The backend's representation of `r`.
    pub relation: Rel,
}

impl<Ty, Rel> Arrow<Ty, Rel> {
    /// Construct a typed relation arrow.
    pub const fn new(domain: Ty, codomain: Ty, relation: Rel) -> Self {
        Self {
            domain,
            codomain,
            relation,
        }
    }
}

/// Category structure on typed relation arrows.
pub trait Category: Logic {
    /// Backend representation of a binary relation.
    type Relation: Clone + PartialEq + core::fmt::Debug;

    /// Identity relation on an object.
    fn identity(
        &self,
        object: Self::Type,
    ) -> Result<Arrow<Self::Type, Self::Relation>, Self::Error>;

    /// Relational composition `right ∘ left`.
    fn compose(
        &self,
        left: Arrow<Self::Type, Self::Relation>,
        right: Arrow<Self::Type, Self::Relation>,
    ) -> Result<Arrow<Self::Type, Self::Relation>, Self::Error>;
}

/// Core algebra of binary relations.
pub trait RelationAlgebra: Category {
    /// Empty relation `⊥ : A ↔ B`.
    fn empty(
        &self,
        domain: Self::Type,
        codomain: Self::Type,
    ) -> Result<Arrow<Self::Type, Self::Relation>, Self::Error>;
    /// Universal relation `⊤ : A ↔ B`.
    fn universal(
        &self,
        domain: Self::Type,
        codomain: Self::Type,
    ) -> Result<Arrow<Self::Type, Self::Relation>, Self::Error>;
    /// Converse `r† : B ↔ A`.
    fn converse(
        &self,
        relation: Arrow<Self::Type, Self::Relation>,
    ) -> Result<Arrow<Self::Type, Self::Relation>, Self::Error>;
    /// Union of same-typed relations.
    fn union(
        &self,
        left: Arrow<Self::Type, Self::Relation>,
        right: Arrow<Self::Type, Self::Relation>,
    ) -> Result<Arrow<Self::Type, Self::Relation>, Self::Error>;
    /// Intersection of same-typed relations.
    fn intersection(
        &self,
        left: Arrow<Self::Type, Self::Relation>,
        right: Arrow<Self::Type, Self::Relation>,
    ) -> Result<Arrow<Self::Type, Self::Relation>, Self::Error>;
}

/// Residual operations on relations.
///
/// For `r : A ↔ B`, `s : B ↔ C`, and `t : A ↔ C`, the right residual
/// `t / r : B ↔ C` is the greatest candidate `s` for which `s ∘ r ⊆ t`.
/// Dually, the left residual `s \ t : A ↔ B` is the greatest candidate `r`
/// for which `s ∘ r ⊆ t`.
///
/// This capability deliberately depends only on [`Category`]. A backend can
/// construct residual syntax without implementing the lattice operations in
/// [`RelationAlgebra`] or claiming that arbitrary inclusion is decidable.
pub trait ResidualSyntax: Category {
    /// Construct the right residual `dividend / divisor`.
    ///
    /// Given `dividend : A ↔ C` and `divisor : A ↔ B`, returns a relation
    /// `B ↔ C`.
    fn right_residual(
        &self,
        dividend: Arrow<Self::Type, Self::Relation>,
        divisor: Arrow<Self::Type, Self::Relation>,
    ) -> Result<Arrow<Self::Type, Self::Relation>, Self::Error>;

    /// Construct the left residual `divisor \ dividend`.
    ///
    /// Given `divisor : B ↔ C` and `dividend : A ↔ C`, returns a relation
    /// `A ↔ B`.
    fn left_residual(
        &self,
        divisor: Arrow<Self::Type, Self::Relation>,
        dividend: Arrow<Self::Type, Self::Relation>,
    ) -> Result<Arrow<Self::Type, Self::Relation>, Self::Error>;
}

// TODO(cov:kernel.logic.relation-allegory, major): Add products, coproducts, tabulation, and closure as optional capabilities with law bundles.

/// Proposition syntax for inclusion and extensional equality of relations.
///
/// Constructing a proposition does not prove or decide it.
pub trait RelationJudgmentSyntax: Category {
    /// Construct the proposition `left ⊆ right`.
    fn inclusion_proposition(
        &self,
        left: &Arrow<Self::Type, Self::Relation>,
        right: &Arrow<Self::Type, Self::Relation>,
    ) -> Result<Self::Term, Self::Error>;
    /// Construct the proposition `left = right` extensionally.
    fn relation_equality_proposition(
        &self,
        left: &Arrow<Self::Type, Self::Relation>,
        right: &Arrow<Self::Type, Self::Relation>,
    ) -> Result<Self::Term, Self::Error>;
}

/// Primitive derivation laws for relation inclusion.
///
/// These methods consume only previously proved facts or derive unconditional
/// algebraic laws. They do not claim to solve arbitrary inclusion goals.
pub trait RelationOrderLaws: RelationJudgmentSyntax {
    fn inclusion_reflexivity(
        &self,
        relation: &Arrow<Self::Type, Self::Relation>,
    ) -> Result<Self::Thm, Self::Error>;
    fn inclusion_transitivity(
        &self,
        left_in_middle: Self::Thm,
        middle_in_right: Self::Thm,
    ) -> Result<Self::Thm, Self::Error>;
    fn inclusion_antisymmetry(
        &self,
        left_in_right: Self::Thm,
        right_in_left: Self::Thm,
    ) -> Result<Self::Thm, Self::Error>;
}

/// Proof rules for the defining residual adjunctions.
///
/// Each pair of methods gives both directions of one equivalence:
///
/// - `s ∘ r ⊆ t` iff `s ⊆ t / r`;
/// - `s ∘ r ⊆ t` iff `r ⊆ s \ t`.
///
/// The explicit arrows let a backend check that the supplied theorem proves
/// the expected premise. Methods transform positive evidence; they are not
/// decision procedures and do not mint proofs without an input theorem.
pub trait ResidualLaws: ResidualSyntax + RelationJudgmentSyntax {
    /// Transform a proof of `candidate ∘ divisor ⊆ dividend` into a proof of
    /// `candidate ⊆ dividend / divisor`.
    fn right_residual_intro(
        &self,
        divisor: &Arrow<Self::Type, Self::Relation>,
        candidate: &Arrow<Self::Type, Self::Relation>,
        dividend: &Arrow<Self::Type, Self::Relation>,
        composite_in_dividend: Self::Thm,
    ) -> Result<Self::Thm, Self::Error>;

    /// Transform a proof of `candidate ⊆ dividend / divisor` into a proof of
    /// `candidate ∘ divisor ⊆ dividend`.
    fn right_residual_elim(
        &self,
        divisor: &Arrow<Self::Type, Self::Relation>,
        candidate: &Arrow<Self::Type, Self::Relation>,
        dividend: &Arrow<Self::Type, Self::Relation>,
        candidate_in_residual: Self::Thm,
    ) -> Result<Self::Thm, Self::Error>;

    /// Transform a proof of `candidate ∘ divisor ⊆ dividend` into a proof of
    /// `divisor ⊆ candidate \ dividend`.
    fn left_residual_intro(
        &self,
        divisor: &Arrow<Self::Type, Self::Relation>,
        candidate: &Arrow<Self::Type, Self::Relation>,
        dividend: &Arrow<Self::Type, Self::Relation>,
        composite_in_dividend: Self::Thm,
    ) -> Result<Self::Thm, Self::Error>;

    /// Transform a proof of `divisor ⊆ candidate \ dividend` into a proof of
    /// `candidate ∘ divisor ⊆ dividend`.
    fn left_residual_elim(
        &self,
        divisor: &Arrow<Self::Type, Self::Relation>,
        candidate: &Arrow<Self::Type, Self::Relation>,
        dividend: &Arrow<Self::Type, Self::Relation>,
        divisor_in_residual: Self::Thm,
    ) -> Result<Self::Thm, Self::Error>;
}

/// Check externally supplied positive evidence for a relation judgment.
///
/// Evidence may be a finite enumeration, a solver certificate, or another
/// backend-defined object. Failure to check evidence is not a refutation.
pub trait RelationEvidence: RelationJudgmentSyntax {
    type InclusionEvidence;
    type EqualityEvidence;

    fn check_inclusion(
        &self,
        left: &Arrow<Self::Type, Self::Relation>,
        right: &Arrow<Self::Type, Self::Relation>,
        evidence: Self::InclusionEvidence,
    ) -> Result<Self::Thm, Self::Error>;
    fn check_relation_equality(
        &self,
        left: &Arrow<Self::Type, Self::Relation>,
        right: &Arrow<Self::Type, Self::Relation>,
        evidence: Self::EqualityEvidence,
    ) -> Result<Self::Thm, Self::Error>;
}

/// A proof-producing decision, with proof in either branch.
#[derive(Clone, Debug)]
pub enum Decision<Thm> {
    Holds(Thm),
    DoesNotHold(Thm),
}

/// Optional decision procedure for finite or otherwise decidable relations.
pub trait RelationOrderDecision: RelationJudgmentSyntax {
    fn decide_inclusion(
        &self,
        left: &Arrow<Self::Type, Self::Relation>,
        right: &Arrow<Self::Type, Self::Relation>,
    ) -> Result<Decision<Self::Thm>, Self::Error>;
    fn decide_relation_equality(
        &self,
        left: &Arrow<Self::Type, Self::Relation>,
        right: &Arrow<Self::Type, Self::Relation>,
    ) -> Result<Decision<Self::Thm>, Self::Error>;
}

/// Standard properties which may be requested from a relational backend.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RelationProperty {
    /// `identity ⊆ r`.
    Reflexive,
    /// `r† ⊆ r`.
    Symmetric,
    /// `r ∘ r ⊆ r`.
    Transitive,
    /// Every domain value is related to at least one codomain value.
    Total,
    /// Every domain value is related to at most one codomain value.
    Functional,
    /// Every codomain value has at least one preimage.
    Surjective,
    /// Every codomain value has at most one preimage.
    Injective,
}

/// Proposition syntax for standard relation properties.
pub trait RelationPropertySyntax: Category {
    fn property_proposition(
        &self,
        relation: &Arrow<Self::Type, Self::Relation>,
        property: RelationProperty,
    ) -> Result<Self::Term, Self::Error>;
}

/// Check supplied positive evidence for a standard relation property.
pub trait RelationPropertyEvidence: RelationPropertySyntax {
    type PropertyEvidence;

    fn check_property(
        &self,
        relation: &Arrow<Self::Type, Self::Relation>,
        property: RelationProperty,
        evidence: Self::PropertyEvidence,
    ) -> Result<Self::Thm, Self::Error>;
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::convert::Infallible;

    struct Relations;

    impl Logic for Relations {
        type Kind = ();
        type Type = &'static str;
        type Term = ();
        type Thm = String;
        type Error = Infallible;
    }

    impl Category for Relations {
        type Relation = String;

        fn identity(
            &self,
            object: &'static str,
        ) -> Result<Arrow<&'static str, String>, Infallible> {
            Ok(Arrow::new(object, object, format!("id[{object}]")))
        }

        fn compose(
            &self,
            left: Arrow<&'static str, String>,
            right: Arrow<&'static str, String>,
        ) -> Result<Arrow<&'static str, String>, Infallible> {
            assert_eq!(left.codomain, right.domain);
            Ok(Arrow::new(
                left.domain,
                right.codomain,
                format!("{};{}", left.relation, right.relation),
            ))
        }
    }

    impl RelationJudgmentSyntax for Relations {
        fn inclusion_proposition(
            &self,
            _left: &Arrow<&'static str, String>,
            _right: &Arrow<&'static str, String>,
        ) -> Result<(), Infallible> {
            Ok(())
        }

        fn relation_equality_proposition(
            &self,
            _left: &Arrow<&'static str, String>,
            _right: &Arrow<&'static str, String>,
        ) -> Result<(), Infallible> {
            Ok(())
        }
    }

    impl ResidualSyntax for Relations {
        fn right_residual(
            &self,
            dividend: Arrow<&'static str, String>,
            divisor: Arrow<&'static str, String>,
        ) -> Result<Arrow<&'static str, String>, Infallible> {
            assert_eq!(dividend.domain, divisor.domain);
            Ok(Arrow::new(
                divisor.codomain,
                dividend.codomain,
                format!("{}/{}", dividend.relation, divisor.relation),
            ))
        }

        fn left_residual(
            &self,
            divisor: Arrow<&'static str, String>,
            dividend: Arrow<&'static str, String>,
        ) -> Result<Arrow<&'static str, String>, Infallible> {
            assert_eq!(divisor.codomain, dividend.codomain);
            Ok(Arrow::new(
                dividend.domain,
                divisor.domain,
                format!("{}\\{}", divisor.relation, dividend.relation),
            ))
        }
    }

    impl ResidualLaws for Relations {
        fn right_residual_intro(
            &self,
            _divisor: &Arrow<&'static str, String>,
            _candidate: &Arrow<&'static str, String>,
            _dividend: &Arrow<&'static str, String>,
            composite_in_dividend: String,
        ) -> Result<String, Infallible> {
            Ok(format!("right-intro({composite_in_dividend})"))
        }

        fn right_residual_elim(
            &self,
            _divisor: &Arrow<&'static str, String>,
            _candidate: &Arrow<&'static str, String>,
            _dividend: &Arrow<&'static str, String>,
            candidate_in_residual: String,
        ) -> Result<String, Infallible> {
            Ok(format!("right-elim({candidate_in_residual})"))
        }

        fn left_residual_intro(
            &self,
            _divisor: &Arrow<&'static str, String>,
            _candidate: &Arrow<&'static str, String>,
            _dividend: &Arrow<&'static str, String>,
            composite_in_dividend: String,
        ) -> Result<String, Infallible> {
            Ok(format!("left-intro({composite_in_dividend})"))
        }

        fn left_residual_elim(
            &self,
            _divisor: &Arrow<&'static str, String>,
            _candidate: &Arrow<&'static str, String>,
            _dividend: &Arrow<&'static str, String>,
            divisor_in_residual: String,
        ) -> Result<String, Infallible> {
            Ok(format!("left-elim({divisor_in_residual})"))
        }
    }

    #[test]
    fn arrows_retain_domains_across_composition() {
        let algebra = Relations;
        let f = Arrow::new("A", "B", "f".to_owned());
        let g = Arrow::new("B", "C", "g".to_owned());
        let gf = algebra.compose(f, g).unwrap();
        assert_eq!(gf.domain, "A");
        assert_eq!(gf.codomain, "C");
        assert_eq!(gf.relation, "f;g");
    }

    #[test]
    fn residuals_have_the_adjunction_types() {
        let algebra = Relations;
        let r = Arrow::new("A", "B", "r".to_owned());
        let s = Arrow::new("B", "C", "s".to_owned());
        let t = Arrow::new("A", "C", "t".to_owned());

        let right = algebra.right_residual(t.clone(), r.clone()).unwrap();
        assert_eq!(right, Arrow::new("B", "C", "t/r".to_owned()));

        let left = algebra.left_residual(s.clone(), t.clone()).unwrap();
        assert_eq!(left, Arrow::new("A", "B", "s\\t".to_owned()));

        let composite_in_t = "s∘r⊆t".to_owned();
        let right_intro = algebra
            .right_residual_intro(&r, &s, &t, composite_in_t.clone())
            .unwrap();
        assert_eq!(right_intro, "right-intro(s∘r⊆t)");
        assert_eq!(
            algebra
                .right_residual_elim(&r, &s, &t, right_intro)
                .unwrap(),
            "right-elim(right-intro(s∘r⊆t))"
        );

        let left_intro = algebra
            .left_residual_intro(&r, &s, &t, composite_in_t)
            .unwrap();
        assert_eq!(left_intro, "left-intro(s∘r⊆t)");
        assert_eq!(
            algebra.left_residual_elim(&r, &s, &t, left_intro).unwrap(),
            "left-elim(left-intro(s∘r⊆t))"
        );
    }
}
