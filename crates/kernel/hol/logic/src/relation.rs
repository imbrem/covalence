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

// TODO(cov:kernel.logic.relation-allegory, major): Add products, coproducts, residuals, tabulation, and closure capabilities with law bundles, without making them prerequisites for the core relation algebra.

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
}
