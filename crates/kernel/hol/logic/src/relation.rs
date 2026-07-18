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

/// Inclusion/equality judgments for relations.
///
/// Results are theorems, not booleans: a backend need not decide either
/// judgment.
pub trait RelationOrder: Category {
    // TODO(cov:kernel.logic.relation-judgment-separation, major): Split proposition construction, derivation laws, supplied evidence, and optional decision procedures so this API does not suggest arbitrary inclusions can be proved on demand.
    /// Prove `left ⊆ right`.
    fn inclusion(
        &self,
        left: &Arrow<Self::Type, Self::Relation>,
        right: &Arrow<Self::Type, Self::Relation>,
    ) -> Result<Self::Thm, Self::Error>;
    /// Prove extensional equality of relations.
    fn relation_equality(
        &self,
        left: &Arrow<Self::Type, Self::Relation>,
        right: &Arrow<Self::Type, Self::Relation>,
    ) -> Result<Self::Thm, Self::Error>;
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

/// Proof-producing relation-property interface.
pub trait RelationProperties: Category {
    /// Prove a property of a relation.
    fn prove_property(
        &self,
        relation: &Arrow<Self::Type, Self::Relation>,
        property: RelationProperty,
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
