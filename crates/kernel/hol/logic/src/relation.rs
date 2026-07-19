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

/// Binary product objects and their relational structural arrows.
///
/// Pairing accepts arbitrary relations, not only maps. Backends which support
/// products only for functional arrows can expose a narrower adapter above
/// this vocabulary instead of claiming this capability.
pub trait ProductSyntax: Category {
    /// Construct the product object `A × B`.
    fn product_type(&self, left: Self::Type, right: Self::Type) -> Result<Self::Type, Self::Error>;

    /// First projection `π₁ : A × B ↔ A`.
    fn first_projection(
        &self,
        left: Self::Type,
        right: Self::Type,
    ) -> Result<Arrow<Self::Type, Self::Relation>, Self::Error>;

    /// Second projection `π₂ : A × B ↔ B`.
    fn second_projection(
        &self,
        left: Self::Type,
        right: Self::Type,
    ) -> Result<Arrow<Self::Type, Self::Relation>, Self::Error>;

    /// Pair `left : X ↔ A` and `right : X ↔ B` as `⟨left,right⟩ : X ↔ A × B`.
    fn pair(
        &self,
        left: Arrow<Self::Type, Self::Relation>,
        right: Arrow<Self::Type, Self::Relation>,
    ) -> Result<Arrow<Self::Type, Self::Relation>, Self::Error>;
}

/// Binary coproduct objects and their relational structural arrows.
pub trait CoproductSyntax: Category {
    /// Construct the coproduct object `A + B`.
    fn coproduct_type(
        &self,
        left: Self::Type,
        right: Self::Type,
    ) -> Result<Self::Type, Self::Error>;

    /// Left injection `ι₁ : A ↔ A + B`.
    fn left_injection(
        &self,
        left: Self::Type,
        right: Self::Type,
    ) -> Result<Arrow<Self::Type, Self::Relation>, Self::Error>;

    /// Right injection `ι₂ : B ↔ A + B`.
    fn right_injection(
        &self,
        left: Self::Type,
        right: Self::Type,
    ) -> Result<Arrow<Self::Type, Self::Relation>, Self::Error>;

    /// Copair `left : A ↔ X` and `right : B ↔ X` as `[left,right] : A + B ↔ X`.
    fn copair(
        &self,
        left: Arrow<Self::Type, Self::Relation>,
        right: Arrow<Self::Type, Self::Relation>,
    ) -> Result<Arrow<Self::Type, Self::Relation>, Self::Error>;
}

/// A span which tabulates a relation `A ↔ B`.
#[derive(Clone, Debug, PartialEq)]
pub struct Tabulation<Ty, Rel> {
    /// The apex object `T`.
    pub object: Ty,
    /// The left leg `f : T ↔ A`.
    pub left: Arrow<Ty, Rel>,
    /// The right leg `g : T ↔ B`.
    pub right: Arrow<Ty, Rel>,
}

impl<Ty, Rel> Tabulation<Ty, Rel> {
    /// Construct a tabulating span.
    pub const fn new(object: Ty, left: Arrow<Ty, Rel>, right: Arrow<Ty, Rel>) -> Self {
        Self {
            object,
            left,
            right,
        }
    }
}

/// Construction of tabulating spans.
///
/// The laws are separate: returning a span alone does not claim that it
/// factors the relation or that its legs are jointly monic.
pub trait TabulationSyntax: Category {
    fn tabulate(
        &self,
        relation: &Arrow<Self::Type, Self::Relation>,
    ) -> Result<Tabulation<Self::Type, Self::Relation>, Self::Error>;
}

/// Reflexive-transitive closure syntax.
///
/// This operation constructs a candidate `r*`; its universal property is
/// advertised independently through [`ClosureLaws`].
pub trait ClosureSyntax: Category {
    fn reflexive_transitive_closure(
        &self,
        relation: Arrow<Self::Type, Self::Relation>,
    ) -> Result<Arrow<Self::Type, Self::Relation>, Self::Error>;
}

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

/// Proof interface for the relational universal property of binary products.
///
/// Implementations return checked theorems in their existing theorem carrier;
/// this vocabulary grants no authority to construct one.
pub trait ProductLaws: ProductSyntax + RelationJudgmentSyntax {
    /// `π₁ ∘ ⟨f,g⟩ ⊆ f`.
    fn pair_first_inclusion(
        &self,
        left: &Arrow<Self::Type, Self::Relation>,
        right: &Arrow<Self::Type, Self::Relation>,
    ) -> Result<Self::Thm, Self::Error>;

    /// `π₂ ∘ ⟨f,g⟩ ⊆ g`.
    fn pair_second_inclusion(
        &self,
        left: &Arrow<Self::Type, Self::Relation>,
        right: &Arrow<Self::Type, Self::Relation>,
    ) -> Result<Self::Thm, Self::Error>;

    /// From `π₁ ∘ h ⊆ f` and `π₂ ∘ h ⊆ g`, prove `h ⊆ ⟨f,g⟩`.
    fn pair_greatest(
        &self,
        left: &Arrow<Self::Type, Self::Relation>,
        right: &Arrow<Self::Type, Self::Relation>,
        candidate: &Arrow<Self::Type, Self::Relation>,
        candidate_first_in_left: Self::Thm,
        candidate_second_in_right: Self::Thm,
    ) -> Result<Self::Thm, Self::Error>;
}

/// Proof interface for the relational universal property of binary coproducts.
pub trait CoproductLaws: CoproductSyntax + RelationJudgmentSyntax {
    /// `f ⊆ [f,g] ∘ ι₁`.
    fn copair_contains_left(
        &self,
        left: &Arrow<Self::Type, Self::Relation>,
        right: &Arrow<Self::Type, Self::Relation>,
    ) -> Result<Self::Thm, Self::Error>;

    /// `g ⊆ [f,g] ∘ ι₂`.
    fn copair_contains_right(
        &self,
        left: &Arrow<Self::Type, Self::Relation>,
        right: &Arrow<Self::Type, Self::Relation>,
    ) -> Result<Self::Thm, Self::Error>;

    /// From `f ⊆ h ∘ ι₁` and `g ⊆ h ∘ ι₂`, prove `[f,g] ⊆ h`.
    fn copair_least(
        &self,
        left: &Arrow<Self::Type, Self::Relation>,
        right: &Arrow<Self::Type, Self::Relation>,
        candidate: &Arrow<Self::Type, Self::Relation>,
        left_in_candidate: Self::Thm,
        right_in_candidate: Self::Thm,
    ) -> Result<Self::Thm, Self::Error>;
}

/// Proof interface for a tabulating span.
pub trait TabulationLaws: TabulationSyntax + RelationAlgebra + RelationJudgmentSyntax {
    /// Prove `relation = right ∘ left†`.
    fn tabulation_factorization(
        &self,
        relation: &Arrow<Self::Type, Self::Relation>,
        tabulation: &Tabulation<Self::Type, Self::Relation>,
    ) -> Result<Self::Thm, Self::Error>;

    /// Prove `(left† ∘ left) ∩ (right† ∘ right) = id[T]`.
    fn tabulation_joint_monic(
        &self,
        tabulation: &Tabulation<Self::Type, Self::Relation>,
    ) -> Result<Self::Thm, Self::Error>;
}

/// Proof interface for the least reflexive-transitive relation containing `r`.
pub trait ClosureLaws: ClosureSyntax + RelationJudgmentSyntax {
    /// Prove `id[A] ⊆ r*`.
    fn closure_contains_identity(
        &self,
        relation: &Arrow<Self::Type, Self::Relation>,
    ) -> Result<Self::Thm, Self::Error>;

    /// Prove `r ⊆ r*`.
    fn closure_contains_relation(
        &self,
        relation: &Arrow<Self::Type, Self::Relation>,
    ) -> Result<Self::Thm, Self::Error>;

    /// Prove `r* ∘ r* ⊆ r*`.
    fn closure_is_transitive(
        &self,
        relation: &Arrow<Self::Type, Self::Relation>,
    ) -> Result<Self::Thm, Self::Error>;

    /// Given proofs that `candidate` is reflexive, contains `relation`, and is
    /// transitive, prove `relation* ⊆ candidate`.
    fn closure_least(
        &self,
        relation: &Arrow<Self::Type, Self::Relation>,
        candidate: &Arrow<Self::Type, Self::Relation>,
        identity_in_candidate: Self::Thm,
        relation_in_candidate: Self::Thm,
        candidate_transitive: Self::Thm,
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

    impl RelationAlgebra for Relations {
        fn empty(
            &self,
            domain: &'static str,
            codomain: &'static str,
        ) -> Result<Arrow<&'static str, String>, Infallible> {
            Ok(Arrow::new(domain, codomain, "empty".to_owned()))
        }

        fn universal(
            &self,
            domain: &'static str,
            codomain: &'static str,
        ) -> Result<Arrow<&'static str, String>, Infallible> {
            Ok(Arrow::new(domain, codomain, "universal".to_owned()))
        }

        fn converse(
            &self,
            relation: Arrow<&'static str, String>,
        ) -> Result<Arrow<&'static str, String>, Infallible> {
            Ok(Arrow::new(
                relation.codomain,
                relation.domain,
                format!("{}†", relation.relation),
            ))
        }

        fn union(
            &self,
            left: Arrow<&'static str, String>,
            right: Arrow<&'static str, String>,
        ) -> Result<Arrow<&'static str, String>, Infallible> {
            assert_eq!((left.domain, left.codomain), (right.domain, right.codomain));
            Ok(Arrow::new(
                left.domain,
                left.codomain,
                format!("{}∪{}", left.relation, right.relation),
            ))
        }

        fn intersection(
            &self,
            left: Arrow<&'static str, String>,
            right: Arrow<&'static str, String>,
        ) -> Result<Arrow<&'static str, String>, Infallible> {
            assert_eq!((left.domain, left.codomain), (right.domain, right.codomain));
            Ok(Arrow::new(
                left.domain,
                left.codomain,
                format!("{}∩{}", left.relation, right.relation),
            ))
        }
    }

    impl ProductSyntax for Relations {
        fn product_type(
            &self,
            _left: &'static str,
            _right: &'static str,
        ) -> Result<&'static str, Infallible> {
            Ok("A×B")
        }

        fn first_projection(
            &self,
            left: &'static str,
            right: &'static str,
        ) -> Result<Arrow<&'static str, String>, Infallible> {
            Ok(Arrow::new(
                self.product_type(left, right)?,
                left,
                "π1".to_owned(),
            ))
        }

        fn second_projection(
            &self,
            left: &'static str,
            right: &'static str,
        ) -> Result<Arrow<&'static str, String>, Infallible> {
            Ok(Arrow::new(
                self.product_type(left, right)?,
                right,
                "π2".to_owned(),
            ))
        }

        fn pair(
            &self,
            left: Arrow<&'static str, String>,
            right: Arrow<&'static str, String>,
        ) -> Result<Arrow<&'static str, String>, Infallible> {
            assert_eq!(left.domain, right.domain);
            Ok(Arrow::new(
                left.domain,
                self.product_type(left.codomain, right.codomain)?,
                format!("⟨{},{}⟩", left.relation, right.relation),
            ))
        }
    }

    impl CoproductSyntax for Relations {
        fn coproduct_type(
            &self,
            _left: &'static str,
            _right: &'static str,
        ) -> Result<&'static str, Infallible> {
            Ok("A+B")
        }

        fn left_injection(
            &self,
            left: &'static str,
            right: &'static str,
        ) -> Result<Arrow<&'static str, String>, Infallible> {
            Ok(Arrow::new(
                left,
                self.coproduct_type(left, right)?,
                "ι1".to_owned(),
            ))
        }

        fn right_injection(
            &self,
            left: &'static str,
            right: &'static str,
        ) -> Result<Arrow<&'static str, String>, Infallible> {
            Ok(Arrow::new(
                right,
                self.coproduct_type(left, right)?,
                "ι2".to_owned(),
            ))
        }

        fn copair(
            &self,
            left: Arrow<&'static str, String>,
            right: Arrow<&'static str, String>,
        ) -> Result<Arrow<&'static str, String>, Infallible> {
            assert_eq!(left.codomain, right.codomain);
            Ok(Arrow::new(
                self.coproduct_type(left.domain, right.domain)?,
                left.codomain,
                format!("[{},{}]", left.relation, right.relation),
            ))
        }
    }

    impl TabulationSyntax for Relations {
        fn tabulate(
            &self,
            relation: &Arrow<&'static str, String>,
        ) -> Result<Tabulation<&'static str, String>, Infallible> {
            Ok(Tabulation::new(
                "T",
                Arrow::new("T", relation.domain, "f".to_owned()),
                Arrow::new("T", relation.codomain, "g".to_owned()),
            ))
        }
    }

    impl ClosureSyntax for Relations {
        fn reflexive_transitive_closure(
            &self,
            relation: Arrow<&'static str, String>,
        ) -> Result<Arrow<&'static str, String>, Infallible> {
            assert_eq!(relation.domain, relation.codomain);
            Ok(Arrow::new(
                relation.domain,
                relation.codomain,
                format!("{}*", relation.relation),
            ))
        }
    }

    impl ProductLaws for Relations {
        fn pair_first_inclusion(
            &self,
            _left: &Arrow<&'static str, String>,
            _right: &Arrow<&'static str, String>,
        ) -> Result<String, Infallible> {
            Ok("pair-first-inclusion".to_owned())
        }

        fn pair_second_inclusion(
            &self,
            _left: &Arrow<&'static str, String>,
            _right: &Arrow<&'static str, String>,
        ) -> Result<String, Infallible> {
            Ok("pair-second-inclusion".to_owned())
        }

        fn pair_greatest(
            &self,
            _left: &Arrow<&'static str, String>,
            _right: &Arrow<&'static str, String>,
            _candidate: &Arrow<&'static str, String>,
            candidate_first_in_left: String,
            candidate_second_in_right: String,
        ) -> Result<String, Infallible> {
            Ok(format!(
                "pair-greatest({candidate_first_in_left},{candidate_second_in_right})"
            ))
        }
    }

    impl CoproductLaws for Relations {
        fn copair_contains_left(
            &self,
            _left: &Arrow<&'static str, String>,
            _right: &Arrow<&'static str, String>,
        ) -> Result<String, Infallible> {
            Ok("copair-contains-left".to_owned())
        }

        fn copair_contains_right(
            &self,
            _left: &Arrow<&'static str, String>,
            _right: &Arrow<&'static str, String>,
        ) -> Result<String, Infallible> {
            Ok("copair-contains-right".to_owned())
        }

        fn copair_least(
            &self,
            _left: &Arrow<&'static str, String>,
            _right: &Arrow<&'static str, String>,
            _candidate: &Arrow<&'static str, String>,
            left_in_candidate: String,
            right_in_candidate: String,
        ) -> Result<String, Infallible> {
            Ok(format!(
                "copair-least({left_in_candidate},{right_in_candidate})"
            ))
        }
    }

    impl TabulationLaws for Relations {
        fn tabulation_factorization(
            &self,
            _relation: &Arrow<&'static str, String>,
            _tabulation: &Tabulation<&'static str, String>,
        ) -> Result<String, Infallible> {
            Ok("tabulation-factorization".to_owned())
        }

        fn tabulation_joint_monic(
            &self,
            _tabulation: &Tabulation<&'static str, String>,
        ) -> Result<String, Infallible> {
            Ok("tabulation-joint-monic".to_owned())
        }
    }

    impl ClosureLaws for Relations {
        fn closure_contains_identity(
            &self,
            _relation: &Arrow<&'static str, String>,
        ) -> Result<String, Infallible> {
            Ok("closure-reflexive".to_owned())
        }

        fn closure_contains_relation(
            &self,
            _relation: &Arrow<&'static str, String>,
        ) -> Result<String, Infallible> {
            Ok("closure-contains".to_owned())
        }

        fn closure_is_transitive(
            &self,
            _relation: &Arrow<&'static str, String>,
        ) -> Result<String, Infallible> {
            Ok("closure-transitive".to_owned())
        }

        fn closure_least(
            &self,
            _relation: &Arrow<&'static str, String>,
            _candidate: &Arrow<&'static str, String>,
            identity_in_candidate: String,
            relation_in_candidate: String,
            candidate_transitive: String,
        ) -> Result<String, Infallible> {
            Ok(format!(
                "closure-least({identity_in_candidate},{relation_in_candidate},{candidate_transitive})"
            ))
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

    #[test]
    fn allegory_capabilities_are_independent_and_typed() {
        let algebra = Relations;
        let f = Arrow::new("X", "A", "f".to_owned());
        let g = Arrow::new("X", "B", "g".to_owned());
        assert_eq!(
            algebra.pair(f.clone(), g.clone()).unwrap(),
            Arrow::new("X", "A×B", "⟨f,g⟩".to_owned())
        );
        assert_eq!(
            algebra.first_projection("A", "B").unwrap(),
            Arrow::new("A×B", "A", "π1".to_owned())
        );
        assert_eq!(
            algebra.pair_first_inclusion(&f, &g).unwrap(),
            "pair-first-inclusion"
        );

        let h = Arrow::new("A", "X", "h".to_owned());
        let k = Arrow::new("B", "X", "k".to_owned());
        assert_eq!(
            algebra.copair(h.clone(), k.clone()).unwrap(),
            Arrow::new("A+B", "X", "[h,k]".to_owned())
        );
        assert_eq!(
            algebra.right_injection("A", "B").unwrap(),
            Arrow::new("B", "A+B", "ι2".to_owned())
        );
        assert_eq!(
            algebra.copair_contains_right(&h, &k).unwrap(),
            "copair-contains-right"
        );

        let relation = Arrow::new("A", "B", "r".to_owned());
        let tabulation = algebra.tabulate(&relation).unwrap();
        assert_eq!(tabulation.object, "T");
        assert_eq!(tabulation.left, Arrow::new("T", "A", "f".to_owned()));
        assert_eq!(tabulation.right, Arrow::new("T", "B", "g".to_owned()));
        assert_eq!(
            algebra
                .tabulation_factorization(&relation, &tabulation)
                .unwrap(),
            "tabulation-factorization"
        );

        let step = Arrow::new("A", "A", "step".to_owned());
        assert_eq!(
            algebra.reflexive_transitive_closure(step.clone()).unwrap(),
            Arrow::new("A", "A", "step*".to_owned())
        );
        assert_eq!(
            algebra
                .closure_least(
                    &step,
                    &Arrow::new("A", "A", "candidate".to_owned()),
                    "id⊆c".to_owned(),
                    "step⊆c".to_owned(),
                    "c;c⊆c".to_owned(),
                )
                .unwrap(),
            "closure-least(id⊆c,step⊆c,c;c⊆c)"
        );
    }
}
