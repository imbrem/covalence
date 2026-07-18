//! Dependency-free interfaces for logic backends.
//!
//! This crate owns vocabulary, not a logic or a trusted implementation.  In
//! particular, implementing one of these traits cannot mint a theorem unless
//! the associated [`Logic::Theorem`] type already provides that authority.
//! APIs for theories such as naturals and inductive datatypes should depend on
//! this crate rather than on a concrete HOL representation.
//!
//! The traits are deliberately capability-sized.  A backend may implement
//! syntax without proof rules, equality without classical logic, or the
//! relational fragment without claiming to decide a relation.

#![forbid(unsafe_code)]

pub mod relation;

use core::fmt::Debug;

pub use relation::{
    Arrow, Category, Decision, RelationAlgebra, RelationEvidence, RelationJudgmentSyntax,
    RelationOrderDecision, RelationOrderLaws, RelationProperty, RelationPropertyEvidence,
    RelationPropertySyntax, ResidualLaws, ResidualSyntax,
};

/// The carrier types shared by logic capabilities.
///
/// `Kind` leaves room for HOL-ω and other higher-kinded backends.  A
/// simply-kinded backend can use `()` without paying for a reflected kind
/// language.
pub trait Logic {
    /// Kinds of types and type constructors.
    type Kind: Clone + PartialEq + Debug;
    /// Object-language types.
    type Type: Clone + PartialEq + Debug;
    /// Object-language terms.  Propositions are terms of a distinguished type
    /// in HOL-like implementations.
    type Term: Clone + PartialEq + Debug;
    /// Unforgeable proof/certificate values.
    type Thm: Clone + Debug;
    /// Errors produced while constructing or checking syntax and proofs.
    type Error: core::error::Error;
}

/// Kinds and type-operator application.
///
/// This is sufficient to describe the shape `m a` used by Haskell-style APIs.
/// Quantification and rank disciplines are separate capabilities because not
/// every logic supports higher-rank types.
pub trait TypeSystem: Logic {
    /// The kind of proper term-level types.
    fn proper(&self) -> Self::Kind;
    /// The kind `a -> b`.
    fn kind_arrow(&self, a: Self::Kind, b: Self::Kind) -> Self::Kind;
    /// The type of propositions.
    fn proposition_type(&self) -> Self::Type;
    /// A term-level function type.
    fn function_type(&self, a: Self::Type, b: Self::Type) -> Self::Type;
    /// A free type or type-operator variable.
    fn type_variable(&self, name: &str, kind: Self::Kind) -> Self::Type;
    /// Apply a type operator to a type argument.
    fn type_apply(
        &self,
        operator: Self::Type,
        argument: Self::Type,
    ) -> Result<Self::Type, Self::Error>;
    /// Return the kind of a type when the backend can establish one.
    fn kind_of(&self, ty: &Self::Type) -> Result<Self::Kind, Self::Error>;
}

/// Variables, application, and binders for object-language terms.
pub trait TermLanguage: Logic {
    /// A free term variable.
    fn variable(&self, name: &str, ty: Self::Type) -> Self::Term;
    /// Type-checked term application.
    fn apply(&self, function: Self::Term, argument: Self::Term) -> Result<Self::Term, Self::Error>;
    /// Bind a named free variable in a term.
    fn abstract_term(&self, name: &str, ty: Self::Type, body: Self::Term) -> Self::Term;
    /// Return the type of a term.
    fn type_of(&self, term: &Self::Term) -> Result<Self::Type, Self::Error>;
}

/// Equality propositions, kept separate from equality proof rules.
pub trait EqualitySyntax: Logic {
    /// Construct `left = right`.
    fn equal(&self, left: Self::Term, right: Self::Term) -> Result<Self::Term, Self::Error>;
    /// Destruct an equality proposition.
    fn as_equal(&self, proposition: &Self::Term) -> Option<(Self::Term, Self::Term)>;
}

/// Universal and existential object-language binders.
pub trait QuantifierSyntax: Logic {
    /// Construct `forall name: ty. body`, binding the named free variable.
    fn forall(
        &self,
        name: &str,
        ty: Self::Type,
        body: Self::Term,
    ) -> Result<Self::Term, Self::Error>;
    /// Construct `exists name: ty. body`, binding the named free variable.
    fn exists(
        &self,
        name: &str,
        ty: Self::Type,
        body: Self::Term,
    ) -> Result<Self::Term, Self::Error>;
}

/// Read-only access to a theorem's sequent.
pub trait TheoremView: Logic {
    /// The theorem's conclusion.
    fn conclusion(&self, theorem: &Self::Thm) -> Self::Term;
    /// The theorem's hypotheses.
    fn hypotheses(&self, theorem: &Self::Thm) -> Vec<Self::Term>;
}

/// Minimal equality proof rules.
pub trait EqualityRules: EqualitySyntax + TheoremView {
    /// Prove reflexivity.
    fn reflexivity(&self, term: Self::Term) -> Result<Self::Thm, Self::Error>;
    /// Reverse a proved equality.
    fn symmetry(&self, theorem: Self::Thm) -> Result<Self::Thm, Self::Error>;
    /// Compose proved equalities.
    fn transitivity(&self, left: Self::Thm, right: Self::Thm) -> Result<Self::Thm, Self::Error>;
    /// Transport a proof along an equality of propositions.
    fn equality_elim(
        &self,
        equality: Self::Thm,
        proof: Self::Thm,
    ) -> Result<Self::Thm, Self::Error>;
}

/// Proof rules for term-level binders.
pub trait BinderRules: QuantifierSyntax + TheoremView {
    /// Generalize a theorem over a free variable.
    fn forall_intro(
        &self,
        theorem: Self::Thm,
        name: &str,
        ty: Self::Type,
    ) -> Result<Self::Thm, Self::Error>;
    /// Instantiate a universally quantified theorem.
    fn forall_elim(
        &self,
        theorem: Self::Thm,
        argument: Self::Term,
    ) -> Result<Self::Thm, Self::Error>;
}
