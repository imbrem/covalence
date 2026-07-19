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
//!
//! @covalence-api {"id":"A0001","title":"Logic carriers and capabilities","status":"experimental","dependsOn":[]}

#![forbid(unsafe_code)]

pub mod bits;
pub mod bytes;
pub mod bytes_nat;
pub mod nat;
pub mod relation;

use core::fmt::Debug;

pub use bits::{
    BitSyntax, BitsBytesPacking, BitsBytesPackingLaws, BitsConcatLaws, BitsConstruction,
    BitsNormalization, BitsObservation, BitsSyntax, BytePacking, FixedWidthBits,
    FixedWidthBitsLaws, IntraByteOrder, PartialByte,
};
pub use bytes_nat::{
    CanonicalNatBytes, FixedWidthError, NatBackedBytes, NatByteList, NatByteListError, Radix256Nat,
};
pub use nat::{
    NatAdditiveLaws, NatArithmetic, NatEqDecision, NatFreeness, NatLaws, NatMultiplicativeLaws,
    NatNormalization, NatOrder, NatRecursionLaws, NatSyntax,
};
pub use relation::{
    Arrow, Category, ClosureLaws, ClosureSyntax, CoproductLaws, CoproductSyntax, Decision,
    ProductLaws, ProductSyntax, RelationAlgebra, RelationEvidence, RelationJudgmentSyntax,
    RelationOrderDecision, RelationOrderLaws, RelationProperty, RelationPropertyEvidence,
    RelationPropertySyntax, ResidualLaws, ResidualSyntax, Tabulation, TabulationLaws,
    TabulationSyntax,
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

/// Read-only application syntax, separated from term construction so opaque
/// term representations need not expose their internals.
pub trait ApplicationView: Logic {
    /// Destruct `function argument`.
    fn as_application(&self, term: &Self::Term) -> Option<(Self::Term, Self::Term)>;
}

/// Equality propositions, kept separate from equality proof rules.
pub trait EqualitySyntax: Logic {
    /// Construct `left = right`.
    fn equal(&self, left: Self::Term, right: Self::Term) -> Result<Self::Term, Self::Error>;
    /// Destruct an equality proposition.
    fn as_equal(&self, proposition: &Self::Term) -> Option<(Self::Term, Self::Term)>;
}

/// Implication and conjunction syntax.
pub trait PropositionSyntax: Logic {
    /// Construct `antecedent ⟹ consequent`.
    fn implies(
        &self,
        antecedent: Self::Term,
        consequent: Self::Term,
    ) -> Result<Self::Term, Self::Error>;
    /// Construct `left ∧ right`.
    fn conjunction(&self, left: Self::Term, right: Self::Term) -> Result<Self::Term, Self::Error>;
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

/// Introduce a theorem with one explicit hypothesis.
pub trait AssumptionRules: TheoremView {
    /// `{proposition} ⊢ proposition`.
    fn assume(&self, proposition: Self::Term) -> Result<Self::Thm, Self::Error>;
}

/// Proof-producing β-conversion.
pub trait BetaRules: TermLanguage + TheoremView {
    /// Prove one top-level β reduction.
    fn beta_conversion(&self, redex: Self::Term) -> Result<Self::Thm, Self::Error>;
}

/// Congruence for object-language application.
pub trait ApplicationCongruence: TermLanguage + EqualityRules {
    /// Lift proved equalities through application.
    fn application_congruence(
        &self,
        functions: Self::Thm,
        arguments: Self::Thm,
    ) -> Result<Self::Thm, Self::Error>;
}

/// Instantiate a named free variable in a theorem.
pub trait TheoremInstantiation: TheoremView {
    fn instantiate(
        &self,
        theorem: Self::Thm,
        name: &str,
        replacement: Self::Term,
    ) -> Result<Self::Thm, Self::Error>;
}

/// Natural-deduction rules for implication.
pub trait ImplicationRules: PropositionSyntax + TheoremView {
    /// Discharge `hypothesis` from a theorem.
    fn implication_intro(
        &self,
        theorem: Self::Thm,
        hypothesis: &Self::Term,
    ) -> Result<Self::Thm, Self::Error>;
    /// Modus ponens.
    fn implication_elim(
        &self,
        implication: Self::Thm,
        antecedent: Self::Thm,
    ) -> Result<Self::Thm, Self::Error>;
}

/// Natural-deduction rules for conjunction.
pub trait ConjunctionRules: PropositionSyntax + TheoremView {
    fn conjunction_intro(
        &self,
        left: Self::Thm,
        right: Self::Thm,
    ) -> Result<Self::Thm, Self::Error>;
    fn conjunction_elim_left(&self, theorem: Self::Thm) -> Result<Self::Thm, Self::Error>;
    fn conjunction_elim_right(&self, theorem: Self::Thm) -> Result<Self::Thm, Self::Error>;
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
pub use bytes::{
    ByteNatBridge, ByteNatBridgeLaws, ByteSyntax, BytesConcatLaws, BytesConstruction,
    BytesNormalization, BytesObservation, BytesObservationLaws, BytesSyntax, Endianness,
    FixedWidthNatBytesConditions, FixedWidthNatBytesEncoding, FixedWidthNatBytesEncodingLaws,
    MinimalNatBytesEncoding, MinimalNatBytesEncodingLaws, NatByteSequence, NatByteSequenceBridge,
    NatByteSequenceBridgeLaws, NatBytesEquivalenceLaws, NatBytesEquivalenceSyntax,
};
