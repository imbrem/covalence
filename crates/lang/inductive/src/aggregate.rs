//! Backend seams for finite aggregate datatypes.
//!
//! These traits are intentionally smaller than a logic API. They let a
//! backend expose its own proof-bearing realization bundle without making
//! this crate choose universal term or theorem carrier types.

use crate::error::SpecError;
use crate::logic::Logic;
use crate::polynomial::{EnumSpec, RecordSpec, VariantSpec};
use crate::validated::Validated;

/// A realized record and its proof-bearing operations.
///
/// `constructor` has the curried field types followed by `carrier`;
/// `projections` follow declaration order.
pub struct RecordTheory<L: Logic, P> {
    /// The exact checked declaration realized by this bundle.
    pub spec: Validated<RecordSpec<P>>,
    /// Backend representation of the record type.
    pub carrier: L::Type,
    /// Record constructor.
    pub constructor: L::Term,
    /// Field projections in declaration order.
    pub projections: Vec<L::Term>,
    /// Laws for construction and observation.
    pub facts: Box<dyn RecordFacts<L>>,
}

/// Laws for a record realization.
pub trait RecordFacts<L: Logic> {
    /// Projection β-law for field `i`: `⊢ projectᵢ (construct fields) = fieldsᵢ`.
    fn project_construct(&self, fields: &[L::Term], i: usize) -> Result<L::Thm, L::Error>;

    /// Record η/extensionality: prove two records equal from equality of all
    /// corresponding projections.
    fn extensionality(
        &self,
        left: &L::Term,
        right: &L::Term,
        fields_equal: Vec<L::Thm>,
    ) -> Result<L::Thm, L::Error>;
}

/// A realized variant and its proof-bearing operations.
pub struct VariantTheory<L: Logic, P> {
    /// The exact checked declaration realized by this bundle.
    pub spec: Validated<VariantSpec<P>>,
    /// Backend representation of the sum type.
    pub carrier: L::Type,
    /// Injections in case order.
    pub injections: Vec<L::Term>,
    /// Elimination and constructor laws.
    pub facts: Box<dyn VariantFacts<L>>,
}

/// Laws for a variant realization.
pub trait VariantFacts<L: Logic> {
    /// Apply case analysis with one branch per declared case.
    fn case_app(&self, branches: &[L::Term], value: &L::Term) -> Result<L::Term, L::Error>;

    /// Case β-law for injection `i`.
    fn case_injection(
        &self,
        branches: &[L::Term],
        i: usize,
        fields: &[L::Term],
    ) -> Result<L::Thm, L::Error>;

    /// Injectivity at field `field` of case `i`.
    fn injective(
        &self,
        i: usize,
        field: usize,
        left: &[L::Term],
        right: &[L::Term],
    ) -> Result<L::Thm, L::Error>;

    /// Distinct constructors have unequal images.
    fn distinct(
        &self,
        left_case: usize,
        right_case: usize,
        left: &[L::Term],
        right: &[L::Term],
    ) -> Result<L::Thm, L::Error>;
}

/// Enumeration theory. This is the nullary specialization of a variant.
pub struct EnumTheory<L: Logic> {
    /// The exact checked declaration.
    pub spec: Validated<EnumSpec>,
    /// Backend representation of the enum type.
    pub carrier: L::Type,
    /// Nullary case terms in declaration order.
    pub cases: Vec<L::Term>,
    /// Exhaustiveness and distinctness laws.
    pub facts: Box<dyn EnumFacts<L>>,
}

/// Laws for an enumeration.
pub trait EnumFacts<L: Logic> {
    /// Exhaustiveness over the listed cases.
    fn cases(&self) -> Result<L::Thm, L::Error>;
    /// Distinctness of cases `i` and `j`.
    fn distinct(&self, i: usize, j: usize) -> Result<L::Thm, L::Error>;
}

/// Backend whose record result obeys the shared proof-bearing contract.
pub trait ProofBearingRecordBackend<L: Logic, P> {
    /// Backend error.
    type Error;
    /// Realize a checked record as constructors, projections, and laws.
    fn realize_record_theory(
        &self,
        spec: &Validated<RecordSpec<P>>,
    ) -> Result<RecordTheory<L, P>, Self::Error>;
}

/// Backend whose variant result obeys the shared proof-bearing contract.
pub trait ProofBearingVariantBackend<L: Logic, P> {
    /// Backend error.
    type Error;
    /// Realize a checked variant as injections, elimination, and laws.
    fn realize_variant_theory(
        &self,
        spec: &Validated<VariantSpec<P>>,
    ) -> Result<VariantTheory<L, P>, Self::Error>;
}

/// Backend whose enum result obeys the shared proof-bearing contract.
pub trait ProofBearingEnumBackend<L: Logic> {
    /// Backend error.
    type Error;
    /// Realize a checked enum as cases and their laws.
    fn realize_enum_theory(&self, spec: &Validated<EnumSpec>)
    -> Result<EnumTheory<L>, Self::Error>;
}

/// Capability for realizing non-recursive records.
pub trait RecordBackend<P> {
    /// Backend-specific record bundle.
    type Record;
    /// Backend error.
    type Error;

    /// Realize a structurally valid record.
    fn realize_record(&self, spec: &Validated<RecordSpec<P>>) -> Result<Self::Record, Self::Error>;
}

/// Capability for realizing non-recursive variants.
pub trait VariantBackend<P> {
    /// Backend-specific variant bundle.
    type Variant;
    /// Backend error.
    type Error;

    /// Realize a structurally valid variant.
    fn realize_variant(
        &self,
        spec: &Validated<VariantSpec<P>>,
    ) -> Result<Self::Variant, Self::Error>;
}

/// Capability for realizing finite enumerations.
pub trait EnumBackend {
    /// Backend-specific enum bundle.
    type Enum;
    /// Backend error.
    type Error;

    /// Realize a structurally valid enum.
    fn realize_enum(&self, spec: &Validated<EnumSpec>) -> Result<Self::Enum, Self::Error>;
}

/// Validate before invoking a record backend.
pub fn realize_record<P: Clone, B: RecordBackend<P>>(
    backend: &B,
    spec: &RecordSpec<P>,
) -> Result<B::Record, AggregateRealizeError<B::Error>> {
    let spec = Validated::try_from(spec.clone()).map_err(AggregateRealizeError::Spec)?;
    backend
        .realize_record(&spec)
        .map_err(AggregateRealizeError::Backend)
}

/// Validate before invoking a variant backend.
pub fn realize_variant<P: Clone, B: VariantBackend<P>>(
    backend: &B,
    spec: &VariantSpec<P>,
) -> Result<B::Variant, AggregateRealizeError<B::Error>> {
    let spec = Validated::try_from(spec.clone()).map_err(AggregateRealizeError::Spec)?;
    backend
        .realize_variant(&spec)
        .map_err(AggregateRealizeError::Backend)
}

/// Validate before invoking an enum backend.
pub fn realize_enum<B: EnumBackend>(
    backend: &B,
    spec: &EnumSpec,
) -> Result<B::Enum, AggregateRealizeError<B::Error>> {
    let spec = Validated::try_from(spec.clone()).map_err(AggregateRealizeError::Spec)?;
    backend
        .realize_enum(&spec)
        .map_err(AggregateRealizeError::Backend)
}

/// Failure from aggregate validation or backend realization.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AggregateRealizeError<E> {
    /// The portable aggregate specification is malformed.
    Spec(SpecError),
    /// The backend refused or failed to realize a valid specification.
    Backend(E),
}
