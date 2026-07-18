//! Backend seams for finite aggregate datatypes.
//!
//! These traits are intentionally smaller than a logic API. They let a
//! backend expose its own proof-bearing realization bundle without making
//! this crate choose universal term or theorem carrier types.

use crate::error::SpecError;
use crate::polynomial::{EnumSpec, RecordSpec, VariantSpec};

/// Capability for realizing non-recursive records.
pub trait RecordBackend<P> {
    /// Backend-specific record bundle.
    type Record;
    /// Backend error.
    type Error;

    /// Realize a structurally valid record.
    fn realize_record(&self, spec: &RecordSpec<P>) -> Result<Self::Record, Self::Error>;
}

/// Capability for realizing non-recursive variants.
pub trait VariantBackend<P> {
    /// Backend-specific variant bundle.
    type Variant;
    /// Backend error.
    type Error;

    /// Realize a structurally valid variant.
    fn realize_variant(&self, spec: &VariantSpec<P>) -> Result<Self::Variant, Self::Error>;
}

/// Capability for realizing finite enumerations.
pub trait EnumBackend {
    /// Backend-specific enum bundle.
    type Enum;
    /// Backend error.
    type Error;

    /// Realize a structurally valid enum.
    fn realize_enum(&self, spec: &EnumSpec) -> Result<Self::Enum, Self::Error>;
}

/// Validate before invoking a record backend.
pub fn realize_record<P, B: RecordBackend<P>>(
    backend: &B,
    spec: &RecordSpec<P>,
) -> Result<B::Record, AggregateRealizeError<B::Error>> {
    spec.validate().map_err(AggregateRealizeError::Spec)?;
    backend
        .realize_record(spec)
        .map_err(AggregateRealizeError::Backend)
}

/// Validate before invoking a variant backend.
pub fn realize_variant<P, B: VariantBackend<P>>(
    backend: &B,
    spec: &VariantSpec<P>,
) -> Result<B::Variant, AggregateRealizeError<B::Error>> {
    spec.validate().map_err(AggregateRealizeError::Spec)?;
    backend
        .realize_variant(spec)
        .map_err(AggregateRealizeError::Backend)
}

/// Validate before invoking an enum backend.
pub fn realize_enum<B: EnumBackend>(
    backend: &B,
    spec: &EnumSpec,
) -> Result<B::Enum, AggregateRealizeError<B::Error>> {
    spec.validate().map_err(AggregateRealizeError::Spec)?;
    backend
        .realize_enum(spec)
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
