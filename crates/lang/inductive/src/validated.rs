//! Validated specification wrappers.
//!
//! Parsing and interchange need permissive plain-data `*Spec` values so they
//! can report malformed input. Realization needs the opposite: a backend
//! should only receive a value whose structural invariants have already been
//! checked. [`Validated`] is that boundary.

use std::ops::Deref;

use crate::error::SpecError;
use crate::fixpoint::FixpointSpec;
use crate::polynomial::{EnumSpec, PolynomialSpec, RecordSpec, VariantSpec};
use crate::spec::InductiveSpec;

/// A specification which has passed its structural validation.
///
/// The inner value is intentionally private. Construct this with `TryFrom`;
/// use [`into_inner`](Self::into_inner) when serializing or transforming it.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Validated<S>(S);

impl<S> Validated<S> {
    /// Borrow the checked specification.
    pub fn as_inner(&self) -> &S {
        &self.0
    }

    /// Recover the plain-data specification.
    pub fn into_inner(self) -> S {
        self.0
    }
}

impl<S> Deref for Validated<S> {
    type Target = S;

    fn deref(&self) -> &Self::Target {
        self.as_inner()
    }
}

impl<P> Validated<PolynomialSpec<P>> {
    /// Map parameter tokens. This preserves every structural invariant.
    pub fn map_param<Q>(self, f: impl FnMut(P) -> Q) -> Validated<PolynomialSpec<Q>> {
        Validated(self.into_inner().map_param(f))
    }
}

impl<P> Validated<FixpointSpec<P>> {
    /// Map parameter tokens. This preserves every structural invariant.
    pub fn map_param<Q>(self, f: impl FnMut(P) -> Q) -> Validated<FixpointSpec<Q>> {
        Validated(self.into_inner().map_param(f))
    }
}

impl<P> Validated<InductiveSpec<P>> {
    /// Map external sorts. This preserves every structural invariant.
    pub fn map_ext<Q>(self, f: impl FnMut(P) -> Q) -> Validated<InductiveSpec<Q>> {
        Validated(self.into_inner().map_ext(f))
    }
}

impl TryFrom<EnumSpec> for Validated<EnumSpec> {
    type Error = SpecError;
    fn try_from(spec: EnumSpec) -> Result<Self, Self::Error> {
        spec.validate()?;
        Ok(Self(spec))
    }
}

macro_rules! impl_generic_validated {
    ($spec:ident) => {
        impl<P> TryFrom<$spec<P>> for Validated<$spec<P>> {
            type Error = SpecError;
            fn try_from(spec: $spec<P>) -> Result<Self, Self::Error> {
                spec.validate()?;
                Ok(Self(spec))
            }
        }
    };
}

impl_generic_validated!(RecordSpec);
impl_generic_validated!(VariantSpec);
impl_generic_validated!(PolynomialSpec);
impl_generic_validated!(FixpointSpec);
impl_generic_validated!(InductiveSpec);

#[cfg(test)]
mod tests {
    use crate::{CtorSpec, EnumSpec, InductiveSpec, Position, RecordSpec};

    use super::Validated;

    #[test]
    fn invalid_specs_cannot_be_wrapped() {
        assert!(Validated::try_from(EnumSpec::new("empty", Vec::<&str>::new())).is_err());
        assert!(
            Validated::try_from(RecordSpec::<()>::new(
                "recursive",
                vec![crate::FieldSpec::new("tail", Position::Var)],
            ))
            .is_err()
        );
        assert!(
            Validated::try_from(InductiveSpec::<()>::new(
                "duplicate",
                vec![CtorSpec::nullary("x"), CtorSpec::nullary("x")],
            ))
            .is_err()
        );
    }

    #[test]
    fn checked_value_round_trips_as_plain_data() {
        let spec = EnumSpec::new("colour", ["red", "green"]);
        let checked = Validated::try_from(spec.clone()).unwrap();
        assert_eq!(checked.as_inner(), &spec);
        assert_eq!(checked.into_inner(), spec);
    }
}
