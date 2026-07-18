//! Least and greatest fixpoints of polynomial functors.
//!
//! The API deliberately separates the two capabilities. Implementing
//! [`InductiveFixpointBackend`] says a backend can construct `μF` and its
//! induction/recursion package; implementing [`CoinductiveFixpointBackend`]
//! says it can construct `νF` and its coinduction/corecursion package. A
//! partial backend implements only what it can honestly realize.

use smol_str::SmolStr;

use crate::error::SpecError;
use crate::polynomial::PolynomialSpec;

// TODO(cov:inductive.fixpoint-law-bundles, severe): Define shared proof-bearing in/out isomorphism, fold/unfold, induction, coinduction, and computation-law bundles instead of leaving realizations wholly opaque.

/// A polynomial endofunctor whose least or greatest fixpoint may be formed.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FixpointSpec<P> {
    /// Public name of the resulting carrier.
    pub name: SmolStr,
    /// The functor body `F`.
    pub functor: PolynomialSpec<P>,
}

impl<P> FixpointSpec<P> {
    /// Construct a fixpoint specification.
    pub fn new(name: impl Into<SmolStr>, functor: PolynomialSpec<P>) -> Self {
        Self {
            name: name.into(),
            functor,
        }
    }

    /// Validate the result name and functor.
    ///
    /// A constant functor is valid: its least and greatest fixpoints coincide
    /// with the represented aggregate.
    pub fn validate(&self) -> Result<(), SpecError> {
        if self.name.is_empty() {
            return Err(SpecError::EmptyTypeName);
        }
        self.functor.validate()
    }

    /// Map external parameter tokens without changing recursion positions.
    pub fn map_param<Q>(self, f: impl FnMut(P) -> Q) -> FixpointSpec<Q> {
        FixpointSpec {
            name: self.name,
            functor: self.functor.map_param(f),
        }
    }
}

/// Backend capability for least fixpoints `μF`.
///
/// `Inductive` is deliberately opaque to this crate. A logic-specific API
/// chooses the carrier, constructor, fold, induction, and computation-law
/// handles it exposes while preserving the plain-data specification.
pub trait InductiveFixpointBackend<P> {
    /// Logic/backend-specific realized induction bundle.
    type Inductive;
    /// Backend error.
    type Error;

    /// Realize the least fixpoint of `spec`.
    fn realize_inductive(&self, spec: &FixpointSpec<P>) -> Result<Self::Inductive, Self::Error>;
}

/// Backend capability for greatest fixpoints `νF`.
///
/// A realization normally packages destructors, unfold/corecursion, and a
/// bisimulation/coinduction rule. Those proof objects remain backend-specific.
pub trait CoinductiveFixpointBackend<P> {
    /// Logic/backend-specific realized coinduction bundle.
    type Coinductive;
    /// Backend error.
    type Error;

    /// Realize the greatest fixpoint of `spec`.
    fn realize_coinductive(&self, spec: &FixpointSpec<P>)
    -> Result<Self::Coinductive, Self::Error>;
}

/// Validate before invoking an inductive backend.
pub fn realize_inductive<P, B: InductiveFixpointBackend<P>>(
    backend: &B,
    spec: &FixpointSpec<P>,
) -> Result<B::Inductive, RealizeError<B::Error>> {
    spec.validate().map_err(RealizeError::Spec)?;
    backend
        .realize_inductive(spec)
        .map_err(RealizeError::Backend)
}

/// Validate before invoking a coinductive backend.
pub fn realize_coinductive<P, B: CoinductiveFixpointBackend<P>>(
    backend: &B,
    spec: &FixpointSpec<P>,
) -> Result<B::Coinductive, RealizeError<B::Error>> {
    spec.validate().map_err(RealizeError::Spec)?;
    backend
        .realize_coinductive(spec)
        .map_err(RealizeError::Backend)
}

/// Failure from the shared validation/realization boundary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RealizeError<E> {
    /// The portable specification is malformed.
    Spec(SpecError),
    /// The backend refused or failed to realize a valid specification.
    Backend(E),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::polynomial::{FieldSpec, Position, VariantCase};

    struct Names;

    impl InductiveFixpointBackend<&'static str> for Names {
        type Inductive = String;
        type Error = &'static str;

        fn realize_inductive(
            &self,
            spec: &FixpointSpec<&'static str>,
        ) -> Result<Self::Inductive, Self::Error> {
            Ok(format!("mu {}", spec.name))
        }
    }

    #[test]
    fn validates_before_backend_realization() {
        let list = FixpointSpec::new(
            "list",
            PolynomialSpec::new(
                "list-f",
                vec![
                    VariantCase::nullary("nil"),
                    VariantCase::new(
                        "cons",
                        vec![
                            FieldSpec::new("head", Position::Param("a")),
                            FieldSpec::new("tail", Position::Var),
                        ],
                    ),
                ],
            ),
        );
        assert_eq!(realize_inductive(&Names, &list).unwrap(), "mu list");
    }
}
