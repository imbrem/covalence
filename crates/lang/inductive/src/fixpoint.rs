//! Least and greatest fixpoints of polynomial functors.
//!
//! The API deliberately separates the two capabilities. Implementing
//! [`InductiveFixpointBackend`] says a backend can construct `μF` and its
//! induction/recursion package; implementing [`CoinductiveFixpointBackend`]
//! says it can construct `νF` and its coinduction/corecursion package. A
//! partial backend implements only what it can honestly realize.

use smol_str::SmolStr;

use crate::error::SpecError;
use crate::logic::Logic;
use crate::polynomial::PolynomialSpec;
use crate::validated::Validated;

/// A polynomial endofunctor whose least or greatest fixpoint may be formed.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FixpointSpec<P> {
    /// Public name of the resulting carrier.
    pub name: SmolStr,
    /// The functor body `F`.
    pub functor: PolynomialSpec<P>,
}

/// The Lambek isomorphism shared by least and greatest fixpoints.
///
/// `layer` is the backend's representation of `F carrier`. `roll` and
/// `unroll` respectively represent `F carrier → carrier` and
/// `carrier → F carrier`. The facts make the isomorphism proof-bearing
/// rather than a convention hidden inside a backend-specific value.
pub struct FixpointCore<L: Logic, P> {
    /// The exact checked functor declaration.
    pub spec: Validated<FixpointSpec<P>>,
    /// The fixpoint carrier.
    pub carrier: L::Type,
    /// The instantiated layer type `F carrier`.
    pub layer: L::Type,
    /// `F carrier → carrier`.
    pub roll: L::Term,
    /// `carrier → F carrier`.
    pub unroll: L::Term,
    /// Inverse laws.
    pub facts: Box<dyn FixpointIsoFacts<L>>,
}

/// Proof that `roll` and `unroll` are mutually inverse.
pub trait FixpointIsoFacts<L: Logic> {
    /// `⊢ roll (unroll x) = x`.
    fn roll_unroll(&self, x: &L::Term) -> Result<L::Thm, L::Error>;
    /// `⊢ unroll (roll layer) = layer`.
    fn unroll_roll(&self, layer: &L::Term) -> Result<L::Thm, L::Error>;
}

/// Proof-bearing least-fixpoint realization.
pub struct LeastFixpoint<L: Logic, P> {
    /// Shared fixpoint carrier and Lambek isomorphism.
    pub core: FixpointCore<L, P>,
    /// Iteration and induction laws.
    pub facts: Box<dyn LeastFixpointFacts<L>>,
}

/// Optional constructor no-confusion evidence for a least fixpoint.
///
/// This is deliberately not a field of [`LeastFixpoint`]: Lambek's
/// isomorphism and induction do not by themselves promise that a backend can
/// expose constructor injectivity or distinctness in its object logic.
/// Backends attach this stronger bundle only when they can prove it.
pub struct NoConfusionLeastFixpoint<L: Logic, P> {
    /// The underlying least-fixpoint realization.
    pub fixpoint: LeastFixpoint<L, P>,
    /// Constructor distinctness and injectivity laws.
    pub no_confusion: Box<dyn FixpointNoConfusionFacts<L>>,
}

/// Constructor no-confusion laws indexed by the checked polynomial.
///
/// Case and field positions are declaration-order positions in
/// [`FixpointCore::spec`]. Both methods return closed implications in the
/// backend's logic; they do not accept an equality theorem as an unchecked
/// Rust-level premise.
pub trait FixpointNoConfusionFacts<L: Logic> {
    /// `⊢ (Cᵢ left = Cᵢ right) ⟹ left[field] = right[field]`.
    fn injective(
        &self,
        case: usize,
        field: usize,
        left: &[L::Term],
        right: &[L::Term],
    ) -> Result<L::Thm, L::Error>;

    /// `⊢ (Cᵢ left = Cⱼ right) ⟹ F`, for distinct `i` and `j`.
    fn distinct(
        &self,
        left_case: usize,
        right_case: usize,
        left: &[L::Term],
        right: &[L::Term],
    ) -> Result<L::Thm, L::Error>;
}

/// Catamorphism and induction capabilities of a least fixpoint.
pub trait LeastFixpointFacts<L: Logic> {
    /// Build `fold algebra : μF → A`.
    fn fold(&self, algebra: &L::Term) -> Result<L::Term, L::Error>;

    /// Constructor/fusion computation law:
    /// `⊢ fold algebra (roll layer) = algebra (map (fold algebra) layer)`.
    fn fold_roll(&self, algebra: &L::Term, layer: &L::Term) -> Result<L::Thm, L::Error>;

    /// Structural induction. `closed` proves that the predicate is preserved
    /// by one functor layer; the result is the predicate for every carrier
    /// value. The logic-specific bundle determines the exact encoding of the
    /// predicate and layer premise.
    fn induction(&self, predicate: &L::Term, closed: L::Thm) -> Result<L::Thm, L::Error>;
}

/// Proof-bearing greatest-fixpoint realization.
pub struct GreatestFixpoint<L: Logic, P> {
    /// Shared fixpoint carrier and Lambek isomorphism.
    pub core: FixpointCore<L, P>,
    /// Coiteration and coinduction laws.
    pub facts: Box<dyn GreatestFixpointFacts<L>>,
}

/// Anamorphism and coinduction capabilities of a greatest fixpoint.
pub trait GreatestFixpointFacts<L: Logic> {
    /// Build `unfold coalgebra : A → νF`.
    fn unfold(&self, coalgebra: &L::Term) -> Result<L::Term, L::Error>;

    /// Destructor computation law:
    /// `⊢ unroll (unfold coalgebra seed) =
    ///     map (unfold coalgebra) (coalgebra seed)`.
    fn unroll_unfold(&self, coalgebra: &L::Term, seed: &L::Term) -> Result<L::Thm, L::Error>;

    /// Bisimulation/coinduction. `preserved` proves the relation is preserved
    /// by one observation layer; the result identifies related carriers.
    fn coinduction(&self, relation: &L::Term, preserved: L::Thm) -> Result<L::Thm, L::Error>;
}

/// Backend implementing the shared proof-bearing least-fixpoint contract.
///
/// Implementing this trait is stronger than the compatibility
/// [`InductiveFixpointBackend`]: it requires the Lambek isomorphism, fold,
/// induction, and their computation laws.
pub trait ProofBearingLeastFixpointBackend<L: Logic, P> {
    /// Backend error.
    type Error;
    /// Realize a checked `μF`.
    fn realize_least(
        &self,
        spec: &Validated<FixpointSpec<P>>,
    ) -> Result<LeastFixpoint<L, P>, Self::Error>;
}

/// Backend implementing the shared proof-bearing greatest-fixpoint contract.
pub trait ProofBearingGreatestFixpointBackend<L: Logic, P> {
    /// Backend error.
    type Error;
    /// Realize a checked `νF`.
    fn realize_greatest(
        &self,
        spec: &Validated<FixpointSpec<P>>,
    ) -> Result<GreatestFixpoint<L, P>, Self::Error>;
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
    fn realize_inductive(
        &self,
        spec: &Validated<FixpointSpec<P>>,
    ) -> Result<Self::Inductive, Self::Error>;
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
    fn realize_coinductive(
        &self,
        spec: &Validated<FixpointSpec<P>>,
    ) -> Result<Self::Coinductive, Self::Error>;
}

/// Validate before invoking an inductive backend.
pub fn realize_inductive<P: Clone, B: InductiveFixpointBackend<P>>(
    backend: &B,
    spec: &FixpointSpec<P>,
) -> Result<B::Inductive, RealizeError<B::Error>> {
    let spec = Validated::try_from(spec.clone()).map_err(RealizeError::Spec)?;
    backend
        .realize_inductive(&spec)
        .map_err(RealizeError::Backend)
}

/// Validate before invoking a coinductive backend.
pub fn realize_coinductive<P: Clone, B: CoinductiveFixpointBackend<P>>(
    backend: &B,
    spec: &FixpointSpec<P>,
) -> Result<B::Coinductive, RealizeError<B::Error>> {
    let spec = Validated::try_from(spec.clone()).map_err(RealizeError::Spec)?;
    backend
        .realize_coinductive(&spec)
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
    use std::cell::Cell;

    use super::*;
    use crate::polynomial::{FieldSpec, Position, VariantCase};

    struct Names {
        calls: Cell<usize>,
    }

    impl InductiveFixpointBackend<&'static str> for Names {
        type Inductive = String;
        type Error = &'static str;

        fn realize_inductive(
            &self,
            spec: &Validated<FixpointSpec<&'static str>>,
        ) -> Result<Self::Inductive, Self::Error> {
            self.calls.set(self.calls.get() + 1);
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
        let backend = Names {
            calls: Cell::new(0),
        };
        assert_eq!(realize_inductive(&backend, &list).unwrap(), "mu list");
        assert_eq!(backend.calls.get(), 1);

        let malformed = FixpointSpec::new("", PolynomialSpec::<&str>::new("f", vec![]));
        assert!(matches!(
            realize_inductive(&backend, &malformed),
            Err(RealizeError::Spec(SpecError::EmptyTypeName))
        ));
        assert_eq!(backend.calls.get(), 1, "invalid input reached the backend");
    }
}
