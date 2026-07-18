//! The **realization seam**: [`InductiveBackend`].

use crate::error::IndResult;
use crate::logic::Logic;
use crate::spec::InductiveSpec;
use crate::theory::InductiveTheory;
use crate::validated::Validated;

// TODO(cov:inductive.legacy-fixpoint-adapter, major): Adapt InductiveTheory to LeastFixpoint when the logic API exposes polynomial functor action/map terms without representation-specific assumptions.

/// A way of realizing inductive specs in logic `L`.
///
/// **Swapping the backend within a logic** is the point: two values
/// implementing `InductiveBackend<HolLogic>` (say, an impredicative/Church
/// encoding and a typedef + recursion-theorem construction) both realize
/// the same spec; a consumer holds a `&dyn InductiveBackend<L>` (or is
/// generic over it), calls [`realize`](Self::realize), and works purely
/// through the [`InductiveTheory`] bundle — nothing in the consumer
/// mentions the representation.
///
/// A backend may **refuse** a spec (e.g. an adapter wrapping one already
/// carved type refuses others — [`crate::InductiveError::SpecMismatch`];
/// an encoding may not support some shape —
/// [`crate::InductiveError::Unsupported`]). Refusal is part of the honest
/// contract, never silent degradation.
pub trait InductiveBackend<L: Logic> {
    /// Realize a spec as a theory bundle in logic `L`.
    fn realize(&self, logic: &L, spec: &InductiveSpec<L::Type>)
    -> IndResult<InductiveTheory<L>, L>;

    /// Realize an already validated specification.
    ///
    /// This additive adapter lets existing backends retain their `realize`
    /// implementation while new consumers keep validation at the API
    /// boundary. A future backend API can make this the only entry point
    /// after legacy consumers migrate.
    fn realize_validated(
        &self,
        logic: &L,
        spec: &Validated<InductiveSpec<L::Type>>,
    ) -> IndResult<InductiveTheory<L>, L> {
        self.realize(logic, spec.as_inner())
    }
}
