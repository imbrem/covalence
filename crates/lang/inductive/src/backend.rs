//! The **realization seam**: [`InductiveBackend`].

use crate::error::IndResult;
use crate::logic::Logic;
use crate::spec::InductiveSpec;
use crate::theory::InductiveTheory;

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
}
