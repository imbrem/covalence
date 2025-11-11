use crate::{fact::Seq, formula::StableFormula, store::Ctx};

/// Stable facts are sealed
pub(crate) mod stable_facts_sealed {
    pub trait FactSealed<D> {}
}

use either::Either;
pub(crate) use stable_facts_sealed::FactSealed;

/// A stable fact is one which will stay true as the kernel evolves
pub trait StableFact<D>: FactSealed<D> {}

impl<D> StableFact<D> for () {}

impl<D> StableFact<D> for bool {}

impl<D, A: StableFact<D>, B: StableFact<D>> StableFact<D> for (A, B) {}

impl<D, A: StableFact<D>, B: StableFact<D>> StableFact<D> for Either<A, B> {}

impl<D, C: Ctx<D>, F: StableFormula<C, D>> StableFact<D> for Seq<C, F> {}

impl<D> FactSealed<D> for () {}

impl<D> FactSealed<D> for bool {}

impl<D, A: FactSealed<D>, B: FactSealed<D>> FactSealed<D> for (A, B) {}

impl<D, A: FactSealed<D>, B: FactSealed<D>> FactSealed<D> for Either<A, B> {}

impl<D, C: Ctx<D>, F: StableFormula<C, D>> FactSealed<D> for Seq<C, F> {}
