use crate::{
    fact::{Holds, IntoPred1, Is, Pred0, Rw, Seq},
    store::{Ctx, LocalTerm},
};

/// Stable facts are sealed
pub(crate) mod stable_facts_sealed {
    pub trait FactSealed<D> {}

    pub trait FactInSealed<C, D> {}
}

use either::Either;
pub(crate) use stable_facts_sealed::{FactInSealed, FactSealed};

/// A stable fact is one which will stay true as the kernel evolves
pub trait StableFact<D>: FactSealed<D> {}

/// A fact is stable in a context if it remains true as that context evolves
pub trait StableFactIn<C, D>: FactInSealed<C, D> {}

impl<D> StableFact<D> for () {}

impl<D, C: Ctx<D>> StableFactIn<C, D> for () {}

impl<D> StableFact<D> for bool {}

impl<D, C: Ctx<D>> StableFactIn<C, D> for bool {}

impl<D, A: StableFact<D>, B: StableFact<D>> StableFact<D> for (A, B) {}

impl<D, C: Ctx<D>, A: StableFactIn<C, D>, B: StableFactIn<C, D>> StableFactIn<C, D> for (A, B) {}

impl<D, A: StableFact<D>, B: StableFact<D>> StableFact<D> for Either<A, B> {}

impl<D, C: Ctx<D>, A: StableFactIn<C, D>, B: StableFactIn<C, D>> StableFactIn<C, D>
    for Either<A, B>
{
}

impl<D, C: Ctx<D>, F: StableFactIn<C, D>> StableFact<D> for Seq<C, F> {}

impl<D, C: Ctx<D>> StableFactIn<C, D> for Pred0 {}

impl<D, C: Ctx<D>, T: LocalTerm<C, D>> StableFactIn<C, D> for Holds<T> {}

impl<D, C: Ctx<D>, L: LocalTerm<C, D>, R: LocalTerm<C, D>> StableFactIn<C, D> for Rw<L, R> {}

impl<D, P: IntoPred1, C: Ctx<D>, T: LocalTerm<C, D>> StableFactIn<C, D> for Is<P, T> {}

impl<D> FactSealed<D> for () {}

impl<D, C: Ctx<D>> FactInSealed<C, D> for () {}

impl<D> FactSealed<D> for bool {}

impl<D, C: Ctx<D>> FactInSealed<C, D> for bool {}

impl<D, A: FactSealed<D>, B: FactSealed<D>> FactSealed<D> for (A, B) {}

impl<D, C: Ctx<D>, A: FactInSealed<C, D>, B: FactInSealed<C, D>> FactInSealed<C, D> for (A, B) {}

impl<D, A: FactSealed<D>, B: FactSealed<D>> FactSealed<D> for Either<A, B> {}

impl<D, C: Ctx<D>, A: FactInSealed<C, D>, B: FactInSealed<C, D>> FactInSealed<C, D>
    for Either<A, B>
{
}

impl<D, C: Ctx<D>, F: FactInSealed<C, D>> FactSealed<D> for Seq<C, F> {}

impl<D, C: Ctx<D>> FactInSealed<C, D> for Pred0 {}

impl<D, C: Ctx<D>, T: LocalTerm<C, D>> FactInSealed<C, D> for Holds<T> {}

impl<D, C: Ctx<D>, L: LocalTerm<C, D>, R: LocalTerm<C, D>> FactInSealed<C, D> for Rw<L, R> {}

impl<D, P: IntoPred1, C: Ctx<D>, T: LocalTerm<C, D>> FactInSealed<C, D> for Is<P, T> {}
