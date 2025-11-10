use crate::{
    fact::{Eqn, HasTy, Holds, IntoPred1, Is, Pred0, Seq},
    store::{Ctx, LocalTerm},
};

/// Stable facts are sealed
pub(crate) mod stable_facts_sealed {
    pub trait StableFactSealed<D> {}

    pub trait StableFactInSealed<C, D> {}
}

use either::Either;
pub(crate) use stable_facts_sealed::{StableFactInSealed, StableFactSealed};

/// A stable fact is one which will stay true as the kernel evolves
pub trait StableFact<D>: StableFactSealed<D> {}

/// A fact is stable in a context if it remains true as that context evolves
pub trait StableFactIn<C, D>: StableFactInSealed<C, D> {}

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

impl<D, C: Ctx<D>, L: LocalTerm<C, D>, R: LocalTerm<C, D>> StableFactIn<C, D> for Eqn<L, R> {}

impl<D, C: Ctx<D>, L: LocalTerm<C, D>, R: LocalTerm<C, D>> StableFactIn<C, D> for HasTy<L, R> {}

impl<D, P: IntoPred1, C: Ctx<D>, T: LocalTerm<C, D>> StableFactIn<C, D> for Is<P, T> {}

impl<D> StableFactSealed<D> for () {}

impl<D, C: Ctx<D>> StableFactInSealed<C, D> for () {}

impl<D> StableFactSealed<D> for bool {}

impl<D, C: Ctx<D>> StableFactInSealed<C, D> for bool {}

impl<D, A: StableFactSealed<D>, B: StableFactSealed<D>> StableFactSealed<D> for (A, B) {}

impl<D, C: Ctx<D>, A: StableFactInSealed<C, D>, B: StableFactInSealed<C, D>>
    StableFactInSealed<C, D> for (A, B)
{
}

impl<D, A: StableFactSealed<D>, B: StableFactSealed<D>> StableFactSealed<D> for Either<A, B> {}

impl<D, C: Ctx<D>, A: StableFactInSealed<C, D>, B: StableFactInSealed<C, D>>
    StableFactInSealed<C, D> for Either<A, B>
{
}

impl<D, C: Ctx<D>, F: StableFactInSealed<C, D>> StableFactSealed<D> for Seq<C, F> {}

impl<D, C: Ctx<D>> StableFactInSealed<C, D> for Pred0 {}

impl<D, C: Ctx<D>, T: LocalTerm<C, D>> StableFactInSealed<C, D> for Holds<T> {}

impl<D, C: Ctx<D>, L: LocalTerm<C, D>, R: LocalTerm<C, D>> StableFactInSealed<C, D> for Eqn<L, R> {}

impl<D, C: Ctx<D>, L: LocalTerm<C, D>, R: LocalTerm<C, D>> StableFactInSealed<C, D>
    for HasTy<L, R>
{
}

impl<D, P: IntoPred1, C: Ctx<D>, T: LocalTerm<C, D>> StableFactInSealed<C, D> for Is<P, T> {}
