use crate::{
    fact::{Eqn, HasTy, Holds, IsEmpty, IsFalse, IsInhab, IsProp, IsTrue, IsTy, IsWf, Seq},
    store::TermIndex,
};

/// Stable facts are sealed
pub(crate) mod stable_facts_sealed {
    pub trait StableFactSealed {}

    pub trait StableFactCtxSealed<D> {}
}

use either::Either;
pub(crate) use stable_facts_sealed::{StableFactCtxSealed, StableFactSealed};

/// A stable fact is one which will stay true as the kernel evolves
pub trait StableFact: StableFactSealed {}

/// A fact-in-context is stable under weakening if it remains true when the context is weakened
pub trait StableUnderWkn: StableFactSealed {}

/// A stable fact context is one for which facts will stay true as the kernel evolves
///
/// Note the context _itself_ may change, e.g. by adding (but not removing!) variables
pub trait StableFactCtx<D>: StableFactCtxSealed<D> {}

impl StableFactSealed for () {}

impl StableFactSealed for bool {}

impl<A: StableFactSealed, B: StableFactSealed> StableFactSealed for (A, B) {}

impl<A: StableFactSealed, B: StableFactSealed> StableFactSealed for Either<A, B> {}

impl<R: TermIndex> StableFactCtxSealed<R> for R::CtxId {}

impl<C: StableFactCtxSealed<Self>, F: StableFactSealed> StableFactSealed for Seq<C, F> {}

impl<L, R> StableFactSealed for HasTy<L, R> {}

impl<L, R> StableFactSealed for Eqn<L, R> {}

impl<T> StableFactSealed for Holds<T> {}

impl<T> StableFactSealed for IsTy<T> {}

impl<T> StableFactSealed for IsWf<T> {}

impl<T> StableFactSealed for IsInhab<T> {}

impl<T> StableFactSealed for IsEmpty<T> {}

impl<T> StableFactSealed for IsProp<T> {}

impl<T> StableFactSealed for IsTrue<T> {}

impl<T> StableFactSealed for IsFalse<T> {}

impl StableFact for () {}

impl StableFact for bool {}

impl<A: StableFact, B: StableFact> StableFact for (A, B) {}

impl<A: StableFact, B: StableFact> StableFact for Either<A, B> {}

impl<R: TermIndex> StableFactCtx<R> for R::CtxId {}

impl<C: StableFactCtx<Self>, F: StableUnderWkn> StableFact for Seq<C, F> {}

impl<L, R> StableUnderWkn for HasTy<L, R> {}

impl<L, R> StableUnderWkn for Eqn<L, R> {}

impl<T> StableUnderWkn for Holds<T> {}

impl<T> StableUnderWkn for IsTy<T> {}

impl<T> StableUnderWkn for IsWf<T> {}

impl<T> StableUnderWkn for IsInhab<T> {}

impl<T> StableUnderWkn for IsEmpty<T> {}

impl<T> StableUnderWkn for IsProp<T> {}

impl<T> StableUnderWkn for IsTrue<T> {}

impl<T> StableUnderWkn for IsFalse<T> {}
