use crate::{fact::Seq, store::TermIndex};

/// Stable facts are sealed
pub(crate) mod stable_facts_sealed {
    pub trait StableFactSealed {}

    pub trait StableFactCtxSealed<D> {}
}

use either::Either;
pub(crate) use stable_facts_sealed::{StableFactCtxSealed, StableFactSealed};

/// A stable fact is one which will stay true as the kernel evolves
pub trait StableFact: StableFactSealed {}

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
