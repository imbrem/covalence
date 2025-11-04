/*!
The `covalence` kernel, parametrized by a datastore `D`
*/

use std::ops::Deref;

use crate::data::term::ULvl;
use crate::store::*;

pub use covalence_data as data;
pub use covalence_data::store;

pub mod fact;
pub mod rule;
pub mod strategy;

// pub use crate::rule::ensure::{DeriveTrusted, WriteTrusted};
pub use crate::store::{
    ReadCtx, ReadCtxFacts, ReadCtxRel, ReadFacts, ReadLocalFacts, ReadLocalTerm, ReadQuantFacts,
    ReadTermDb, ReadTermFacts, ReadTermStore, WriteFacts, WriteLocalFactsUnchecked, WriteLocalTerm,
};
pub use covalence_data::univ::{ReadUniv, WriteUniv};

pub use covalence_data::fact::{
    IS_CONTR, IS_EMPTY, IS_FF, IS_INHAB, IS_PROP, IS_SCOPED, IS_TT, IS_TY, IS_UNIV, IS_WF, Pred1,
};

/// The `covalence` kernel
///
/// This type is parametrized by its datastore `D`
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
pub struct Kernel<D>(D);

impl<D> Kernel<D> {
    /// Get an _immutable_ reference to the underlying datastore
    pub fn data(&self) -> &D {
        &self.0
    }
}

impl<D> Deref for Kernel<D> {
    type Target = D;

    fn deref(&self) -> &D {
        &self.0
    }
}

impl<C, T, D: ReadTermDb<C, T>> ReadTermDb<C, T> for Kernel<D> {
    type Reader = D::Reader;

    fn read(&self) -> &Self::Reader {
        self.0.read()
    }
}

impl<D: TermIndex> TermIndex for Kernel<D> {
    type CtxId = D::CtxId;
    type Ix = D::Ix;
}

impl<D: WriteUniv> WriteUniv for Kernel<D> {
    fn succ(&mut self, level: ULvl) -> ULvl {
        self.0.succ(level)
    }

    fn umax(&mut self, lhs: ULvl, rhs: ULvl) -> ULvl {
        self.0.umax(lhs, rhs)
    }

    fn imax(&mut self, lhs: ULvl, rhs: ULvl) -> ULvl {
        self.0.imax(lhs, rhs)
    }
}

impl<D: WriteLocalTerm> WriteLocalTerm for Kernel<D> {
    fn new_ctx(&mut self) -> CtxId<D> {
        self.0.new_ctx()
    }

    fn with_parent(&mut self, parent: CtxId<D>) -> CtxId<D> {
        self.0.with_parent(parent)
    }

    fn add_raw(&mut self, ctx: CtxId<D>, term: NodeIx<D>) -> Ix<D> {
        self.0.add_raw(ctx, term)
    }

    fn import(&mut self, ctx: CtxId<D>, val: TermId<D>) -> Ix<D> {
        self.0.import(ctx, val)
    }

    fn propagate_in(&mut self, ctx: CtxId<D>) -> usize {
        self.0.propagate_in(ctx)
    }
}
