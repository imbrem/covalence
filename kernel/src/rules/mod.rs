use std::ops::Deref;

use crate::api::store::*;
use crate::data::term::ULvl;

/// Derivation rules for the `covalence` kernel
mod derive;

/// Rules for unfolding substitutions, imports, and closures
mod unfold;

/// Predicates which can be inferred from subterms
mod pred;

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

impl<D: IndexTypes> IndexTypes for Kernel<D> {
    type CtxId = D::CtxId;
    type TermId = D::TermId;
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

impl<D: WriteTermIndex> WriteTermIndex for Kernel<D> {
    fn new_ctx(&mut self) -> KCtxId<D> {
        self.0.new_ctx()
    }

    fn with_parent(&mut self, parent: KCtxId<D>) -> KCtxId<D> {
        self.0.with_parent(parent)
    }

    fn add_raw(&mut self, ctx: KCtxId<D>, term: KNodeIx<D>) -> KTermId<D> {
        self.0.add_raw(ctx, term)
    }

    fn import(&mut self, ctx: KCtxId<D>, val: KValId<D>) -> KTermId<D> {
        self.0.import(ctx, val)
    }

    fn propagate_in(&mut self, ctx: KCtxId<D>) -> usize {
        self.0.propagate_in(ctx)
    }
}
