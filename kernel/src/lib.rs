/*!
The `covalence` kernel, parametrized by a datastore `D`
*/
use std::ops::Deref;

use crate::{data::term::*, id::KernelId, store::*};

pub mod ctx;
pub mod data;
pub mod error;
pub mod fact;
pub mod id;
pub mod rule;
pub mod store;
pub mod theorem;
pub mod univ;
pub mod rw;

pub use theorem::Theorem;

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
pub struct Kernel<D> {
    /// The kernel's underlying term store
    db: D,
    /// This kernel's unique identifier
    id: KernelId,
}

impl<D> Kernel<D> {
    /// Get this kernel's unique identifier
    ///
    /// # Examples
    /// ```rust
    /// # use covalence::kernel::Kernel;
    /// let k1 = Kernel::default();
    /// let k2 = Kernel::default();
    /// assert_ne!(k1.id(), k2.id());
    /// ```
    pub fn id(&self) -> KernelId {
        self.id
    }
}

impl<D> Deref for Kernel<D> {
    type Target = D;

    fn deref(&self) -> &Self::Target {
        &self.db
    }
}

impl<D: TermIndex> TermStore for Kernel<D> {
    type Store = D;
}

impl<D: TermIndex + ReadLocalTerm<D>> ReadLocalTerm<D> for Kernel<D> {
    fn node(&self, ctx: CtxId<D>, tm: Ix<D>) -> NodeIx<D> {
        self.db.node(ctx, tm)
    }

    fn lookup(&self, ctx: CtxId<D>, tm: NodeIx<D>) -> Option<Ix<D>> {
        self.db.lookup(ctx, tm)
    }

    fn lookup_import(&self, ctx: CtxId<D>, tm: TmId<D>) -> Option<Ix<D>> {
        self.db.lookup_import(ctx, tm)
    }

    fn local_bvi(&self, ctx: CtxId<D>, tm: Ix<D>) -> Bv {
        self.db.local_bvi(ctx, tm)
    }

    fn local_may_have_var(&self, ctx: CtxId<D>, tm: Ix<D>, var: FvId<D>) -> bool {
        self.db.local_may_have_var_from(ctx, tm, var.ctx)
    }

    fn local_may_have_var_from(&self, ctx: CtxId<D>, tm: Ix<D>, vars: CtxId<D>) -> bool {
        self.db.local_may_have_var_from(ctx, tm, vars)
    }
}

impl<D: TermIndex + WriteLocalTerm<D>> WriteLocalTerm<D> for Kernel<D> {
    fn new_ctx(&mut self) -> CtxId<D> {
        self.db.new_ctx()
    }

    fn cons_node_ix(&mut self, ctx: CtxId<D>, tm: NodeIx<D>) -> Ix<D> {
        self.db.cons_node_ix(ctx, tm)
    }

    fn propagate_in(&mut self, ctx: CtxId<D>) -> usize {
        self.db.propagate_in(ctx)
    }
}

impl<D: ReadUniv> ReadUniv for Kernel<D> {
    fn u_le(&self, lo: ULvl, hi: ULvl) -> bool {
        self.db.u_le(lo, hi)
    }

    fn u_lt(&self, lo: ULvl, hi: ULvl) -> bool {
        self.db.u_lt(lo, hi)
    }

    fn imax_le(&self, lo_lhs: ULvl, lo_rhs: ULvl, hi: ULvl) -> bool {
        self.db.imax_le(lo_lhs, lo_rhs, hi)
    }
}

impl<D: WriteUniv> WriteUniv for Kernel<D> {
    fn succ(&mut self, level: ULvl) -> ULvl {
        self.db.succ(level)
    }

    fn umax(&mut self, lhs: ULvl, rhs: ULvl) -> ULvl {
        self.db.umax(lhs, rhs)
    }

    fn imax(&mut self, lhs: ULvl, rhs: ULvl) -> ULvl {
        self.db.imax(lhs, rhs)
    }
}

impl<C, D: ReadCtx<C>> ReadCtx<C> for Kernel<D> {
    type VarId = D::VarId;

    fn num_assumptions(&self, ctx: C) -> u32 {
        self.db.num_assumptions(ctx)
    }

    fn num_vars(&self, ctx: C) -> u32 {
        self.db.num_vars(ctx)
    }

    fn assumption(&self, ctx: C, ix: u32) -> D::VarId {
        self.db.assumption(ctx, ix)
    }

    fn var_ty(&self, var: Fv<C>) -> D::VarId {
        self.db.var_ty(var)
    }
}
