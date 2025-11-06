/*!
The `covalence` kernel, parametrized by a datastore `D`
*/
use crate::{data::term::*, store::*};

pub mod data;
pub mod fact;
pub mod store;
pub mod univ;

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
pub struct Kernel<D>(D);

impl<D: TermIndex> TermIndex for Kernel<D> {
    type CtxId = D::CtxId;
    type Ix = D::Ix;
}

impl<D: ReadLocalTerm> ReadLocalTerm for Kernel<D> {
    fn node(&self, ctx: CtxId<D>, tm: Ix<D>) -> &NodeIx<D> {
        self.0.node(ctx, tm)
    }

    fn lookup(&self, ctx: CtxId<D>, tm: NodeIx<D>) -> Option<Ix<D>> {
        self.0.lookup(ctx, tm)
    }

    fn lookup_import(&self, ctx: CtxId<D>, tm: TmId<D>) -> Option<Ix<D>> {
        self.0.lookup_import(ctx, tm)
    }

    fn local_bvi(&self, ctx: CtxId<D>, tm: Ix<D>) -> Bv {
        self.0.local_bvi(ctx, tm)
    }

    fn local_may_have_var(&self, ctx: CtxId<D>, tm: Ix<D>, var: FvId<D>) -> bool {
        self.0.local_may_have_var_from(ctx, tm, var.ctx)
    }

    fn local_may_have_var_from(&self, ctx: CtxId<D>, tm: Ix<D>, vars: CtxId<D>) -> bool {
        self.0.local_may_have_var_from(ctx, tm, vars)
    }
}

impl<D: WriteLocalTerm> WriteLocalTerm for Kernel<D> {
    fn new_ctx(&mut self) -> CtxId<D> {
        self.0.new_ctx()
    }

    fn cons_node_ix(&mut self, ctx: CtxId<Self>, tm: NodeIx<Self>) -> Ix<Self> {
        self.0.cons_node_ix(ctx, tm)
    }

    fn propagate_in(&mut self, ctx: CtxId<Self>) -> usize {
        self.0.propagate_in(ctx)
    }
}

impl<D: ReadUniv> ReadUniv for Kernel<D> {
    fn u_le(&self, lo: ULvl, hi: ULvl) -> bool {
        self.0.u_le(lo, hi)
    }

    fn u_lt(&self, lo: ULvl, hi: ULvl) -> bool {
        self.0.u_lt(lo, hi)
    }

    fn imax_le(&self, lo_lhs: ULvl, lo_rhs: ULvl, hi: ULvl) -> bool {
        self.0.imax_le(lo_lhs, lo_rhs, hi)
    }
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

impl<C, T, D: ReadCtx<C, T>> ReadCtx<C, T> for Kernel<D> {
    fn num_vars(&self, ctx: C) -> u32 {
        self.0.num_vars(ctx)
    }

    fn var_ty(&self, var: Fv<C>) -> T {
        self.0.var_ty(var)
    }
}
