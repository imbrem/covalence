use typed_generational_arena::{SmallArena, SmallIndex};

use covalence_data::fact::{Pred0, Pred1};
use covalence_data::store::*;
use covalence_data::term::*;

mod ctx;
use ctx::*;

pub use ctx::{NodeIx, TermId};

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CtxId(SmallIndex<Ctx>);

pub type ValId = covalence_data::store::ValId<TermDb>;

pub type FvId = covalence_data::store::FvId<TermDb>;

/// A term store implemented using `egg`
#[derive(Debug, Clone, Default)]
pub struct TermDb {
    pub(crate) x: SmallArena<Ctx>,
}

impl TermDb {
    /// Construct a new, empty term database
    pub fn new() -> TermDb {
        TermDb::default()
    }

    fn set_this(&mut self, ctx: CtxId) {
        self.x[ctx.0].set_this(ctx);
    }
}

impl TermIndex for TermDb {
    type CtxId = CtxId;
    type TermId = TermId;
}

impl ReadLocalTerm for TermDb {
    fn val(&self, ctx: CtxId, tm: TermId) -> ValId {
        match self.node(ctx, tm) {
            NodeIx::Import(val) => self.val(val.ctx, val.tm),
            _ => Val { ctx, tm },
        }
    }

    fn node(&self, ctx: CtxId, tm: TermId) -> &NodeIx {
        self.x[ctx.0].node(tm)
    }

    fn lookup(&self, ctx: CtxId, tm: NodeIx) -> Option<TermId> {
        self.x[ctx.0].lookup(tm)
    }

    fn lookup_import(&self, ctx: CtxId, val: ValId) -> Option<TermId> {
        // NOTE: an import cycle will lead to a stack overflow here, but that should be an error But
        // think about it!
        //
        // We could try a cycle detection algorithm and return `Invalid`, if we want to be very
        // clever... but again, this is a deeply invalid state, since import destinations should
        // _not_ be mutable, and we can't get the `TermId` of an import without synthesizing an
        // invalid one (which is unspecified behaviour, but should not cause unsoundness) before
        // inserting the import and hence fixing the `TermId`.
        if let NodeIx::Import(imp) = self.node(val.ctx, val.tm) {
            self.lookup_import(ctx, *imp)
        } else if ctx == val.ctx {
            Some(val.tm)
        } else {
            self.x[ctx.0].lookup(NodeT::Import(val))
        }
    }

    fn bvi(&self, ctx: CtxId, tm: TermId) -> Bv {
        //TODO: compute the bvi if invalid
        self.x[ctx.0].bvi(tm)
    }

    fn deref_eq(&self, lhs: Val<CtxId, TermId>, rhs: Val<CtxId, TermId>) -> bool {
        lhs == rhs || self.val(lhs.ctx, lhs.tm) == self.val(rhs.ctx, rhs.tm)
    }

    fn cons_eq(&self, lhs: ValId, rhs: ValId) -> bool {
        if lhs == rhs {
            return true;
        }
        lhs.node_val(self) == rhs.node_val(self)
    }
}

impl ReadUniv for TermDb {
    fn u_le(&self, lo: ULvl, hi: ULvl) -> bool {
        match (lo.as_const(), hi.as_const()) {
            (Some(0), _) => true,
            (Some(lo), Some(hi)) => lo <= hi,
            _ => lo == hi,
        }
    }

    fn u_lt(&self, lo: ULvl, hi: ULvl) -> bool {
        match (lo.as_const(), hi.as_const()) {
            (Some(lo), Some(hi)) => lo < hi,
            _ => false,
        }
    }

    fn imax_le(&self, lo_lhs: ULvl, lo_rhs: ULvl, hi: ULvl) -> bool {
        self.u_le(lo_rhs, ULvl::PROP) || self.u_le(lo_lhs, hi) && self.u_le(lo_rhs, hi)
    }
}

impl WriteLocalTerm for TermDb {
    fn new_ctx(&mut self) -> CtxId {
        let result = CtxId(self.x.insert(Ctx::new_ctx()));
        self.set_this(result);
        result
    }

    fn with_parent(&mut self, parent: CtxId) -> CtxId {
        debug_assert!(self.x.contains(parent.0));
        let result = CtxId(self.x.insert(Ctx::with_parent(parent)));
        self.set_this(result);
        result
    }

    fn add_raw(&mut self, ctx: CtxId, tm: NodeIx) -> TermId {
        self.x[ctx.0].add(tm)
    }

    fn import(&mut self, ctx: CtxId, val: ValId) -> TermId {
        // NOTE: an import cycle will lead to a stack overflow here, but that should be an error But
        // think about it!
        //
        // We could try a cycle detection algorithm and return `Invalid`, if we want to be very
        // clever... but again, this is a deeply invalid state, since import destinations should
        // _not_ be mutable, and we can't get the `TermId` of an import without synthesizing an
        // invalid one (which is unspecified behaviour, but should not cause unsoundness) before
        // inserting the import and hence fixing the `TermId`.
        let result = if let NodeIx::Import(imp) = self.node(val.ctx, val.tm) {
            self.import(ctx, *imp)
        } else if ctx == val.ctx {
            return val.tm;
        } else {
            self.x[ctx.0].add(NodeT::Import(val))
        };
        let bvi = self.bvi(val.ctx, val.tm);
        self.set_bvi_unchecked(ctx, result, bvi);
        result
    }

    fn propagate_in(&mut self, ctx: CtxId) -> usize {
        self.x[ctx.0].propagate_in()
    }
}

impl WriteUniv for TermDb {
    fn succ(&mut self, level: ULvl) -> ULvl {
        if let Some(level) = level.as_const() {
            ULvl::of_nat(level + 1)
        } else {
            panic!("universe variables not implemented")
        }
    }

    fn umax(&mut self, lhs: ULvl, rhs: ULvl) -> ULvl {
        match (lhs.as_const(), rhs.as_const()) {
            (Some(0), _) => rhs,
            (_, Some(0)) => lhs,
            (Some(l), Some(r)) => ULvl::of_nat(l.max(r)),
            _ => panic!("universe variables not implemented"),
        }
    }

    fn imax(&mut self, lhs: ULvl, rhs: ULvl) -> ULvl {
        match (lhs.as_const(), rhs.as_const()) {
            (Some(0), _) => rhs,
            (_, Some(0)) => ULvl::PROP,
            (Some(l), Some(r)) => ULvl::of_nat(l.max(r)),
            _ => panic!("universe variables not implemented"),
        }
    }
}

impl ReadCtx<CtxId, TermId> for TermDb {
    fn num_vars(&self, ctx: CtxId) -> u32 {
        self.x[ctx.0].num_vars()
    }

    fn var_ty(&self, var: FvId) -> ValId {
        self.x[var.ctx.0]
            .var_ty(var.ix)
            .expect("invalid variable index")
    }
}

impl ReadCtxFacts<CtxId> for TermDb {
    fn ctx_satisfies(&self, ctx: CtxId, pred: Pred0) -> bool {
        self.x[ctx.0].nullary().contains(pred)
    }
}

impl ReadCtxRel<CtxId> for TermDb {
    fn is_root(&self, ctx: CtxId) -> bool {
        //TODO: optimize
        self.x[ctx.0].is_null_extension() && self.x[ctx.0].parent().is_none_or(|p| self.is_root(p))
    }

    fn is_ancestor(&self, lo: CtxId, mut hi: CtxId) -> bool {
        while lo != hi {
            hi = if let Some(parent) = self.x[hi.0].parent() {
                parent
            } else {
                return false;
            }
        }
        true
    }

    fn is_strict_ancestor(&self, lo: CtxId, hi: CtxId) -> bool {
        lo != hi && self.is_ancestor(lo, hi)
    }

    fn is_subctx(&self, mut lo: CtxId, hi: CtxId) -> bool {
        while self.x[lo.0].is_null_extension() {
            if let Some(parent) = self.x[lo.0].parent() {
                lo = parent;
            } else {
                return true;
            }
        }
        self.is_ancestor(lo, hi)
    }

    fn is_subctx_of_parents(&self, lo: CtxId, hi: CtxId) -> bool {
        if let Some(parent) = self.x[hi.0].parent() {
            self.is_subctx(lo, parent)
        } else {
            self.is_root(lo)
        }
    }

    fn parents_are_subctx(&self, lo: CtxId, hi: CtxId) -> bool {
        if let Some(parent) = self.x[lo.0].parent() {
            self.is_subctx(parent, hi)
        } else {
            true
        }
    }
}

impl ReadLocalFacts for TermDb {
    fn local_tm_flags(&self, ctx: CtxId, tm: TermId) -> Pred1 {
        self.x[ctx.0].tm_flags(tm)
    }

    fn local_eq(&self, ctx: CtxId, lhs: TermId, rhs: TermId) -> bool {
        self.x[ctx.0].eq_in(lhs, rhs)
    }
}

impl ReadTermFacts<CtxId, TermId> for TermDb {
    fn tm_flags(&self, ctx: CtxId, tm: TermId) -> Pred1 {
        self.x[ctx.0].tm_flags(tm)
    }

    fn eq_in(&self, ctx: CtxId, lhs: TermId, rhs: TermId) -> bool {
        self.x[ctx.0].eq_in(lhs, rhs)
    }

    fn has_ty(&self, ctx: CtxId, tm: TermId, ty: TermId) -> bool {
        self.x[ctx.0].has_ty(tm, ty)
    }
}

impl ReadQuantFacts<CtxId, TermId> for TermDb {
    fn forall_eq_in(&self, ctx: CtxId, binder: TermId, lhs: TermId, rhs: TermId) -> bool {
        if !self.is_ty(ctx, binder) {
            return false;
        }
        if self.eq_in(ctx, lhs, rhs) {
            return true;
        }
        let Some(abs_lhs) = self.lookup(ctx, NodeT::Abs([binder, lhs])) else {
            return false;
        };
        let Some(abs_rhs) = self.lookup(ctx, NodeT::Abs([binder, rhs])) else {
            return false;
        };
        self.eq_in(ctx, abs_lhs, abs_rhs)
    }

    fn forall_has_ty(&self, ctx: CtxId, binder: TermId, tm: TermId, ty: TermId) -> bool {
        if self.is_ty(ctx, binder) && self.has_ty(ctx, tm, ty) {
            return true;
        }
        let Some(abs) = self.lookup(ctx, NodeT::Abs([binder, tm])) else {
            return false;
        };
        let Some(pi) = self.lookup(ctx, NodeT::Pi([binder, ty])) else {
            return false;
        };
        self.has_ty(ctx, abs, pi)
    }

    fn forall_is_wf(&self, ctx: CtxId, binder: TermId, tm: TermId) -> bool {
        if !self.is_ty(ctx, binder) {
            return false;
        }
        self.is_wf(ctx, tm)
            || self
                .lookup(ctx, NodeT::Abs([binder, tm]))
                .is_some_and(|abs| self.is_wf(ctx, abs))
    }

    fn forall_is_ty(&self, ctx: CtxId, binder: TermId, tm: TermId) -> bool {
        if !self.is_ty(ctx, binder) {
            return false;
        }
        self.is_ty(ctx, tm)
            || (self.is_wf(ctx, tm) && self.is_empty(ctx, binder))
            || self
                .lookup(ctx, NodeT::Pi([binder, tm]))
                .is_some_and(|pi| self.is_ty(ctx, pi))
    }

    fn forall_is_prop(&self, ctx: CtxId, binder: TermId, tm: TermId) -> bool {
        if !self.is_ty(ctx, binder) {
            return false;
        }
        self.is_prop(ctx, tm)
            || (self.is_wf(ctx, tm) && self.is_empty(ctx, binder))
            || self
                .lookup(ctx, NodeT::Pi([binder, tm]))
                .is_some_and(|pi| self.is_prop(ctx, pi))
    }

    fn forall_is_inhab(&self, ctx: CtxId, binder: TermId, tm: TermId) -> bool {
        if !self.is_ty(ctx, binder) {
            return false;
        }
        self.is_inhab(ctx, tm)
            || (self.is_wf(ctx, tm) && self.is_empty(ctx, binder))
            || self.eq_in(ctx, tm, binder)
            || self
                .lookup(ctx, NodeT::Pi([binder, tm]))
                .is_some_and(|pi| self.is_inhab(ctx, pi))
    }

    fn forall_is_tt(&self, ctx: CtxId, binder: TermId, tm: TermId) -> bool {
        if !self.is_ty(ctx, binder) {
            return false;
        }
        self.is_tt(ctx, tm)
            || (self.is_wf(ctx, tm) && self.is_empty(ctx, binder))
            || (self.is_prop(ctx, binder) && self.eq_in(ctx, tm, binder))
            || self
                .lookup(ctx, NodeT::Pi([binder, tm]))
                .is_some_and(|pi| self.is_tt(ctx, pi))
    }

    fn forall_is_empty(&self, ctx: CtxId, binder: TermId, tm: TermId) -> bool {
        if !self.is_ty(ctx, binder) {
            return false;
        }
        self.is_empty(ctx, tm)
            || (self.is_wf(ctx, tm) && self.is_empty(ctx, binder))
            || self
                .lookup(ctx, NodeT::Sigma([binder, tm]))
                .is_some_and(|sigma| self.is_empty(ctx, sigma))
    }

    fn forall_is_ff(&self, ctx: CtxId, binder: TermId, tm: TermId) -> bool {
        self.forall_is_prop(ctx, binder, tm) && self.forall_is_empty(ctx, binder, tm)
    }

    fn forall_is_contr(&self, ctx: CtxId, binder: TermId, tm: TermId) -> bool {
        self.is_empty(ctx, binder) && self.forall_is_wf(ctx, binder, tm)
    }
}

impl ReadTermDb<CtxId, TermId> for TermDb {
    type Reader = TermDb;

    fn read(&self) -> &Self::Reader {
        self
    }
}

impl WriteFacts<CtxId, TermId> for TermDb {
    fn set_tm_flags_unchecked(&mut self, ctx: CtxId, tm: TermId, pred: Pred1) {
        self.x[ctx.0].set_flags_unchecked(tm, pred);
    }

    fn set_is_contr_unchecked(&mut self, ctx: CtxId) {
        self.x[ctx.0].set_is_contr();
    }

    fn set_parent_unchecked(&mut self, ctx: CtxId, parent: CtxId) {
        self.x[ctx.0].set_parent_unchecked(parent);
    }

    fn set_eq_unchecked(&mut self, ctx: CtxId, lhs: TermId, rhs: TermId) {
        self.x[ctx.0].set_eq_unchecked(lhs, rhs);
    }

    fn set_has_ty_unchecked(&mut self, ctx: CtxId, tm: TermId, ty: TermId) {
        self.x[ctx.0].set_has_ty_unchecked(tm, ty);
    }

    fn set_forall_eq_unchecked(&mut self, ctx: CtxId, binder: TermId, lhs: TermId, rhs: TermId) {
        self.x[ctx.0].set_forall_eq_unchecked(binder, lhs, rhs);
    }

    fn set_forall_is_wf_unchecked(&mut self, ctx: CtxId, binder: TermId, tm: TermId) {
        self.x[ctx.0].set_forall_is_wf_unchecked(binder, tm);
    }

    fn set_forall_is_ty_unchecked(&mut self, ctx: CtxId, binder: TermId, tm: TermId) {
        self.x[ctx.0].set_forall_is_ty_unchecked(binder, tm);
    }

    fn set_forall_is_prop_unchecked(&mut self, ctx: CtxId, binder: TermId, tm: TermId) {
        self.x[ctx.0].set_forall_is_prop_unchecked(binder, tm);
    }

    fn set_forall_has_ty_unchecked(&mut self, ctx: CtxId, binder: TermId, tm: TermId, ty: TermId) {
        self.x[ctx.0].set_forall_has_ty_unchecked(binder, tm, ty);
    }

    fn set_forall_is_inhab_unchecked(&mut self, ctx: CtxId, binder: TermId, ty: TermId) {
        self.x[ctx.0].set_forall_is_inhab_unchecked(binder, ty);
    }

    fn set_forall_is_empty_unchecked(&mut self, ctx: CtxId, binder: TermId, tm: TermId) {
        self.x[ctx.0].set_forall_is_empty_unchecked(binder, tm);
    }

    fn set_exists_is_inhab_unchecked(&mut self, ctx: CtxId, binder: TermId, ty: TermId) {
        self.x[ctx.0].set_exists_is_inhab_unchecked(binder, ty);
    }

    fn add_var_unchecked(&mut self, ctx: CtxId, ty: ValId) -> FvId {
        self.x[ctx.0].add_var_unchecked(ctx, ty)
    }

    fn set_bvi_unchecked(&mut self, ctx: CtxId, tm: TermId, bvi: Bv) {
        self.x[ctx.0].set_bvi_unchecked(tm, bvi);
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn basic_imax_le() {
        let db = TermDb::default();
        let u0 = ULvl::PROP;
        assert!(db.imax_le(u0, u0, u0));
        let u1 = ULvl::SET;
        assert!(db.imax_le(u1, u1, u1));
        assert!(db.imax_le(u1, u0, u1));
        assert!(db.imax_le(u0, u1, u1));
        assert!(db.imax_le(u0, u0, u1));
        assert!(!db.imax_le(u1, u1, u0));
        assert!(db.imax_le(u1, u0, u0));
        assert!(!db.imax_le(u0, u1, u0));
    }
}
