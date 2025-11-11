use typed_generational_arena::{SmallArena, SmallIndex};

use covalence_kernel::data::term::*;
use covalence_kernel::fact::{CheckFactIn, Rw, Holds, Pred0, SetFactUncheckedIn, StoreFailure};
use covalence_kernel::store::*;

mod ctx;

use ctx::Ctx;

pub type CtxId = covalence_kernel::store::CtxId<TermDb>;

pub type Ix = covalence_kernel::store::Ix<TermDb>;

pub type NodeIx = covalence_kernel::store::NodeIx<TermDb>;

pub type TmId = covalence_kernel::store::TmId<TermDb>;

pub type FvId = covalence_kernel::store::FvId<TermDb>;

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
    type CtxId = SmallIndex<Ctx>;
    type Ix = u32;
}

impl ReadLocalTerm<TermDb> for TermDb {
    fn node(&self, ctx: CtxId, tm: Ix) -> NodeIx {
        self.x[ctx.0].node(tm)
    }

    fn lookup(&self, ctx: CtxId, tm: NodeIx) -> Option<Ix> {
        self.x[ctx.0].lookup(tm)
    }

    fn local_bvi(&self, ctx: CtxId, tm: Ix) -> Bv {
        //TODO: compute the bvi if invalid
        self.x[ctx.0].bvi(tm)
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

impl WriteLocalTerm<TermDb> for TermDb {
    fn new_ctx(&mut self) -> CtxId {
        let result = CtxId(self.x.insert(Ctx::new_ctx()));
        self.set_this(result);
        result
    }

    fn cons_node_ix(&mut self, ctx: CtxId, tm: NodeIx) -> Ix {
        let ix = self.x[ctx.0].add(tm);
        let bvi = match tm {
            Node::Quote(tm) => self.local_bvi(tm.ctx, tm.ix),
            tm => tm.bvi_with(|x| self.local_bvi(ctx, *x)),
        };
        self.x[ctx.0].set_bvi_unchecked(ix, bvi);
        ix
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

impl ReadCtx<CtxId> for TermDb {
    type VarId = TmId;

    fn num_assumptions(&self, ctx: CtxId) -> u32 {
        self.x[ctx.0].num_vars()
    }

    fn num_vars(&self, ctx: CtxId) -> u32 {
        self.x[ctx.0].num_vars()
    }

    fn var_ty(&self, var: FvId) -> TmId {
        self.x[var.ctx.0]
            .var_ty(var.ix)
            .expect("invalid variable index")
    }

    fn assumption(&self, ctx: CtxId, ix: u32) -> TmId {
        self.x[ctx.0].var_ty(ix).expect("invalid assumption index")
    }
}

impl ReadCtxGraph<CtxId> for TermDb {
    fn is_locally_empty(&self, ctx: CtxId) -> bool {
        self.x[ctx.0].is_locally_empty()
    }

    fn num_parents(&self, ctx: CtxId) -> u32 {
        self.x[ctx.0].num_parents()
    }

    fn parent(&self, ctx: CtxId, n: u32) -> Option<CtxId> {
        self.x[ctx.0].parent(n)
    }

    fn is_parent(&self, parent: CtxId, child: CtxId) -> bool {
        self.x[parent.0].is_parent(child)
    }
}

impl SealCtx<CtxId> for TermDb {
    fn seal_ctx_assumptions(&mut self, ctx: CtxId) {
        self.x[ctx.0].set_ctx_flags(Pred0::ASSUME_SEALED);
    }

    fn seal_ctx_parents(&mut self, ctx: CtxId) {
        self.x[ctx.0].set_ctx_flags(Pred0::PARENTS_SEALED);
    }

    fn seal_ctx_local(&mut self, ctx: CtxId) {
        self.x[ctx.0].set_ctx_flags(Pred0::LOCAL_SEALED);
    }

    fn seal_ctx_exts(&mut self, ctx: CtxId) {
        (0..self.num_parents(ctx)).for_each(|n| {
            self.parent(ctx, n).map(|p| self.seal_ctx(p));
        });
    }

    fn seal_ctx(&mut self, ctx: CtxId) {
        if self.x[ctx.0].ctx_flags().contains(Pred0::GLOBAL_SEALED) {
            return;
        }
        self.seal_ctx_exts(ctx);
        self.x[ctx.0].set_ctx_flags(Pred0::GLOBAL_SEALED);
    }
}

impl AddParentUnchecked<CtxId> for TermDb {
    fn add_parent_unchecked(&mut self, ctx: CtxId, parent: CtxId) -> Result<(), AddParentFailure> {
        self.x[ctx.0].add_parent_unchecked(parent)
    }
}

impl CheckFactIn<CtxId, Pred0> for TermDb {
    fn check_in(&self, ctx: CtxId, fact: &Pred0) -> bool {
        self.x[ctx.0].ctx_flags().contains(*fact)
    }
}

impl SetFactUncheckedIn<CtxId, Pred0> for TermDb {
    fn set_unchecked_in(&mut self, ctx: CtxId, fact: &Pred0) -> Result<(), StoreFailure> {
        self.x[ctx.0].set_ctx_flags(*fact);
        Ok(())
    }
}

impl CheckFactIn<CtxId, Holds<Ix>> for TermDb {
    fn check_in(&self, ctx: CtxId, fact: &Holds<Ix>) -> bool {
        self.x[ctx.0].tm_flags(fact.1).contains(fact.0)
    }
}

impl SetFactUncheckedIn<CtxId, Holds<Ix>> for TermDb {
    fn set_unchecked_in(&mut self, ctx: CtxId, fact: &Holds<Ix>) -> Result<(), StoreFailure> {
        self.x[ctx.0].set_tm_flags_unchecked(fact.1, fact.0);
        Ok(())
    }
}

impl CheckFactIn<CtxId, Rw<Ix>> for TermDb {
    fn check_in(&self, ctx: CtxId, fact: &Rw<Ix>) -> bool {
        self.x[ctx.0].eq_in(fact.0, fact.1)
    }
}

impl SetFactUncheckedIn<CtxId, Rw<Ix>> for TermDb {
    fn set_unchecked_in(&mut self, ctx: CtxId, fact: &Rw<Ix>) -> Result<(), StoreFailure> {
        self.x[ctx.0].set_eq_unchecked(fact.0, fact.1);
        Ok(())
    }
}

impl AddVarUnchecked<CtxId, TmId> for TermDb {
    fn add_var_unchecked(&mut self, ctx: CtxId, ty: TmId) -> Result<FvId, AddVarFailure> {
        self.x[ctx.0].add_var_unchecked(ctx, ty)
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
