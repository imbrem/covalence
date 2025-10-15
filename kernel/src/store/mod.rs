use typed_generational_arena::{SmallArena, SmallIndex};

use crate::{
    derive::*,
    term::{GNode, Gv, Import, ULvl},
};

mod ctx;
use ctx::*;

pub use ctx::{Node, TermId};

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CtxId(SmallIndex<Ctx>);

pub type VarId = Gv<CtxId>;

/// A term store implemented using `egg`
#[derive(Debug, Clone, Default)]
pub struct EggTermDb {
    pub(crate) x: SmallArena<Ctx>,
}

impl EggTermDb {
    fn set_this(&mut self, ctx: CtxId) {
        self.x[ctx.0].set_this(ctx);
    }
}

impl TermStore<CtxId, TermId> for EggTermDb {
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

    fn add(&mut self, ctx: CtxId, tm: Node) -> TermId {
        self.x[ctx.0].add(tm)
    }

    fn import(&mut self, ctx: CtxId, src: CtxId, tm: TermId) -> TermId {
        // NOTE: an import cycle will lead to a stack overflow here, but that should be an error But
        // think about it!
        //
        // We could try a cycle detection algorithm and return `Invalid`, if we want to be very
        // clever... but again, this is a deeply invalid state, since import destinations should
        // _not_ be mutable, and we can't get the `TermId` of an import without synthesizing an
        // invalid one (which is unspecified behaviour, but should not cause unsoundness) before
        // inserting the import and hence fixing the `TermId`.
        let bvi = self.bvi(src, tm);
        if let &Node::Import(Import {
            bvi: import_bvi,
            ctx: src,
            tm,
        }) = self.node(src, tm)
        {
            // For an import to be valid, `bvi` must be correct
            //
            // Otherwise, the import is potentially invalid, so we cannot recurse past it and must
            // instead just import it as itself.
            //
            // We can't require `bvi` to be an exact bound (so need import_bvi to be an upper bound)
            // since when we add `close` terms we don't want to bother computing whether we need to
            // bump the `bvi` or not, but this means the `bvi` can change (but only downwards!) as
            // we reduce `close` terms.
            if bvi <= import_bvi {
                return self.import(ctx, src, tm);
            }
        }
        if ctx == src {
            return tm;
        }
        self.x[ctx.0].add(GNode::Import(Import { bvi, ctx: src, tm }))
    }

    fn node(&self, ctx: CtxId, tm: TermId) -> &Node {
        self.x[ctx.0].node(tm)
    }

    fn lookup(&self, ctx: CtxId, tm: &mut Node) -> Option<TermId> {
        self.x[ctx.0].lookup(tm)
    }

    fn lookup_import(&self, ctx: CtxId, src: CtxId, tm: TermId) -> Option<TermId> {
        // NOTE: an import cycle will lead to a stack overflow here, but that should be an error But
        // think about it!
        //
        // We could try a cycle detection algorithm and return `Invalid`, if we want to be very
        // clever... but again, this is a deeply invalid state, since import destinations should
        // _not_ be mutable, and we can't get the `TermId` of an import without synthesizing an
        // invalid one (which is unspecified behaviour, but should not cause unsoundness) before
        // inserting the import and hence fixing the `TermId`.
        let bvi = self.bvi(src, tm);
        if let &Node::Import(Import {
            bvi: import_bvi,
            ctx: src,
            tm,
        }) = self.node(src, tm)
        {
            // For an import to be valid, `bvi` must be correct
            //
            // Otherwise, the import is potentially invalid, so we cannot recurse past it and must
            // instead just import it as itself.
            //
            // We can't require `bvi` to be an exact bound (so need import_bvi to be an upper bound)
            // since when we add `close` terms we don't want to bother computing whether we need to
            // bump the `bvi` or not, but this means the `bvi` can change (but only downwards!) as
            // we reduce `close` terms.
            if bvi <= import_bvi {
                if let Some(import) = self.lookup_import(ctx, src, tm) {
                    return Some(import);
                }
            }
        }
        if ctx == src {
            return Some(tm);
        }
        self.lookup(ctx, &mut GNode::Import(Import { bvi, ctx: src, tm }))
    }

    fn num_assumptions(&self, ctx: CtxId) -> usize {
        self.x[ctx.0].num_assumptions()
    }

    fn assumption(&self, ctx: CtxId, ix: usize) -> Option<TermId> {
        self.x[ctx.0].assumption(ix)
    }

    fn var_ty(&mut self, ctx: CtxId, var: VarId) -> TermId {
        let ty = self.get_var_ty(var);
        self.import(ctx, var.ctx, ty)
    }

    fn get_var_ty(&self, var: VarId) -> TermId {
        self.x[var.ctx.0]
            .var_ty(var.ix)
            .expect("invalid variable index")
    }

    fn succ(&mut self, level: ULvl) -> ULvl {
        //TODO: universe store and variables
        ULvl {
            level: level.level.checked_add(1).expect("universe level overflow"),
        }
    }

    fn umax(&mut self, lhs: ULvl, rhs: ULvl) -> ULvl {
        //TODO: universe store and variables
        ULvl {
            level: lhs.level.max(rhs.level),
        }
    }

    fn imax(&mut self, lhs: ULvl, rhs: ULvl) -> ULvl {
        //TODO: universe store and variables
        ULvl {
            level: if rhs.level == 0 {
                0
            } else {
                lhs.level.max(rhs.level)
            },
        }
    }

    fn propagate_in(&mut self, ctx: CtxId) -> usize {
        self.x[ctx.0].propagate_in()
    }
}

impl ReadFacts<CtxId, TermId> for EggTermDb {
    fn is_root(&self, ctx: CtxId) -> bool {
        //TODO: optimize
        self.x[ctx.0].is_null_extension() && self.parent(ctx).is_none_or(|p| self.is_root(p))
    }

    fn is_contr(&self, ctx: CtxId) -> bool {
        self.x[ctx.0].is_contr()
    }

    fn parent(&self, ctx: CtxId) -> Option<CtxId> {
        self.x[ctx.0].parent()
    }

    fn bvi(&self, ctx: CtxId, tm: TermId) -> crate::term::Bv {
        self.x[ctx.0].bvi(tm)
    }

    fn is_subctx(&self, lo: CtxId, mut hi: CtxId) -> bool {
        //TODO: optimize
        if self.is_root(lo) {
            return true;
        }
        while lo != hi {
            hi = if let Some(parent) = self.parent(hi) {
                parent
            } else {
                return false;
            }
        }
        true
    }

    fn is_subctx_of_parent(&self, lo: CtxId, hi: CtxId) -> bool {
        if self.is_root(lo) {
            return true;
        }
        if lo == hi {
            return false;
        }
        self.is_subctx(lo, hi)
    }

    fn is_wf(&self, ctx: CtxId, tm: TermId) -> bool {
        self.x[ctx.0].is_wf(tm)
    }

    fn is_ty(&self, ctx: CtxId, tm: TermId) -> bool {
        self.x[ctx.0].is_ty(tm)
    }

    fn is_inhab(&self, ctx: CtxId, tm: TermId) -> bool {
        self.x[ctx.0].is_inhab(tm)
    }

    fn is_empty(&self, ctx: CtxId, tm: TermId) -> bool {
        self.x[ctx.0].is_empty(tm)
    }

    fn is_prop(&self, ctx: CtxId, tm: TermId) -> bool {
        self.x[ctx.0].is_prop(tm)
    }

    fn has_var(&self, ctx: CtxId, tm: TermId, var: VarId) -> bool {
        //TODO: optimize, a _lot_
        match self.node(ctx, tm) {
            Node::Fv(v) => *v == var,
            Node::Import(imp) => self.has_var(imp.ctx, imp.tm, var),
            n => n.children().iter().any(|&i| self.has_var(ctx, i, var)),
        }
    }

    fn syn_eq(&self, lctx: CtxId, lhs: TermId, rctx: CtxId, rhs: TermId) -> bool {
        //TODO: optimize; handle close and let at least a little
        if lctx == rctx && lhs == rhs {
            return true;
        }
        let lnode = self.node(lctx, lhs);
        if let Node::Import(import) = lnode {
            return self.syn_eq(import.ctx, import.tm, rctx, rhs);
        }
        let rnode = self.node(rctx, rhs);
        if let Node::Import(rnode) = rnode {
            return self.syn_eq(lctx, lhs, rnode.ctx, rnode.tm);
        }
        // Note this does not work on close since that goes into the discriminator; fine for _now_
        lnode.disc() == rnode.disc()
            && lnode
                .children()
                .iter()
                .zip(rnode.children())
                .all(|(&lhs, &rhs)| self.syn_eq(lctx, lhs, rctx, rhs))
    }

    fn eq_in(&self, ctx: CtxId, lhs: TermId, rhs: TermId) -> bool {
        self.x[ctx.0].eq_in(lhs, rhs)
    }

    fn has_ty(&self, ctx: CtxId, tm: TermId, ty: TermId) -> bool {
        self.x[ctx.0].has_ty(tm, ty)
    }

    fn is_ty_under(&self, ctx: CtxId, binder: TermId, tm: TermId) -> bool {
        self.x[ctx.0].is_ty_under(binder, tm)
    }

    fn has_ty_under(&self, ctx: CtxId, binder: TermId, tm: TermId, ty: TermId) -> bool {
        self.x[ctx.0].has_ty_under(binder, tm, ty)
    }

    fn forall_inhab_under(&self, ctx: CtxId, binder: TermId, ty: TermId) -> bool {
        self.x[ctx.0].forall_inhab_under(binder, ty)
    }

    fn exists_inhab_under(&self, ctx: CtxId, binder: TermId, ty: TermId) -> bool {
        self.x[ctx.0].exists_inhab_under(binder, ty)
    }

    fn u_le(&self, lo: ULvl, hi: ULvl) -> bool {
        lo.level <= hi.level
    }

    fn u_lt(&self, lo: ULvl, hi: ULvl) -> bool {
        lo.level < hi.level
    }

    fn imax_le(&self, lo_lhs: ULvl, lo_rhs: ULvl, hi: ULvl) -> bool {
        self.u_le(lo_rhs, ULvl::PROP) || self.u_le(lo_lhs, hi) && self.u_le(lo_rhs, hi)
    }
}

impl WriteFacts<CtxId, TermId> for EggTermDb {
    fn set_is_contr(&mut self, ctx: CtxId) {
        self.x[ctx.0].set_is_contr();
    }

    fn set_is_wf_unchecked(&mut self, ctx: CtxId, tm: TermId) {
        self.x[ctx.0].set_is_wf_unchecked(tm);
    }

    fn set_is_ty_unchecked(&mut self, ctx: CtxId, tm: TermId) {
        self.x[ctx.0].set_is_ty_unchecked(tm);
    }

    fn set_is_inhab_unchecked(&mut self, ctx: CtxId, tm: TermId) {
        self.x[ctx.0].set_is_inhab_unchecked(tm);
    }

    fn set_is_empty_unchecked(&mut self, ctx: CtxId, tm: TermId) {
        self.x[ctx.0].set_is_empty_unchecked(tm);
    }

    fn set_is_prop_unchecked(&mut self, ctx: CtxId, tm: TermId) {
        self.x[ctx.0].set_is_prop_unchecked(tm);
    }

    fn set_eq_unchecked(&mut self, ctx: CtxId, lhs: TermId, rhs: TermId) {
        self.x[ctx.0].set_eq_unchecked(lhs, rhs);
    }

    fn set_has_ty_unchecked(&mut self, ctx: CtxId, tm: TermId, ty: TermId) {
        self.x[ctx.0].set_has_ty_unchecked(tm, ty);
    }

    fn set_is_ty_under_unchecked(&mut self, ctx: CtxId, binder: TermId, tm: TermId) {
        self.x[ctx.0].set_is_ty_under_unchecked(binder, tm);
    }

    fn set_has_ty_under_unchecked(&mut self, ctx: CtxId, binder: TermId, tm: TermId, ty: TermId) {
        self.x[ctx.0].set_has_ty_under_unchecked(binder, tm, ty);
    }

    fn set_forall_inhab_under_unchecked(&mut self, ctx: CtxId, binder: TermId, ty: TermId) -> bool {
        self.x[ctx.0].set_forall_inhab_under_unchecked(binder, ty)
    }

    fn set_exists_inhab_under_unchecked(&mut self, ctx: CtxId, binder: TermId, ty: TermId) -> bool {
        self.x[ctx.0].set_exists_inhab_under_unchecked(binder, ty)
    }

    fn assume_unchecked(&mut self, ctx: CtxId, ty: TermId) {
        self.x[ctx.0].assume_unchecked(ty);
    }

    fn add_var_unchecked(&mut self, ctx: CtxId, ty: TermId) -> Gv<CtxId> {
        let ix = self.x[ctx.0].add_var_unchecked(ty);
        Gv { ctx, ix }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn unit_eq_empty_contr() {
        let mut db = EggTermDb::default();
        let ctx = db.new_ctx();
        assert!(!db.is_contr(ctx));
        assert_eq!(db.parent(ctx), None);
        let unit = db.add(ctx, Node::Unit);
        let empty = db.add(ctx, Node::Empty);
        assert_ne!(unit, empty);
        assert!(!db.is_contr(ctx));
        db.set_eq_unchecked(ctx, unit, empty);
        assert!(db.is_contr(ctx));
    }

    #[test]
    fn basic_imax_le() {
        let db = EggTermDb::default();
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
