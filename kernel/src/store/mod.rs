use typed_generational_arena::{SmallArena, SmallIndex};

use crate::api::generic::*;
use crate::api::store::*;
use crate::data::term::*;

mod ctx;
use ctx::*;

pub use ctx::{Node, TermId};

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CtxId(SmallIndex<Ctx>);

pub type VarId = Fv<CtxId>;

pub type ValId = Val<CtxId, TermId>;

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

impl ReadTerm<CtxId, TermId> for TermDb {
    fn val(&self, ctx: CtxId, tm: TermId) -> ValId {
        match self.node(ctx, tm) {
            Node::Import(val) => self.val(val.ctx, val.tm),
            _ => Val { ctx, tm },
        }
    }

    fn node(&self, ctx: CtxId, tm: TermId) -> &Node {
        self.x[ctx.0].node(tm)
    }

    fn lookup(&self, ctx: CtxId, tm: &mut Node) -> Option<TermId> {
        self.x[ctx.0].lookup(tm)
    }

    fn lookup_val(&self, ctx: CtxId, val: ValId) -> Option<TermId> {
        // NOTE: an import cycle will lead to a stack overflow here, but that should be an error But
        // think about it!
        //
        // We could try a cycle detection algorithm and return `Invalid`, if we want to be very
        // clever... but again, this is a deeply invalid state, since import destinations should
        // _not_ be mutable, and we can't get the `TermId` of an import without synthesizing an
        // invalid one (which is unspecified behaviour, but should not cause unsoundness) before
        // inserting the import and hence fixing the `TermId`.
        if let Some(node) = val.node_ix(self).relocate() {
            if let Node::Import(imp) = node {
                self.lookup_val(ctx, imp)
            } else {
                self.x[ctx.0].lookup(node)
            }
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

    fn has_var(&self, ctx: CtxId, tm: TermId, var: Fv<CtxId>) -> bool {
        //TODO: optimize, a _lot_
        match self.node(ctx, tm) {
            Node::Fv(v) => *v == var,
            Node::Import(imp) => self.may_have_var(imp.ctx, imp.tm, var),
            n => n.children().iter().any(|&i| self.may_have_var(ctx, i, var)),
        }
    }

    fn has_var_from(&self, ctx: CtxId, tm: TermId, vars: CtxId) -> bool {
        //TODO: optimize, a _lot_
        match self.node(ctx, tm) {
            Node::Fv(v) => v.ctx == vars,
            Node::Import(imp) => self.may_have_var_from(imp.ctx, imp.tm, vars),
            n => n
                .children()
                .iter()
                .any(|&i| self.may_have_var_from(ctx, i, vars)),
        }
    }

    fn may_have_var(&self, ctx: CtxId, tm: TermId, var: VarId) -> bool {
        //TODO: optimize, a _lot_
        match self.node(ctx, tm) {
            Node::Fv(v) => *v == var,
            Node::Import(imp) => self.may_have_var(imp.ctx, imp.tm, var),
            n => n.children().iter().any(|&i| self.may_have_var(ctx, i, var)),
        }
    }

    fn may_have_var_from(&self, ctx: CtxId, tm: TermId, vars: CtxId) -> bool {
        //TODO: optimize, a _lot_
        match self.node(ctx, tm) {
            Node::Fv(v) => v.ctx == vars,
            Node::Import(imp) => self.may_have_var_from(imp.ctx, imp.tm, vars),
            n => n
                .children()
                .iter()
                .any(|&i| self.may_have_var_from(ctx, i, vars)),
        }
    }

    fn deref_eq(&self, lhs: Val<CtxId, TermId>, rhs: Val<CtxId, TermId>) -> bool {
        lhs == rhs || self.val(lhs.ctx, lhs.tm) == self.val(rhs.ctx, rhs.tm)
    }

    fn cons_eq(&self, lhs: ValId, rhs: ValId) -> bool {
        if lhs == rhs {
            return true;
        }
        let ln = lhs.node_val(self);
        let rn = rhs.node_val(self);
        ln.syn_disc() == rn.syn_disc()
            && ln
                .syn_children()
                .iter()
                .zip(rn.syn_children().iter())
                .all(|(&l, &r)| self.cons_eq(l, r))
    }

    fn syn_eq(&self, lhs: ValId, rhs: ValId) -> bool {
        if lhs == rhs {
            return true;
        }
        match (lhs.node_val(self), rhs.node_val(self)) {
            (NodeVT::Import(lhs), _) => self.syn_eq(lhs, rhs),
            (_, NodeVT::Import(rhs)) => self.syn_eq(lhs, rhs),
            (ln, rn) => {
                ln.syn_disc() == rn.syn_disc()
                    && ln
                        .syn_children()
                        .iter()
                        .zip(rn.syn_children().iter())
                        .all(|(&l, &r)| self.syn_eq(l, r))
            }
        }
    }

    fn unfold_eq(&self, lhs: Val<CtxId, TermId>, rhs: Val<CtxId, TermId>) -> bool {
        //TODO: reduce here, later...
        self.syn_eq(lhs, rhs)
    }
}

impl WriteTerm<CtxId, TermId> for TermDb {
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

    fn import(&mut self, ctx: CtxId, val: ValId) -> TermId {
        // NOTE: an import cycle will lead to a stack overflow here, but that should be an error But
        // think about it!
        //
        // We could try a cycle detection algorithm and return `Invalid`, if we want to be very
        // clever... but again, this is a deeply invalid state, since import destinations should
        // _not_ be mutable, and we can't get the `TermId` of an import without synthesizing an
        // invalid one (which is unspecified behaviour, but should not cause unsoundness) before
        // inserting the import and hence fixing the `TermId`.
        let result = if let Some(node) = val.node_ix(self).relocate() {
            if let Node::Import(imp) = node {
                self.import(ctx, imp)
            } else {
                self.x[ctx.0].add(node)
            }
        } else if ctx == val.ctx {
            return val.tm;
        } else {
            self.x[ctx.0].add(NodeT::Import(val))
        };
        let bvi = val.bvi(self);
        self.set_bvi_unchecked(ctx, result, bvi);
        result
    }

    fn var_ty(&mut self, ctx: CtxId, var: VarId) -> TermId {
        let ty = self.get_var_ty(var);
        self.import(
            ctx,
            Val {
                ctx: var.ctx,
                tm: ty,
            },
        )
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

impl ReadCtx<CtxId, TermId> for TermDb {
    fn is_root(&self, ctx: CtxId) -> bool {
        //TODO: optimize
        self.x[ctx.0].is_null_extension() && self.x[ctx.0].parent().is_none_or(|p| self.is_root(p))
    }

    fn is_contr(&self, ctx: CtxId) -> bool {
        self.x[ctx.0].is_contr()
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

    fn num_vars(&self, ctx: CtxId) -> u32 {
        self.x[ctx.0].num_vars()
    }

    fn get_var_ty(&self, var: VarId) -> TermId {
        self.x[var.ctx.0]
            .var_ty(var.ix)
            .expect("invalid variable index")
    }

    fn var_is_ghost(&self, var: Fv<CtxId>) -> bool {
        self.x[var.ctx.0].var_is_ghost(var.ix)
    }
}

impl ReadTermFacts<CtxId, TermId> for TermDb {
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

    fn eq_in(&self, ctx: CtxId, lhs: TermId, rhs: TermId) -> bool {
        self.x[ctx.0].eq_in(lhs, rhs)
    }

    fn has_ty(&self, ctx: CtxId, tm: TermId, ty: TermId) -> bool {
        self.x[ctx.0].has_ty(tm, ty)
    }

    fn forall_eq_in(&self, ctx: CtxId, binder: TermId, lhs: TermId, rhs: TermId) -> bool {
        self.x[ctx.0].forall_eq_in(binder, lhs, rhs)
    }

    fn forall_is_wf(&self, ctx: CtxId, binder: TermId, ty: TermId) -> bool {
        self.x[ctx.0].forall_is_wf(binder, ty)
    }

    fn forall_is_ty(&self, ctx: CtxId, binder: TermId, tm: TermId) -> bool {
        self.x[ctx.0].forall_is_ty(binder, tm)
    }

    fn forall_is_prop(&self, ctx: CtxId, binder: TermId, ty: TermId) -> bool {
        self.x[ctx.0].forall_is_prop(binder, ty)
    }

    fn forall_has_ty(&self, ctx: CtxId, binder: TermId, tm: TermId, ty: TermId) -> bool {
        self.x[ctx.0].forall_has_ty(binder, tm, ty)
    }

    fn forall_is_inhab(&self, ctx: CtxId, binder: TermId, ty: TermId) -> bool {
        self.x[ctx.0].forall_is_inhab(binder, ty)
    }

    fn forall_is_empty(&self, ctx: CtxId, binder: TermId, tm: TermId) -> bool {
        self.x[ctx.0].forall_is_empty(binder, tm)
    }

    fn exists_eq_in(&self, ctx: CtxId, binder: TermId, lhs: TermId, rhs: TermId) -> bool {
        self.x[ctx.0].exists_eq_in(binder, lhs, rhs)
    }

    fn exists_is_wf(&self, ctx: CtxId, binder: TermId, ty: TermId) -> bool {
        self.x[ctx.0].exists_is_wf(binder, ty)
    }

    fn exists_is_ty(&self, ctx: CtxId, binder: TermId, ty: TermId) -> bool {
        self.x[ctx.0].exists_is_ty(binder, ty)
    }

    fn exists_is_prop(&self, ctx: CtxId, binder: TermId, ty: TermId) -> bool {
        self.x[ctx.0].exists_is_prop(binder, ty)
    }

    fn exists_has_ty(&self, ctx: CtxId, binder: TermId, tm: TermId, ty: TermId) -> bool {
        self.x[ctx.0].exists_has_ty(binder, tm, ty)
    }

    fn exists_is_inhab(&self, ctx: CtxId, binder: TermId, ty: TermId) -> bool {
        self.x[ctx.0].exists_is_inhab(binder, ty)
    }

    fn exists_is_empty(&self, ctx: CtxId, binder: TermId, tm: TermId) -> bool {
        self.x[ctx.0].exists_is_empty(binder, tm)
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

impl ReadTermDb<CtxId, TermId> for TermDb {
    type Reader = TermDb;

    fn read(&self) -> &Self::Reader {
        self
    }
}

impl WriteFacts<CtxId, TermId> for TermDb {
    fn set_is_contr_unchecked(&mut self, ctx: CtxId) {
        self.x[ctx.0].set_is_contr();
    }

    fn set_parent_unchecked(&mut self, ctx: CtxId, parent: CtxId) {
        self.x[ctx.0].set_parent_unchecked(parent);
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

    fn set_exists_eq_unchecked(&mut self, ctx: CtxId, binder: TermId, lhs: TermId, rhs: TermId) {
        self.x[ctx.0].set_exists_eq_unchecked(binder, lhs, rhs);
    }

    fn set_exists_is_wf_unchecked(&mut self, ctx: CtxId, binder: TermId, tm: TermId) {
        self.x[ctx.0].set_exists_is_wf_unchecked(binder, tm);
    }

    fn set_exists_is_ty_unchecked(&mut self, ctx: CtxId, binder: TermId, tm: TermId) {
        self.x[ctx.0].set_exists_is_ty_unchecked(binder, tm);
    }

    fn set_exists_is_prop_unchecked(&mut self, ctx: CtxId, binder: TermId, tm: TermId) {
        self.x[ctx.0].set_exists_is_prop_unchecked(binder, tm);
    }

    fn set_exists_has_ty_unchecked(&mut self, ctx: CtxId, binder: TermId, tm: TermId, ty: TermId) {
        self.x[ctx.0].set_exists_has_ty_unchecked(binder, tm, ty);
    }

    fn set_exists_is_inhab_unchecked(&mut self, ctx: CtxId, binder: TermId, ty: TermId) {
        self.x[ctx.0].set_exists_is_inhab_unchecked(binder, ty);
    }

    fn set_exists_is_empty_unchecked(&mut self, ctx: CtxId, binder: TermId, tm: TermId) {
        self.x[ctx.0].set_exists_is_empty_unchecked(binder, tm);
    }

    fn assume_unchecked(&mut self, ctx: CtxId, ty: TermId) -> VarId {
        let ix = self.x[ctx.0].assume_unchecked(ty);
        VarId { ctx, ix }
    }

    fn add_var_unchecked(&mut self, ctx: CtxId, ty: TermId) -> VarId {
        let ix = self.x[ctx.0].add_var_unchecked(ty);
        VarId { ctx, ix }
    }

    fn set_bvi_unchecked(&mut self, ctx: CtxId, tm: TermId, bvi: Bv) {
        self.x[ctx.0].set_bvi_unchecked(tm, bvi);
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn unit_eq_empty_contr() {
        let mut db = TermDb::default();
        let ctx = db.new_ctx();
        assert!(!db.is_contr(ctx));
        let unit = db.add(ctx, Node::Unit);
        let empty = db.add(ctx, Node::Empty);
        assert_ne!(unit, empty);
        assert!(!db.is_contr(ctx));
        db.set_eq_unchecked(ctx, unit, empty);
        assert!(db.is_contr(ctx));
    }

    #[test]
    fn construct_pi_prop_close() {
        let mut db = TermDb::default();
        let root = db.new_ctx();
        let child = db.with_parent(root);
        let child_prop = db.add(child, Node::U(ULvl::PROP));
        let vx = db.add_var_unchecked(child, child_prop);
        let x = db.add(child, Node::Fv(vx));
        let root_prop = db.add(root, Node::U(ULvl::PROP));
        let root_x = db.import(root, Val { ctx: child, tm: x });
        assert_eq!(db.bvi(root, root_x), Bv(0));
        let root_close_x = db.add(
            root,
            Node::Close(Close {
                under: Bv(0),
                var: vx,
                tm: root_x,
            }),
        );
        assert_eq!(db.bvi(root, root_close_x), Bv(1));
        let root_pi = db.add(root, Node::Pi([root_prop, root_close_x]));
        assert_eq!(db.bvi(root, root_pi), Bv(0));
    }

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
