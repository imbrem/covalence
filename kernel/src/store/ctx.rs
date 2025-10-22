use std::{borrow::BorrowMut, ops::BitOr};

use bitflags::bitflags;
use egg::{Analysis, DidMerge, EGraph, Language};
use indexmap::IndexSet;

use crate::store::*;

#[derive(Debug, Clone)]
#[repr(transparent)]
pub struct Ctx {
    e: EGraph<Node, CtxData>,
}

impl Ctx {
    pub fn new_ctx() -> Ctx {
        Ctx {
            e: EGraph::new(CtxData::default()).with_explanations_enabled(),
        }
    }

    pub fn with_parent(parent: CtxId) -> Ctx {
        let mut ctx = Ctx::new_ctx();
        ctx.e.analysis.parent = Some(parent);
        ctx
    }

    pub fn parent(&self) -> Option<CtxId> {
        self.e.analysis.parent
    }

    pub fn set_parent_unchecked(&mut self, parent: CtxId) {
        self.e.analysis.parent = Some(parent);
    }

    pub fn set_this(&mut self, this: CtxId) {
        self.e.analysis.this = Some(this);
    }

    pub fn add(&mut self, node: Node) -> TermId {
        // NOTE: an uncanonical application is necessary to roundtrip with lookup
        TermId(self.e.add_uncanonical(node))
    }

    pub fn node(&self, id: TermId) -> &Node {
        self.e.id_to_node(id.0)
    }

    pub fn lookup(&self, node: impl BorrowMut<Node>) -> Option<TermId> {
        self.e.lookup(node).map(TermId)
    }

    pub fn var_ty(&self, ix: u32) -> Option<TermId> {
        self.e.analysis.vars.get(ix as usize).copied()
    }

    pub fn num_assumptions(&self) -> u32 {
        self.e.analysis.assumptions.len() as u32
    }

    pub fn assumption(&self, ix: u32) -> Option<TermId> {
        self.e.analysis.assumptions.get_index(ix as usize).copied()
    }

    pub fn num_vars(&self) -> u32 {
        self.e.analysis.vars.len() as u32
    }

    pub fn propagate_in(&mut self) -> usize {
        self.e.rebuild()
    }

    pub fn is_null_extension(&self) -> bool {
        self.e.analysis.assumptions.is_empty() && self.e.analysis.vars.is_empty()
    }

    pub fn is_contr(&self) -> bool {
        self.e.analysis.flags.contains(CtxFlags::IS_CONTR)
    }

    pub fn set_is_contr(&mut self) -> bool {
        let old_flags = self.e.analysis.flags;
        self.e.analysis.flags |= CtxFlags::IS_CONTR;
        self.e.analysis.flags != old_flags
    }

    pub fn eq_in(&self, lhs: TermId, rhs: TermId) -> bool {
        self.e.find(lhs.0) == self.e.find(rhs.0)
    }

    pub fn has_ty(&self, tm: TermId, ty: TermId) -> bool {
        let Some(has_ty) = self.lookup(Node::HasTy([tm, ty])) else {
            return false;
        };
        self.is_wf(has_ty)
    }

    pub fn is_ty_under(&self, binder: TermId, ty: TermId) -> bool {
        if !self.is_ty(binder) {
            return false;
        }
        if self.is_ty(ty) {
            return true;
        }
        //TODO: should we check sigma as well, or assume things have been normalized?
        let Some(is_ty_under) = self.lookup(Node::Pi([binder, ty])) else {
            return false;
        };
        self.is_wf(is_ty_under)
    }

    pub fn has_ty_under(&self, binder: TermId, tm: TermId, ty: TermId) -> bool {
        let Some(has_ty) = self.lookup(Node::HasTy([tm, ty])) else {
            return false;
        };
        if !self.is_ty(binder) {
            return false;
        }
        if self.is_wf(has_ty) {
            return true;
        }
        let Some(has_ty_under) = self.lookup(Node::Pi([binder, has_ty])) else {
            return false;
        };
        self.is_wf(has_ty_under)
    }

    pub fn forall_inhab_under(&self, binder: TermId, ty: TermId) -> bool {
        if !self.is_ty(binder) {
            return false;
        }
        if self.is_inhab(ty) || self.eq_in(ty, binder) {
            return true;
        }
        let Some(forall_inhab_under) = self.lookup(Node::Pi([binder, ty])) else {
            return false;
        };
        self.is_inhab(forall_inhab_under)
    }

    pub fn exists_inhab_under(&self, binder: TermId, ty: TermId) -> bool {
        if !self.is_ty(binder) {
            return false;
        }
        if (self.is_inhab(ty) || self.eq_in(ty, binder)) && self.is_inhab(binder) {
            return true;
        }
        let Some(exists_inhab_under) = self.lookup(Node::Sigma([binder, ty])) else {
            return false;
        };
        self.is_inhab(exists_inhab_under)
    }

    pub fn is_wf(&self, tm: TermId) -> bool {
        self.e[tm.0].data.flags.contains(ClassFlags::IS_WF)
    }

    pub fn is_ty(&self, tm: TermId) -> bool {
        self.e[tm.0].data.flags.contains(ClassFlags::IS_TY)
    }

    pub fn is_inhab(&self, tm: TermId) -> bool {
        self.e[tm.0].data.flags.contains(ClassFlags::IS_INHAB)
    }

    pub fn is_empty(&self, tm: TermId) -> bool {
        self.e[tm.0].data.flags.contains(ClassFlags::IS_EMPTY)
    }

    pub fn is_prop(&self, tm: TermId) -> bool {
        self.e[tm.0].data.flags.contains(ClassFlags::IS_PROP)
    }

    pub fn is_univ(&self, tm: TermId) -> bool {
        self.e[tm.0].data.flags.contains(ClassFlags::IS_UNIV)
    }

    fn set_flags_unchecked(&mut self, tm: TermId, flags: ClassFlags) -> bool {
        let mut data = self.e[tm.0].data;
        let old_flags = data.flags;
        data.flags |= flags;
        if data.flags != old_flags {
            self.e.set_analysis_data(tm.0, data);
            true
        } else {
            false
        }
    }

    pub fn set_is_wf_unchecked(&mut self, tm: TermId) -> bool {
        self.set_flags_unchecked(tm, ClassFlags::IS_WF)
    }

    pub fn set_is_ty_unchecked(&mut self, tm: TermId) -> bool {
        self.set_flags_unchecked(tm, ClassFlags::IS_TY)
    }

    pub fn set_is_inhab_unchecked(&mut self, tm: TermId) -> bool {
        self.set_flags_unchecked(tm, ClassFlags::IS_INHAB)
    }

    pub fn set_is_empty_unchecked(&mut self, tm: TermId) -> bool {
        self.set_flags_unchecked(tm, ClassFlags::IS_EMPTY)
    }

    pub fn set_is_prop_unchecked(&mut self, tm: TermId) -> bool {
        self.set_flags_unchecked(tm, ClassFlags::IS_PROP)
    }

    pub fn set_eq_unchecked(&mut self, lhs: TermId, rhs: TermId) -> bool {
        self.e.union(lhs.0, rhs.0)
    }

    pub fn set_has_ty_unchecked(&mut self, tm: TermId, ty: TermId) -> bool {
        if !self.is_prop(tm)
            && self.is_univ(ty)
            && let Some(u0) = self.lookup(Node::U(ULvl::PROP))
            && self.eq_in(ty, u0)
        {
            self.set_is_prop_unchecked(tm);
        }
        self.set_is_wf_unchecked(tm);
        let has_ty = self.add(GNode::HasTy([tm, ty]));
        self.set_is_inhab_unchecked(ty);
        let unit = self.add(GNode::Unit);
        self.set_eq_unchecked(has_ty, unit)
    }

    pub fn set_has_ty_under_unchecked(&mut self, binder: TermId, tm: TermId, ty: TermId) -> bool {
        self.set_is_ty_unchecked(binder);
        let has_ty = self.add(GNode::HasTy([tm, ty]));
        let has_ty_under = self.add(GNode::Pi([binder, has_ty]));
        let unit = self.add(GNode::Unit);
        self.set_is_ty_under_unchecked(binder, ty);
        self.set_eq_unchecked(has_ty_under, unit)
    }

    pub fn set_is_ty_under_unchecked(&mut self, binder: TermId, ty: TermId) -> bool {
        self.set_is_ty_unchecked(binder);
        let pi = self.add(GNode::Pi([binder, ty]));
        self.set_is_ty_unchecked(pi)
    }

    pub fn set_forall_inhab_under_unchecked(&mut self, binder: TermId, ty: TermId) -> bool {
        self.set_is_ty_unchecked(binder);
        let pi = self.add(GNode::Pi([binder, ty]));
        self.set_is_inhab_unchecked(pi)
    }

    pub fn set_exists_inhab_under_unchecked(&mut self, binder: TermId, ty: TermId) -> bool {
        self.set_is_ty_under_unchecked(binder, ty);
        let sigma = self.add(GNode::Sigma([binder, ty]));
        self.set_is_inhab_unchecked(sigma)
    }

    pub fn assume_unchecked(&mut self, ty: TermId) {
        // If something is already inhabited, don't bother adding it as an assumption
        if self.is_inhab(ty) {
            return;
        }
        self.e.analysis.assumptions.insert(ty);
        self.set_is_inhab_unchecked(ty);
    }

    pub fn add_var_unchecked(&mut self, ty: TermId) -> u32 {
        // NOTE: this overflow should be impossible due to limitations of the E-graph, but better
        // safe than sorry...
        let ix: u32 = self
            .e
            .analysis
            .vars
            .len()
            .try_into()
            .expect("variable index overflow");
        self.e.analysis.vars.push(ty);
        ix
    }

    fn from_ref(this: &EGraph<Node, CtxData>) -> &Self {
        // SAFETY: due to `#[repr(transparent)]`
        unsafe { std::mem::transmute(this) }
    }

    // fn from_mut(this: &mut EGraph<Node, CtxData>) -> &mut Self {
    //     // SAFETY: due to `#[repr(transparent)]`
    //     unsafe { std::mem::transmute(this) }
    // }

    pub fn bvi(&self, id: TermId) -> Bv {
        self.e[id.0].data.bvi
    }

    pub fn set_bvi_unchecked(&mut self, id: TermId, bvi: Bv) {
        let mut data = self.e[id.0].data;
        if bvi >= data.bvi {
            return;
        }
        data.bvi = bvi;
        self.e.set_analysis_data(id.0, data);
    }
}

#[derive(Debug, Clone, Default)]
struct CtxData {
    /// Pointer to self
    this: Option<CtxId>,
    /// This context's parent, if any
    parent: Option<CtxId>,
    /// This context's flags
    flags: CtxFlags,
    /// This context's assumptions
    ///
    /// Note these are not allowed to talk about _this_ context's variables!
    assumptions: IndexSet<TermId>,
    /// This context's variables, implemented as a map from indices to types
    vars: Vec<TermId>,
}

impl Analysis<Node> for CtxData {
    type Data = ClassData;

    fn make(egraph: &mut EGraph<Node, Self>, enode: &Node) -> Self::Data {
        let this = Ctx::from_ref(egraph);
        let bvi = enode.bvi(|x| this.bvi(*x));
        let flags = match enode {
            Node::U(_) => ClassFlags::IS_UNIV,
            Node::Unit => ClassFlags::IS_TRUE,
            Node::Empty => ClassFlags::IS_FALSE,
            Node::Nats => ClassFlags::IS_TY,
            Node::N64(_) | Node::Null => ClassFlags::IS_WF,
            &Node::Pi([arg_ty, res_ty]) => {
                let mut result = ClassFlags::MAY_TY;
                result.set(ClassFlags::IS_WF, this.is_ty_under(arg_ty, res_ty));
                result.set(
                    ClassFlags::MAY_INHAB,
                    //NOTE: we don't check forall_inhab_under, since this is just circular!
                    this.is_empty(arg_ty) || this.is_inhab(res_ty),
                );
                result.set(
                    ClassFlags::MAY_EMPTY,
                    this.is_inhab(arg_ty) && this.is_empty(res_ty),
                );
                result.set(ClassFlags::MAY_PROP, this.is_prop(res_ty));
                result
            }
            &Node::Sigma([lhs_ty, rhs_ty]) => {
                let mut result = ClassFlags::MAY_TY;
                result.set(ClassFlags::IS_WF, this.is_ty_under(lhs_ty, rhs_ty));
                result.set(
                    ClassFlags::MAY_INHAB,
                    //NOTE: we don't check exists_inhab_under, since this is just circular!
                    this.is_inhab(lhs_ty) && this.is_inhab(rhs_ty),
                );
                result.set(
                    ClassFlags::MAY_EMPTY,
                    this.is_empty(lhs_ty) || this.is_empty(rhs_ty),
                );
                result.set(
                    ClassFlags::MAY_PROP,
                    this.is_prop(lhs_ty) && this.is_prop(rhs_ty),
                );
                result
            }
            &Node::Trunc([ty]) => {
                let mut result = ClassFlags::MAY_PROP;
                result.set(ClassFlags::IS_WF, this.is_ty(ty));
                result.set(ClassFlags::MAY_INHAB, this.is_inhab(ty));
                result.set(ClassFlags::MAY_EMPTY, this.is_empty(ty));
                result
            }
            &Node::Pair([lhs, rhs]) if this.is_wf(lhs) && this.is_wf(rhs) => ClassFlags::IS_WF,
            _ => ClassFlags::default(),
        };
        ClassData { flags, bvi }
    }

    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> egg::DidMerge {
        let new = *a | b;
        let changed = DidMerge(*a == new, b == new);
        *a = new;
        if new.flags.is_contr() {
            self.flags |= CtxFlags::IS_CONTR;
        }
        changed
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
struct ClassData {
    flags: ClassFlags,
    bvi: Bv,
}

impl BitOr for ClassData {
    type Output = ClassData;

    fn bitor(self, rhs: Self) -> Self::Output {
        ClassData {
            flags: self.flags | rhs.flags,
            bvi: self.bvi.min(rhs.bvi),
        }
    }
}

bitflags! {
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd, Default)]
    struct CtxFlags: u8 {
        const IS_CONTR  = 0b00000001;
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd, Default)]
    struct ClassFlags: u8 {
        const IS_WF     = 0b00000001;
        const MAY_TY    = 0b00000010;
        const IS_TY     = 0b00000011;
        const MAY_INHAB = 0b00000100;
        const IS_INHAB  = 0b00000111;
        const MAY_EMPTY = 0b00001000;
        const IS_EMPTY  = 0b00001011;
        const MAY_PROP  = 0b00010010;
        const IS_PROP   = 0b00010011;
        const IS_TRUE   = 0b00010111;
        const IS_FALSE  = 0b00011011;
        const MAY_UNIV  = 0b00100110;
        const IS_UNIV   = 0b00100111;
    }
}

impl ClassFlags {
    pub fn is_contr(&self) -> bool {
        self.contains(ClassFlags::IS_INHAB | ClassFlags::IS_EMPTY)
    }
}

impl Ctx {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
#[repr(transparent)]
pub struct TermId(egg::Id);

pub type Node = GNode<CtxId, TermId>;

impl Language for Node {
    type Discriminant = GDisc<CtxId, TermId>;

    fn discriminant(&self) -> Self::Discriminant {
        self.disc()
    }

    fn matches(&self, other: &Self) -> bool {
        self.disc() == other.disc()
    }

    fn children(&self) -> &[egg::Id] {
        // SAFETY: a `TermId` has the same representation as an `egg::Id`
        let children = self.children();
        unsafe {
            std::slice::from_raw_parts(children as *const _ as *const egg::Id, children.len())
        }
    }

    fn children_mut(&mut self) -> &mut [egg::Id] {
        // SAFETY: a `TermId` has the same representation as an `egg::Id`
        let children = self.children_mut();
        unsafe {
            std::slice::from_raw_parts_mut(children as *mut _ as *mut egg::Id, children.len())
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn basic_flags() {
        let mut ctx = Ctx::new_ctx();
        let u0 = ctx.add(Node::U(ULvl::PROP));
        let u1 = ctx.add(Node::U(ULvl::SET));
        assert_ne!(u0, u1);
        assert!(!ctx.eq_in(u0, u1));
        for u in [u0, u1] {
            assert!(ctx.is_wf(u));
            assert!(ctx.is_ty(u));
            assert!(ctx.is_inhab(u));
            assert!(!ctx.is_prop(u));
            assert!(!ctx.is_empty(u));
        }
        let unit = ctx.add(Node::Unit);
        let empty = ctx.add(Node::Empty);
        assert_ne!(unit, empty);
        assert!(!ctx.eq_in(unit, empty));
        assert!(ctx.is_inhab(unit));
        assert!(!ctx.is_empty(unit));
        assert!(!ctx.is_inhab(empty));
        assert!(ctx.is_empty(empty));
        let t_unit = ctx.add(Node::Trunc([unit]));
        let t_empty = ctx.add(Node::Trunc([empty]));
        let nats = ctx.add(Node::Nats);
        let t_nats = ctx.add(Node::Trunc([nats]));
        let unit_to_empty = ctx.add(Node::Pi([unit, empty]));
        let empty_to_unit = ctx.add(Node::Pi([empty, unit]));
        let unit_to_empty_to_empty = ctx.add(Node::Pi([unit_to_empty, empty]));
        let unit_and_empty = ctx.add(Node::Sigma([unit, empty]));
        for t in [
            unit,
            empty,
            t_unit,
            t_empty,
            t_nats,
            unit_to_empty,
            empty_to_unit,
            unit_to_empty_to_empty,
            unit_and_empty,
        ] {
            assert!(ctx.is_wf(t));
            assert!(ctx.is_ty(t));
            assert!(ctx.is_prop(t));
            assert!(!ctx.has_ty(t, u0));
            ctx.set_has_ty_unchecked(t, u0);
            assert!(ctx.has_ty(t, u0));
            assert!(!ctx.has_ty(t, u1));
            ctx.set_has_ty_unchecked(t, u1);
            assert!(ctx.has_ty(t, u0));
            assert!(ctx.has_ty(t, u1));
        }
        assert!(!ctx.is_contr());
        ctx.set_eq_unchecked(unit, empty);
        assert!(ctx.is_contr());
    }

    #[test]
    fn add_var_prop() {
        let mut ctx = Ctx::new_ctx();
        let u0 = ctx.add(Node::U(ULvl::PROP));
        assert_eq!(ctx.num_assumptions(), 0);
        assert_eq!(ctx.var_ty(0), None);
        let vx = ctx.add_var_unchecked(u0);
        assert_eq!(vx, 0);
        assert_eq!(ctx.num_assumptions(), 0);
        assert_eq!(ctx.var_ty(0), Some(u0));
        assert_eq!(ctx.var_ty(1), None);
    }
}
