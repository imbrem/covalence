use std::{collections::BTreeMap, ops::BitOr};

use egg::{Analysis, DidMerge, EGraph, Language};

use crate::{Pred1, fact::Pred0, db::*};

#[derive(Debug, Clone)]
#[repr(transparent)]
pub struct Ctx {
    e: EGraph<NodeIx, CtxData>,
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

    pub fn add(&mut self, node: NodeIx) -> TermId {
        // NOTE: an uncanonical insertion is necessary to roundtrip with lookup
        let result = TermId(self.e.add_uncanonical(node));
        self.e.analysis.node_to_id.insert(node, result);
        result
    }

    pub fn node(&self, id: TermId) -> &NodeIx {
        let result = self.e.id_to_node(id.0);
        debug_assert_eq!(
            self.e.analysis.node_to_id.get(result),
            Some(&id),
            "Ctx::node and Ctx::add are out of sync",
        );
        result
    }

    pub fn lookup(&self, node: NodeIx) -> Option<TermId> {
        let result = self.e.analysis.node_to_id.get(&node).copied();
        debug_assert_eq!(
            result.map(|id| self.node(id)),
            if result.is_none() { None } else { Some(&node) },
            "Ctx::node and Ctx::add are out of sync",
        );
        result
    }

    pub fn var_ty(&self, ix: u32) -> Option<ValId> {
        self.e.analysis.vars.get(ix as usize).copied()
    }

    pub fn num_vars(&self) -> u32 {
        self.e.analysis.vars.len() as u32
    }

    pub fn propagate_in(&mut self) -> usize {
        self.e.rebuild()
    }

    pub fn is_null_extension(&self) -> bool {
        self.e.analysis.vars.is_empty()
    }

    pub fn nullary(&self) -> Pred0 {
        self.e.analysis.flags
    }

    pub fn set_is_contr(&mut self) -> bool {
        let old_flags = self.e.analysis.flags;
        self.e.analysis.flags |= Pred0::IS_CONTR;
        self.e.analysis.flags != old_flags
    }

    pub fn eq_in(&self, lhs: TermId, rhs: TermId) -> bool {
        self.e.find(lhs.0) == self.e.find(rhs.0)
    }

    pub fn has_ty(&self, tm: TermId, ty: TermId) -> bool {
        let Some(has_ty) = self.lookup(NodeIx::HasTy([tm, ty])) else {
            return false;
        };
        self.is_wf(has_ty)
    }

    pub fn tm_flags(&self, tm: TermId) -> Pred1 {
        self.e[tm.0].data.flags
    }

    pub fn is_wf(&self, tm: TermId) -> bool {
        self.e[tm.0].data.flags.contains(Pred1::IS_WF)
    }

    pub fn is_prop(&self, tm: TermId) -> bool {
        self.e[tm.0].data.flags.contains(Pred1::IS_PROP)
    }

    pub fn is_univ(&self, tm: TermId) -> bool {
        self.e[tm.0].data.flags.contains(Pred1::IS_UNIV)
    }

    pub fn set_flags_unchecked(&mut self, tm: TermId, flags: Pred1) -> bool {
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
        self.set_flags_unchecked(tm, Pred1::IS_WF)
    }

    pub fn set_is_ty_unchecked(&mut self, tm: TermId) -> bool {
        self.set_flags_unchecked(tm, Pred1::IS_TY)
    }

    pub fn set_is_inhab_unchecked(&mut self, tm: TermId) -> bool {
        self.set_flags_unchecked(tm, Pred1::IS_INHAB)
    }

    pub fn set_is_empty_unchecked(&mut self, tm: TermId) -> bool {
        self.set_flags_unchecked(tm, Pred1::IS_EMPTY)
    }

    pub fn set_is_prop_unchecked(&mut self, tm: TermId) -> bool {
        self.set_flags_unchecked(tm, Pred1::IS_PROP)
    }

    pub fn set_eq_unchecked(&mut self, lhs: TermId, rhs: TermId) -> bool {
        self.e.union(lhs.0, rhs.0)
    }

    pub fn set_has_ty_unchecked(&mut self, tm: TermId, ty: TermId) -> bool {
        if self.is_univ(ty) {
            self.set_is_ty_unchecked(tm);
            if !self.is_prop(tm)
                && let Some(u0) = self.lookup(NodeIx::U(ULvl::PROP))
                && self.eq_in(ty, u0)
            {
                self.set_is_prop_unchecked(tm);
            }
        }
        self.set_is_wf_unchecked(tm);
        let has_ty = self.add(NodeT::HasTy([tm, ty]));
        self.set_is_inhab_unchecked(ty);
        let unit = self.add(NodeT::Unit);
        self.set_eq_unchecked(has_ty, unit)
    }

    pub fn set_forall_eq_unchecked(&mut self, binder: TermId, lhs: TermId, rhs: TermId) -> bool {
        self.set_is_ty_unchecked(binder);
        let abs_lhs = self.add(NodeT::Abs([binder, lhs]));
        let abs_rhs = self.add(NodeT::Abs([binder, rhs]));
        self.set_eq_unchecked(abs_lhs, abs_rhs)
    }

    pub fn set_forall_is_wf_unchecked(&mut self, binder: TermId, tm: TermId) -> bool {
        self.set_is_ty_unchecked(binder);
        let tm = self.add(NodeT::Abs([binder, tm]));
        self.set_is_wf_unchecked(tm)
    }

    pub fn set_forall_is_ty_unchecked(&mut self, binder: TermId, ty: TermId) -> bool {
        self.set_is_ty_unchecked(binder);
        let pi = self.add(NodeT::Pi([binder, ty]));
        self.set_is_ty_unchecked(pi)
    }

    pub fn set_forall_is_prop_unchecked(&mut self, binder: TermId, ty: TermId) -> bool {
        self.set_is_ty_unchecked(binder);
        let pi = self.add(NodeT::Pi([binder, ty]));
        self.set_is_prop_unchecked(pi)
    }

    pub fn set_forall_has_ty_unchecked(&mut self, binder: TermId, tm: TermId, ty: TermId) -> bool {
        self.set_is_ty_unchecked(binder);
        let abs = self.add(NodeT::Abs([binder, tm]));
        let pi = self.add(NodeT::Pi([binder, ty]));
        self.set_has_ty_unchecked(abs, pi)
    }

    pub fn set_forall_is_inhab_unchecked(&mut self, binder: TermId, ty: TermId) -> bool {
        self.set_is_ty_unchecked(binder);
        let pi = self.add(NodeT::Pi([binder, ty]));
        self.set_is_inhab_unchecked(pi)
    }

    pub fn set_forall_is_empty_unchecked(&mut self, binder: TermId, ty: TermId) -> bool {
        self.set_is_ty_unchecked(binder);
        let sigma = self.add(NodeT::Sigma([binder, ty]));
        self.set_is_empty_unchecked(sigma)
    }

    pub fn set_exists_is_inhab_unchecked(&mut self, binder: TermId, ty: TermId) -> bool {
        self.set_forall_is_ty_unchecked(binder, ty);
        let sigma = self.add(NodeT::Sigma([binder, ty]));
        self.set_is_inhab_unchecked(sigma)
    }

    pub fn add_var_unchecked(&mut self, ctx: CtxId, ty: ValId) -> FvId {
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
        Fv { ctx, ix }
    }

    fn from_ref(this: &EGraph<NodeIx, CtxData>) -> &Self {
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
    flags: Pred0,
    /// This context's variables, implemented as a map from indices to types
    vars: Vec<ValId>,
    /// A map from nodes to their TermId
    ///
    /// TODO: remove hack, but required for now for correctness of `lookup`
    ///
    /// Donald Knuth smiles on me this day, for avoiding temptation.
    node_to_id: BTreeMap<NodeIx, TermId>,
}

impl Analysis<NodeIx> for CtxData {
    type Data = ClassData;

    fn make(egraph: &mut EGraph<NodeIx, Self>, enode: &NodeIx) -> Self::Data {
        let this = Ctx::from_ref(egraph);
        let bvi = enode.bvi_with(|x| this.bvi(*x));
        ClassData {
            flags: Pred1::default(),
            bvi,
        }
    }

    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> egg::DidMerge {
        let new = *a | b;
        let changed = DidMerge(*a == new, b == new);
        *a = new;
        if new.flags.is_contr() {
            self.flags |= Pred0::IS_CONTR;
        }
        changed
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
struct ClassData {
    flags: Pred1,
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

impl Ctx {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
#[repr(transparent)]
pub struct TermId(egg::Id);

pub type NodeIx = NodeT<CtxId, TermId>;

impl Language for NodeIx {
    type Discriminant = DiscT<CtxId, TermId>;

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
