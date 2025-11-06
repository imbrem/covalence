use std::{collections::BTreeMap, ops::BitOr};

use covalence_kernel::data::term::{Bv, DiscT, Fv, Node};
use egg::{Analysis, DidMerge, EGraph, Language};

use covalence_kernel::fact::{Pred0, Pred1};

use super::{CtxId, FvId, TmId};

#[derive(Debug, Clone)]
#[repr(transparent)]
pub struct Ctx {
    e: EGraph<InnerNode, CtxData>,
}

impl Ctx {
    pub fn new_ctx() -> Ctx {
        Ctx {
            e: EGraph::new(CtxData::default()).with_explanations_enabled(),
        }
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

    pub fn add(&mut self, node: NodeIx) -> Ix {
        // NOTE: an uncanonical insertion is necessary to roundtrip with lookup
        let result = Ix(self.e.add_uncanonical(InnerNode(node)));
        self.e.analysis.node_to_id.insert(InnerNode(node), result);
        result
    }

    pub fn node(&self, id: Ix) -> &NodeIx {
        let result = self.e.id_to_node(id.0);
        debug_assert_eq!(
            self.e.analysis.node_to_id.get(result),
            Some(&id),
            "Ctx::node and Ctx::add are out of sync",
        );
        &result.0
    }

    pub fn lookup(&self, node: NodeIx) -> Option<Ix> {
        let result = self.e.analysis.node_to_id.get(&InnerNode(node)).copied();
        debug_assert_eq!(
            result.map(|id| self.node(id)),
            if result.is_none() { None } else { Some(&node) },
            "Ctx::node and Ctx::add are out of sync",
        );
        result
    }

    pub fn var_ty(&self, ix: u32) -> Option<TmId> {
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

    pub fn tm_flags(&self, tm: Ix) -> Pred1 {
        self.e[tm.0].data.flags
    }

    pub fn eq_in(&self, lhs: Ix, rhs: Ix) -> bool {
        self.e.find(lhs.0) == self.e.find(rhs.0)
    }

    pub fn has_ty(&self, tm: Ix, ty: Ix) -> bool {
        self.e
            .lookup(InnerNode(NodeIx::HasTy([tm, ty])))
            .is_some_and(|id| self.e[id].data.flags.contains(Pred1::IS_WF))
    }

    pub fn set_flags_unchecked(&mut self, tm: Ix, flags: Pred1) -> bool {
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

    pub fn set_eq_unchecked(&mut self, lhs: Ix, rhs: Ix) {
        self.e.union(lhs.0, rhs.0);
    }

    pub fn set_has_ty_unchecked(&mut self, tm: Ix, ty: Ix) {
        let id = self.add(NodeIx::HasTy([tm, ty]));
        self.set_flags_unchecked(id, Pred1::IS_WF);
    }

    pub fn add_var_unchecked(&mut self, ctx: CtxId, ty: TmId) -> FvId {
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

    // fn from_mut(this: &mut EGraph<Node, CtxData>) -> &mut Self {
    //     // SAFETY: due to `#[repr(transparent)]`
    //     unsafe { std::mem::transmute(this) }
    // }

    pub fn bvi(&self, id: Ix) -> Bv {
        self.e[id.0].data.bvi
    }

    pub fn set_bvi_unchecked(&mut self, id: Ix, bvi: Bv) {
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
    vars: Vec<TmId>,
    /// A map from nodes to their TermId
    ///
    /// TODO: remove hack, but required for now for correctness of `lookup`
    ///
    /// Donald Knuth smiles on me this day, for avoiding temptation.
    node_to_id: BTreeMap<InnerNode, Ix>,
}

impl Analysis<InnerNode> for CtxData {
    type Data = ClassData;

    fn make(_egraph: &mut EGraph<InnerNode, Self>, _enode: &InnerNode) -> Self::Data {
        ClassData::default()
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
pub struct Ix(egg::Id);

pub type NodeIx = Node<CtxId, Ix>;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
#[repr(transparent)]
struct InnerNode(NodeIx);

impl Language for InnerNode {
    type Discriminant = DiscT<CtxId, Ix>;

    fn discriminant(&self) -> Self::Discriminant {
        self.0.disc()
    }

    fn matches(&self, other: &Self) -> bool {
        self.0.disc() == other.0.disc()
    }

    fn children(&self) -> &[egg::Id] {
        // SAFETY: a `TermId` has the same representation as an `egg::Id`
        let children = self.0.children();
        unsafe {
            std::slice::from_raw_parts(children as *const _ as *const egg::Id, children.len())
        }
    }

    fn children_mut(&mut self) -> &mut [egg::Id] {
        // SAFETY: a `TermId` has the same representation as an `egg::Id`
        let children = self.0.children_mut();
        unsafe {
            std::slice::from_raw_parts_mut(children as *mut _ as *mut egg::Id, children.len())
        }
    }
}
