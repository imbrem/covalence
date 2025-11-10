use std::{
    collections::BTreeMap,
    fmt::{self, Debug},
    ops::BitOr,
};

use covalence_kernel::{
    data::term::{Bv, DiscT, Fv},
    store::{AddParentFailure, AddVarFailure},
};
use egg::{Analysis, DidMerge, EGraph, Id, Language};

use covalence_kernel::fact::{Pred0, Pred1};
use indexmap::IndexSet;

use crate::{Ix, NodeIx};

use super::{CtxId, FvId, TmId};

#[derive(Debug, Clone)]
#[repr(transparent)]
pub struct Ctx {
    e: EGraph<InnerNode, CtxData>,
}

fn ix_id(ix: Ix) -> Id {
    Id::from(ix.0 as usize)
}

fn id_ix(id: Id) -> Ix {
    Ix(usize::from(id) as u32)
}

impl Ctx {
    pub fn new_ctx() -> Ctx {
        Ctx {
            e: EGraph::new(CtxData::default()).with_explanations_enabled(),
        }
    }

    pub fn add_parent_unchecked(&mut self, parent: CtxId) -> Result<(), AddParentFailure> {
        if self.ctx_flags().contains(Pred0::PARENTS_SEALED) {
            return Err(AddParentFailure);
        }
        self.e.analysis.parents.insert(parent);
        Ok(())
    }

    pub fn set_this(&mut self, this: CtxId) {
        self.e.analysis.this = Some(this);
    }

    pub fn add(&mut self, node: NodeIx) -> Ix {
        // NOTE: an uncanonical insertion is necessary to roundtrip with lookup
        let result = id_ix(self.e.add_uncanonical(InnerNode(node)));
        self.e.analysis.node_to_id.insert(InnerNode(node), result);
        result
    }

    pub fn node(&self, ix: Ix) -> NodeIx {
        let result = self.e.id_to_node(ix_id(ix));
        debug_assert_eq!(
            self.e.analysis.node_to_id.get(result),
            Some(&ix),
            "Ctx::node and Ctx::add are out of sync",
        );
        result.0
    }

    pub fn lookup(&self, node: NodeIx) -> Option<Ix> {
        let result = self.e.analysis.node_to_id.get(&InnerNode(node)).copied();
        debug_assert_eq!(
            result.map(|id| self.node(id)),
            if result.is_none() { None } else { Some(node) },
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

    pub fn is_locally_empty(&self) -> bool {
        self.e.analysis.vars.is_empty()
    }

    pub fn num_parents(&self) -> u32 {
        self.e.analysis.parents.len() as u32
    }

    pub fn parent(&self, n: u32) -> Option<CtxId> {
        self.e.analysis.parents.get_index(n as usize).copied()
    }

    pub fn is_parent(&self, ctx: CtxId) -> bool {
        self.e.analysis.parents.contains(&ctx)
    }

    pub fn ctx_flags(&self) -> Pred0 {
        self.e.analysis.flags
    }

    pub fn set_ctx_flags(&mut self, flags: Pred0) -> bool {
        let old_flags = self.e.analysis.flags;
        self.e.analysis.flags |= flags;
        self.e.analysis.flags != old_flags
    }

    pub fn tm_flags(&self, tm: Ix) -> Pred1 {
        self.e[ix_id(tm)].data.flags
    }

    pub fn eq_in(&self, lhs: Ix, rhs: Ix) -> bool {
        self.e.find(ix_id(lhs)) == self.e.find(ix_id(rhs))
    }

    pub fn set_tm_flags_unchecked(&mut self, tm: Ix, flags: Pred1) -> bool {
        let mut data = self.e[ix_id(tm)].data;
        let old_flags = data.flags;
        data.flags |= flags;
        if data.flags != old_flags {
            self.e.set_analysis_data(ix_id(tm), data);
            true
        } else {
            false
        }
    }

    pub fn set_eq_unchecked(&mut self, lhs: Ix, rhs: Ix) {
        self.e.union(ix_id(lhs), ix_id(rhs));
    }

    pub fn add_var_unchecked(&mut self, ctx: CtxId, ty: TmId) -> Result<FvId, AddVarFailure> {
        // NOTE: this overflow should be impossible due to limitations of the E-graph, but better
        // safe than sorry...
        if self.ctx_flags().contains(Pred0::ASSUME_SEALED) {
            return Err(AddVarFailure);
        }
        let ix: u32 = self
            .e
            .analysis
            .vars
            .len()
            .try_into()
            .expect("variable index overflow");
        self.e.analysis.vars.push(ty);
        Ok(Fv { ctx, ix })
    }

    // fn from_mut(this: &mut EGraph<Node, CtxData>) -> &mut Self {
    //     // SAFETY: due to `#[repr(transparent)]`
    //     unsafe { std::mem::transmute(this) }
    // }

    pub fn bvi(&self, id: Ix) -> Bv {
        self.e[Id::from(id.0 as usize)].data.bvi
    }

    pub fn set_bvi_unchecked(&mut self, ix: Ix, bvi: Bv) {
        let mut data = self.e[ix_id(ix)].data;
        if bvi >= data.bvi {
            return;
        }
        data.bvi = bvi;
        self.e.set_analysis_data(ix_id(ix), data);
    }
}

#[derive(Debug, Clone, Default)]
struct CtxData {
    /// Pointer to self
    this: Option<CtxId>,
    /// This context's parents
    parents: IndexSet<CtxId>,
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

#[derive(Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
#[repr(transparent)]
struct InnerNode(NodeIx);

impl Debug for InnerNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "TODO")
    }
}

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
