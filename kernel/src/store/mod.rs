use crate::{
    data::term::{Bv, Node},
    fact::{CheckFactIn, Eqn, Holds, Pred0},
};

pub use crate::univ::{ReadUniv, WriteUniv};

pub mod ctx;

pub use ctx::*;

pub mod index;

pub use index::*;

/// Traits implemented by a local store
pub mod local_store {
    pub use super::{
        LocalStore, ReadCtx, ReadCtxGraph, ReadLocalStore, ReadLocalTerm, ReadUniv, SealCtx,
        TermIndex, WriteLocalStore, WriteLocalTerm,
    };
}

/// Traits implemented by an unchecked local store
pub mod local_store_unchecked {
    pub use super::local_store::*;

    pub use super::{
        AddParentUnchecked, AddVarUnchecked, LocalStoreUnchecked, WriteLocalStoreUnchecked,
    };
}

/// A trait implemented by a datastore exposing term indices
pub trait TermStore {
    /// The underlying data store
    type Store: TermIndex;
}

impl<D: TermIndex> TermStore for D {
    type Store = D;
}

/// A datastore that can read local terms
pub trait ReadLocalTerm: TermStore {
    // == Terms ==

    /// Get the node corresponding to a term
    fn node(&self, ctx: CtxId<Self::Store>, tm: Ix<Self::Store>) -> &NodeIx<Self::Store>;

    /// Lookup a term in the store
    fn lookup(&self, ctx: CtxId<Self::Store>, tm: NodeIx<Self::Store>) -> Option<Ix<Self::Store>>;

    /// Lookup an import in `self`
    ///
    /// Does _not_ traverse import chains
    fn lookup_import(
        &self,
        ctx: CtxId<Self::Store>,
        tm: TmId<Self::Store>,
    ) -> Option<Ix<Self::Store>> {
        if tm.ctx == ctx {
            Some(tm.ix)
        } else {
            self.lookup(ctx, Node::Quote(tm))
        }
    }

    // == Syntactic information ==

    /// Get an upper bound on the de-Bruijn indices visible in `tm`
    fn local_bvi(&self, ctx: CtxId<Self::Store>, tm: Ix<Self::Store>) -> Bv;

    /// Check whether the term `tm` may depend on the variable `var`
    fn local_may_have_var(
        &self,
        ctx: CtxId<Self::Store>,
        tm: Ix<Self::Store>,
        var: FvId<Self::Store>,
    ) -> bool {
        self.local_may_have_var_from(ctx, tm, var.ctx)
    }

    /// Check whether the term `tm` may depend on any variable from the context `vars`
    fn local_may_have_var_from(
        &self,
        _ctx: CtxId<Self::Store>,
        _tm: Ix<Self::Store>,
        _vars: CtxId<Self::Store>,
    ) -> bool {
        true
    }
}

pub trait ReadLocalFacts:
    TermStore
    + CheckFactIn<CtxId<Self::Store>, Holds<Ix<Self::Store>>>
    + CheckFactIn<CtxId<Self::Store>, Eqn<Ix<Self::Store>>>
{
}

impl<D> ReadLocalFacts for D where
    D: TermIndex + CheckFactIn<CtxId<D>, Holds<Ix<D>>> + CheckFactIn<CtxId<D>, Eqn<Ix<D>>>
{
}

/// A trait implemented by a datastore that can create hash-consed terms
pub trait WriteLocalTerm: TermStore {
    // == Term management ==

    /// Create a new context in this store
    ///
    /// # Example
    /// ```rust
    /// # use covalence::kernel::*;
    /// # let mut ker = Kernel::default();
    /// let ctx = ker.new_ctx();
    /// assert_eq!(ker.num_vars(ctx), 0);
    /// ```
    fn new_ctx(&mut self) -> CtxId<Self::Store>;

    /// Directly insert a term into the store, returning a handle to it
    fn cons_node_ix(&mut self, ctx: CtxId<Self::Store>, tm: NodeIx<Self::Store>)
    -> Ix<Self::Store>;

    // == Congruence management ==

    /// Propagate congruence information _within_ a context
    fn propagate_in(&mut self, ctx: CtxId<Self::Store>) -> usize;
}

pub trait ReadLocalStore:
    ReadLocalTerm
    + ReadLocalFacts
    + ReadCtx<CtxId<Self::Store>, VarId = TmId<Self::Store>>
    + ReadCtxGraph<CtxId<Self::Store>>
    + CheckFactIn<CtxId<Self::Store>, Pred0>
    + ReadUniv
{
}

impl<D> ReadLocalStore for D where
    D: ReadLocalTerm
        + ReadLocalFacts
        + ReadCtx<CtxId<D::Store>, VarId = TmId<D::Store>>
        + ReadCtxGraph<CtxId<D::Store>>
        + CheckFactIn<CtxId<D::Store>, Pred0>
        + ReadUniv
{
}

pub trait WriteLocalStore: WriteLocalTerm + WriteUniv + SealCtx<CtxId<Self::Store>> {}

impl<D> WriteLocalStore for D where D: WriteLocalTerm + WriteUniv + SealCtx<CtxId<D::Store>> {}

pub trait LocalStore: ReadLocalStore + WriteLocalStore {}

impl<D> LocalStore for D where D: ReadLocalStore + WriteLocalStore {}

pub trait WriteLocalStoreUnchecked:
    WriteLocalStore
    + AddVarUnchecked<CtxId<Self::Store>, TmId<Self::Store>>
    + AddParentUnchecked<CtxId<Self::Store>>
{
}

impl<D> WriteLocalStoreUnchecked for D where
    D: WriteLocalStore
        + AddVarUnchecked<CtxId<D::Store>, TmId<D::Store>>
        + AddParentUnchecked<CtxId<D::Store>>
{
}

pub trait LocalStoreUnchecked: ReadLocalStore + WriteLocalStoreUnchecked {}

impl<D> LocalStoreUnchecked for D where D: ReadLocalStore + WriteLocalStoreUnchecked {}
