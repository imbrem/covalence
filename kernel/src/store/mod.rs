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
pub trait ReadLocalTerm<D: TermIndex> {
    // == Terms ==

    /// Get the value corresponding to the given term, traversing import chains
    fn val(&self, ctx: CtxId<D>, tm: Ix<D>) -> TmId<D> {
        if let Node::Quote(val) = self.node(ctx, tm) {
            return self.val(val.ctx, val.ix);
        }
        TmId { ctx, ix: tm }
    }

    /// Get the node corresponding to a term
    fn node(&self, ctx: CtxId<D>, tm: Ix<D>) -> NodeIx<D>;

    /// Lookup a term in the store
    fn lookup(&self, ctx: CtxId<D>, tm: NodeIx<D>) -> Option<Ix<D>>;

    /// Lookup an import in `self`
    ///
    /// Does _not_ traverse import chains
    fn lookup_import(&self, ctx: CtxId<D>, tm: TmId<D>) -> Option<Ix<D>> {
        if tm.ctx == ctx {
            Some(tm.ix)
        } else {
            self.lookup(ctx, Node::Quote(tm))
        }
    }

    // == Syntactic information ==

    /// Get an upper bound on the de-Bruijn indices visible in `tm`
    fn local_bvi(&self, ctx: CtxId<D>, tm: Ix<D>) -> Bv;

    /// Check whether the term `tm` may depend on the variable `var`
    fn local_may_have_var(&self, ctx: CtxId<D>, tm: Ix<D>, var: FvId<D>) -> bool {
        self.local_may_have_var_from(ctx, tm, var.ctx)
    }

    /// Check whether the term `tm` may depend on any variable from the context `vars`
    fn local_may_have_var_from(&self, _ctx: CtxId<D>, _tm: Ix<D>, _vars: CtxId<D>) -> bool {
        true
    }
}

pub trait ReadLocalFacts<D: TermIndex>:
    CheckFactIn<CtxId<D>, Holds<Ix<D>>> + CheckFactIn<CtxId<D>, Eqn<Ix<D>>>
{
}

impl<K, D> ReadLocalFacts<D> for K
where
    D: TermIndex,
    K: CheckFactIn<CtxId<D>, Holds<Ix<D>>> + CheckFactIn<CtxId<D>, Eqn<Ix<D>>>,
{
}

/// A trait implemented by a datastore that can create hash-consed terms
pub trait WriteLocalTerm<D: TermIndex> {
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
    fn new_ctx(&mut self) -> CtxId<D>;

    /// Directly insert a term into the store, returning a handle to it
    fn cons_node_ix(&mut self, ctx: CtxId<D>, tm: NodeIx<D>) -> Ix<D>;

    // == Congruence management ==

    /// Propagate congruence information _within_ a context
    fn propagate_in(&mut self, ctx: CtxId<D>) -> usize;
}

pub trait ReadLocalStore<D: TermIndex>:
    ReadLocalTerm<D>
    + ReadLocalFacts<D>
    + ReadCtx<CtxId<D>, VarId = TmId<D>>
    + ReadCtxGraph<CtxId<D>>
    + CheckFactIn<CtxId<D>, Pred0>
    + ReadUniv
{
}

impl<K, D> ReadLocalStore<D> for K
where
    D: TermIndex,
    K: ReadLocalTerm<D>
        + ReadLocalFacts<D>
        + ReadCtx<CtxId<D>, VarId = TmId<D>>
        + ReadCtxGraph<CtxId<D>>
        + CheckFactIn<CtxId<D>, Pred0>
        + ReadUniv,
{
}

pub trait WriteLocalStore<D: TermIndex>: WriteLocalTerm<D> + WriteUniv + SealCtx<CtxId<D>> {}

impl<K, D> WriteLocalStore<D> for K
where
    D: TermIndex,
    K: WriteLocalTerm<D> + WriteUniv + SealCtx<CtxId<D>>,
{
}

pub trait LocalStore<D: TermIndex>: ReadLocalStore<D> + WriteLocalStore<D> {}

impl<K, D> LocalStore<D> for K
where
    D: TermIndex,
    K: ReadLocalStore<D> + WriteLocalStore<D>,
{
}

pub trait WriteLocalStoreUnchecked:
    TermIndex
    + Sized
    + WriteLocalStore<Self>
    + AddVarUnchecked<CtxId<Self>, TmId<Self>>
    + AddParentUnchecked<CtxId<Self>>
{
}

impl<D> WriteLocalStoreUnchecked for D where
    D: TermIndex
        + WriteLocalStore<D>
        + AddVarUnchecked<CtxId<D>, TmId<D>>
        + AddParentUnchecked<CtxId<D>>
{
}

pub trait LocalStoreUnchecked: ReadLocalStore<Self> + WriteLocalStoreUnchecked {}

impl<D> LocalStoreUnchecked for D where D: ReadLocalStore<D> + WriteLocalStoreUnchecked {}
