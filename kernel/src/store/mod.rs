use crate::{
    data::term::{Bv, Fv, Node, TmIn},
    fact::{CheckFactIn, Eqn, Holds, Pred0},
};

pub use crate::univ::{ReadUniv, WriteUniv};

pub mod ctx;

pub use ctx::*;

/// A term database with a given index kind
pub trait TermIndex {
    /// The context identifier type
    type CtxId: Copy + PartialEq;
    /// A local index for a term
    type Ix: Copy + PartialEq;
}

pub type CtxId<D> = <D as TermIndex>::CtxId;

pub type Ix<D> = <D as TermIndex>::Ix;

pub type TmId<D> = TmIn<CtxId<D>, Ix<D>>;

pub type NodeIx<D> = Node<CtxId<D>, Ix<D>>;

pub type FvId<D> = Fv<CtxId<D>>;

/// Traits implemented by a local store
pub mod local_store {
    pub use super::{
        LocalStore, ReadCtx, ReadCtxGraph, ReadLocalStore, ReadLocalTerm, ReadUniv, TermIndex,
        WriteLocalStore, WriteLocalTerm,
    };
}

/// Traits implemented by an unchecked local store
pub mod local_store_unchecked {
    pub use super::local_store::*;

    pub use super::{
        AddParentUnchecked, AddVarUnchecked, LocalStoreUnchecked, WriteLocalStoreUnchecked,
    };
}

/// A datastore that can read local terms
///
/// This trait is `dyn`-safe:
/// ```rust
/// # use covalence::kernel::*;
/// let ker : &dyn ReadLocalTerm<CtxId = CtxId, Ix = Ix> = &TermDb::new();
/// ```
pub trait ReadLocalTerm: TermIndex {
    // == Terms ==

    /// Get the node corresponding to a term
    fn node(&self, ctx: CtxId<Self>, tm: Ix<Self>) -> &NodeIx<Self>;

    /// Lookup a term in the store
    fn lookup(&self, ctx: CtxId<Self>, tm: NodeIx<Self>) -> Option<Ix<Self>>;

    /// Lookup an import in `self`
    ///
    /// Does _not_ traverse import chains
    fn lookup_import(&self, ctx: CtxId<Self>, tm: TmId<Self>) -> Option<Ix<Self>> {
        if tm.ctx == ctx {
            Some(tm.ix)
        } else {
            self.lookup(ctx, Node::Import(tm))
        }
    }

    // == Syntactic information ==

    /// Get an upper bound on the de-Bruijn indices visible in `tm`
    fn local_bvi(&self, ctx: CtxId<Self>, tm: Ix<Self>) -> Bv;

    /// Check whether the term `tm` may depend on the variable `var`
    fn local_may_have_var(&self, ctx: CtxId<Self>, tm: Ix<Self>, var: FvId<Self>) -> bool {
        self.local_may_have_var_from(ctx, tm, var.ctx)
    }

    /// Check whether the term `tm` may depend on any variable from the context `vars`
    fn local_may_have_var_from(
        &self,
        _ctx: CtxId<Self>,
        _tm: Ix<Self>,
        _vars: CtxId<Self>,
    ) -> bool {
        true
    }
}

pub trait ReadLocalFacts:
    TermIndex + CheckFactIn<CtxId<Self>, Holds<Ix<Self>>> + CheckFactIn<CtxId<Self>, Eqn<Ix<Self>>>
{
}

impl<D> ReadLocalFacts for D where
    D: TermIndex + CheckFactIn<CtxId<D>, Holds<Ix<D>>> + CheckFactIn<CtxId<D>, Eqn<Ix<D>>>
{
}

/// A trait implemented by a datastore that can create hash-consed terms
pub trait WriteLocalTerm: TermIndex {
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
    fn new_ctx(&mut self) -> CtxId<Self>;

    /// Directly insert a term into the store, returning a handle to it
    fn cons_node_ix(&mut self, ctx: CtxId<Self>, tm: NodeIx<Self>) -> Ix<Self>;

    // == Congruence management ==

    /// Propagate congruence information _within_ a context
    fn propagate_in(&mut self, ctx: CtxId<Self>) -> usize;
}

pub trait ReadLocalStore:
    ReadLocalTerm
    + ReadLocalFacts
    + ReadCtx<CtxId<Self>, VarId = TmId<Self>>
    + ReadCtxGraph<CtxId<Self>>
    + CheckFactIn<CtxId<Self>, Pred0>
    + ReadUniv
{
}

impl<D> ReadLocalStore for D where
    D: ReadLocalTerm
        + ReadLocalFacts
        + ReadCtx<CtxId<D>, VarId = TmId<D>>
        + ReadCtxGraph<CtxId<D>>
        + CheckFactIn<CtxId<D>, Pred0>
        + ReadUniv
{
}

pub trait WriteLocalStore: WriteLocalTerm + WriteUniv {}

impl<D> WriteLocalStore for D where D: WriteLocalTerm + WriteUniv {}

pub trait LocalStore: ReadLocalStore + WriteLocalStore {}

impl<D> LocalStore for D where D: ReadLocalStore + WriteLocalStore {}

pub trait WriteLocalStoreUnchecked:
    WriteLocalStore + AddVarUnchecked<CtxId<Self>, TmId<Self>> + AddParentUnchecked<CtxId<Self>>
{
}

impl<D> WriteLocalStoreUnchecked for D where
    D: WriteLocalStore + AddVarUnchecked<CtxId<Self>, TmId<Self>> + AddParentUnchecked<CtxId<D>>
{
}

pub trait LocalStoreUnchecked: ReadLocalStore + WriteLocalStoreUnchecked {}

impl<D> LocalStoreUnchecked for D where D: ReadLocalStore + WriteLocalStoreUnchecked {}
