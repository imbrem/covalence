use crate::{
    data::term::{Bv, Fv, Node, TmIn},
    fact::Pred1,
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
        LocalStore, ReadCtx, ReadCtxFacts, ReadCtxGraph, ReadLocalFacts, ReadLocalStore,
        ReadLocalTerm, ReadUniv, TermIndex, WriteLocalStore, WriteLocalTerm,
    };
}

/// Traits implemented by an unchecked local store
pub mod local_store_unchecked {
    pub use super::local_store::*;

    pub use super::{
        LocalStoreUnchecked, WriteCtxFactsUnchecked, WriteCtxGraphUnchecked,
        WriteLocalFactsUnchecked, WriteLocalStoreUnchecked,
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
    fn local_may_have_var_from(&self, _ctx: CtxId<Self>, _tm: Ix<Self>, _vars: CtxId<Self>) -> bool {
        true
    }
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

/// A datastore that can read facts about local terms
///
/// This trait is `dyn`-safe:
/// ```rust
/// # use covalence::kernel::*;
/// let ker : &dyn ReadLocalFacts<CtxId=CtxId, Ix = Ix> = &TermDb::new();
/// ```
pub trait ReadLocalFacts: TermIndex {
    // == Typing judgements ==

    /// Get a term's flags in a given context
    fn local_tm_flags(&self, ctx: CtxId<Self>, tm: Ix<Self>) -> Pred1;

    /// Check whether the term `tm` satisfies predicate `pred` in `ctx`
    ///
    /// For details, see the helper methods in [`ReadTermStore`].
    fn local_tm_satisfies(&self, ctx: CtxId<Self>, tm: Ix<Self>, pred: Pred1) -> bool {
        self.local_tm_flags(ctx, tm).contains(pred)
    }

    /// Check whether the term `lhs` is equal to the term `rhs` in `ctx`
    ///
    /// Corresponds to `Ctx.KEq` in `gt3-lean`
    fn local_eq(&self, ctx: CtxId<Self>, lhs: Ix<Self>, rhs: Ix<Self>) -> bool;

    /// Check whether the term `tm` has type `ty` in `ctx`
    ///
    /// Corresponds to `Ctx.KEq` in `gt3-lean`
    fn local_has_ty(&self, ctx: CtxId<Self>, tm: Ix<Self>, ty: Ix<Self>) -> bool;
}

pub trait ReadLocalStore:
    ReadLocalTerm
    + ReadLocalFacts
    + ReadUniv
    + ReadCtx<CtxId<Self>, Ix<Self>>
    + ReadCtxFacts<CtxId<Self>>
    + ReadCtxGraph<CtxId<Self>>
{
}

impl<D> ReadLocalStore for D where
    D: ReadLocalTerm
        + ReadLocalFacts
        + ReadUniv
        + ReadCtx<CtxId<D>, Ix<D>>
        + ReadCtxFacts<CtxId<Self>>
        + ReadCtxGraph<CtxId<D>>
{
}

pub trait WriteLocalStore: WriteLocalTerm + WriteUniv {}

impl<D> WriteLocalStore for D where D: WriteLocalTerm + WriteUniv {}

pub trait LocalStore: ReadLocalStore + WriteLocalStore {}

impl<D> LocalStore for D where D: ReadLocalStore + WriteLocalStore {}

/// A trait implemented by a mutable datastore that can hold _unchecked_ facts about terms in a
/// context.
///
/// This trait is `dyn`-safe:
/// ```rust
/// # use covalence::kernel::*;
/// let db : &dyn WriteLocalFactsUnchecked<CtxId = CtxId, Ix = Ix> = &TermDb::default();
/// ```
pub trait WriteLocalFactsUnchecked: TermIndex {
    // == Typing judgements ==

    /// Set a term's flags
    fn set_tm_flags_unchecked(&mut self, ctx: CtxId<Self>, tm: Ix<Self>, pred: Pred1);

    /// Set two terms as equal in a given context
    fn set_eq_unchecked(&mut self, ctx: CtxId<Self>, lhs: Ix<Self>, rhs: Ix<Self>);

    /// Set a term's type
    fn set_has_ty_unchecked(&mut self, ctx: CtxId<Self>, tm: Ix<Self>, ty: Ix<Self>);

    // == Variable and assumption manipulation ==

    /// Add a variable to the given context
    fn add_var_unchecked(&mut self, ctx: CtxId<Self>, ty: TmId<Self>) -> FvId<Self>;
}

pub trait WriteLocalStoreUnchecked:
    WriteLocalStore
    + WriteLocalFactsUnchecked
    + WriteCtxGraphUnchecked<CtxId<Self>>
    + WriteCtxFactsUnchecked<CtxId<Self>>
{
}

impl<D> WriteLocalStoreUnchecked for D where
    D: WriteLocalStore
        + WriteLocalFactsUnchecked
        + WriteCtxGraphUnchecked<CtxId<D>>
        + WriteCtxFactsUnchecked<CtxId<D>>
{
}

pub trait LocalStoreUnchecked: ReadLocalStore + WriteLocalStoreUnchecked {}

impl<D> LocalStoreUnchecked for D where D: ReadLocalStore + WriteLocalStoreUnchecked {}
