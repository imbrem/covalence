use crate::{
    fact::Pred1,
    term::{Bv, Fv, NodeT, NodeVT, Val},
};

pub use crate::univ::{ReadUniv, WriteUniv};

pub use crate::ctx::*;

/// A term database with a given index kind
pub trait IndexTypes {
    /// The context identifier type
    type CtxId: Copy;
    /// The term identifier type
    type TermId: Copy;
}

pub type CtxId<D> = <D as IndexTypes>::CtxId;

pub type TermId<D> = <D as IndexTypes>::TermId;

pub type ValId<D> = Val<CtxId<D>, TermId<D>>;

pub type NodeIx<D> = NodeT<CtxId<D>, TermId<D>>;

pub type FvId<D> = Fv<CtxId<D>>;

/// A datastore that can read terms and universe levels
///
/// This trait is `dyn`-safe:
/// ```rust
/// # use covalence::kernel::*;
/// let ker : &dyn ReadTermIndex<CtxId = CtxId, TermId = TermId> = &TermDb::new();
/// ```
/// Note that this trait is _not_ implemented by the kernel, to avoid re-compiling read-only
/// functions for different kernel wrappers:
/// ```rust,compile_fail
/// # use covalence::kernel::*;
/// let ker : &dyn ReadTermIndex<CtxId = CtxId, TermId = TermId> = &Kernel::new();
/// ```
pub trait ReadTermIndex: IndexTypes + ReadUniv {
    // == Terms ==

    /// Get the value corresponding to a term
    fn val(&self, ctx: CtxId<Self>, tm: TermId<Self>) -> ValId<Self>;

    /// Get the node corresponding to a term
    fn node(&self, ctx: CtxId<Self>, tm: TermId<Self>) -> &NodeIx<Self>;

    /// Lookup a term in the store
    fn lookup(&self, ctx: CtxId<Self>, tm: NodeIx<Self>) -> Option<TermId<Self>>;

    /// Lookup an import of a term into another context, returning a handle to it if it exists
    fn lookup_import(&self, ctx: CtxId<Self>, val: ValId<Self>) -> Option<TermId<Self>>;

    // == Syntactic information ==

    /// Get an upper bound on the de-Bruijn indices visible in `tm`
    ///
    /// TODO: reference lean
    fn bvi(&self, ctx: CtxId<Self>, tm: TermId<Self>) -> Bv;

    /// Check whether the term `tm` may depend on the variable `var`
    fn may_have_var(&self, ctx: CtxId<Self>, tm: TermId<Self>, var: FvId<Self>) -> bool {
        self.may_have_var_from(ctx, tm, var.ctx)
    }

    /// Check whether the term `tm` may depend on any variable from the context `vars`
    fn may_have_var_from(
        &self,
        _ctx: CtxId<Self>,
        _tm: TermId<Self>,
        _vars: CtxId<Self>,
    ) -> bool {
        true
    }

    // == Syntactic relations ==

    /// Check whether two values resolve to the same value, after following imports
    fn deref_eq(&self, lhs: ValId<Self>, rhs: ValId<Self>) -> bool;

    /// Check whether two values are equal up to first imports
    fn cons_eq(&self, lhs: ValId<Self>, rhs: ValId<Self>) -> bool;
}

impl<C: Copy, T> Val<C, T> {
    /// Get the base value pointed to by this value
    pub fn val(self, store: &(impl ReadTermIndex<CtxId = C, TermId = T> + ?Sized)) -> Val<C, T> {
        store.val(self.ctx, self.tm)
    }
}

impl<C: Copy, T: Copy> Val<C, T> {
    /// Get the node in `self.ctx` corresponding to this value
    pub fn node_ix(
        self,
        store: &(impl ReadTermIndex<CtxId = C, TermId = T> + ?Sized),
    ) -> NodeT<C, T> {
        *store.node(self.ctx, self.tm)
    }

    /// Get the node corresponding to this value
    pub fn node_val(
        self,
        store: &(impl ReadTermIndex<CtxId = C, TermId = T> + ?Sized),
    ) -> NodeVT<C, T> {
        self.node_ix(store).node_val_in(self.ctx, store)
    }

    /// Get the node corresponding to this value
    pub fn raw_node_val(
        self,
        store: &(impl ReadTermIndex<CtxId = C, TermId = T> + ?Sized),
    ) -> NodeVT<C, T> {
        self.node_ix(store).raw_node_val_in(self.ctx)
    }
}

/// A trait implemented by a datastore that can create hash-consed terms
///
/// This trait is `dyn`-safe:
/// ```rust
/// # use covalence::kernel::*;
/// let ker : &dyn WriteTermIndex<CtxId = CtxId, TermId = TermId> = &Kernel::default();
/// ```
pub trait WriteTermIndex: IndexTypes + WriteUniv {
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

    /// Create a new context in this store with the given parent
    ///
    /// # Example
    /// ```rust
    /// # use covalence::kernel::*;
    /// # let mut ker = Kernel::default();
    /// let parent = ker.new_ctx();
    /// let child = ker.with_parent(parent);
    /// // This is true since both contexts are currently empty
    /// assert!(ker.is_subctx(parent, child));
    /// assert!(ker.is_subctx(child, parent));
    /// ```
    fn with_parent(&mut self, parent: CtxId<Self>) -> CtxId<Self>;

    /// Directly insert a term into the store, returning a handle to it
    fn add_raw(&mut self, ctx: CtxId<Self>, tm: NodeIx<Self>) -> TermId<Self>;

    /// Import a term into another context, returning a handle to it
    ///
    /// This automatically traverses import chains, and in particular:
    /// - If `src[tm] := import(src2, tm)`, then `import(ctx, src, tm) => import(ctx, src2, tm)`
    /// - `import(ctx, ctx, tm)` returns `tm`
    /// - otherwise, return an `Import` node
    fn import(&mut self, ctx: CtxId<Self>, val: ValId<Self>) -> TermId<Self>;

    // == Congruence management ==

    /// Propagate congruence information _within_ a context
    fn propagate_in(&mut self, ctx: CtxId<Self>) -> usize;
}

impl<C: Copy, T> NodeT<C, T> {
    /// Interpret this node in the given context
    pub fn val(self, ctx: C, store: &mut (impl RwTermDb<C, T> + ?Sized)) -> Val<C, T> {
        match self {
            NodeT::Import(val) => val.val(store.read()),
            this => Val {
                ctx,
                tm: store.add_raw(ctx, this),
            },
        }
    }

    /// Interpret this node in the given context
    pub fn val_ix(self, ctx: C, store: &mut (impl RwTermDb<C, T> + ?Sized)) -> T {
        match self {
            NodeT::Import(val) => store.import(ctx, val),
            this => store.add_raw(ctx, this),
        }
    }

    /// Interpret this node in the given context
    pub fn node_val_in(
        self,
        ctx: C,
        store: &(impl ReadTermIndex<CtxId = C, TermId = T> + ?Sized),
    ) -> NodeVT<C, T> {
        self.map_subterms(|tm| store.val(ctx, tm))
    }

    /// Tag this node's syntactic children with the given context
    pub fn raw_node_val_in(self, ctx: C) -> NodeVT<C, T> {
        self.map_subterms(|tm| Val { ctx, tm })
    }
}

/// A datastore that can read contexts
///
/// This trait is `dyn`-safe:
/// ```rust
/// # use covalence::kernel::*;
/// let ker : &dyn ReadCtx<CtxId, TermId> = &TermDb::new();
/// ```
/// Note that this trait is _not_ implemented by the kernel, to avoid re-compiling read-only
/// functions for different kernel wrappers:
/// ```rust,compile_fail
/// # use covalence::kernel::*;
/// let ker : &dyn ReadCtx<CtxId, TermId> = &Kernel::new();
/// ```
pub trait ReadCtx<C, T> {
    /// Get the number of variables this context has
    fn num_vars(&self, ctx: C) -> u32;

    /// Lookup the type of a variable
    fn var_ty(&self, var: Fv<C>) -> Val<C, T>;
}

impl<C: Copy> Fv<C> {
    /// Get this variable as a value
    pub fn val<T>(self, store: &(impl ReadTermIndex<CtxId = C, TermId = T> + ?Sized)) -> Val<C, T> {
        Val {
            ctx: self.ctx,
            tm: store
                .lookup(self.ctx, NodeT::Fv(self))
                .expect("valid variables should exist in their contexts"),
        }
    }

    /// Get the type of this variable
    pub fn ty<T>(self, store: &(impl ReadCtx<C, T> + ?Sized)) -> Val<C, T> {
        store.var_ty(self)
    }

    // /// Infer the flags of this variable in the given context
    // pub fn infer_flags<T: Copy>(
    //     self,
    //     ctx: C,
    //     store: &(impl ReadTermStore<C, T> + ?Sized),
    // ) -> Pred1 {
    //     // Reject invalid or ill-scoped variables
    //     if store.num_vars(self.ctx) <= self.ix || !store.is_ancestor(ctx, self.ctx) {
    //         return Pred1::default();
    //     }
    //     if ReadTermFacts::<C, Val<C, T>>::is_univ(store, ctx, self.ty(store)) {
    //         Pred1::IS_TY
    //     } else {
    //         Pred1::IS_WF
    //     }
    // }
}

/// A datastore that can read facts about terms-in-context.
///
/// This trait is `dyn`-safe:
/// ```rust
/// # use covalence::kernel::*;
/// let ker : &dyn ReadTermFacts<CtxId, TermId> = &TermDb::new();
/// ```
/// Note that this trait is _not_ implemented by the kernel, to avoid re-compiling read-only
/// functions for different kernel wrappers:
/// ```rust,compile_fail
/// # use covalence::kernel::*;
/// let ker : &dyn ReadTermFacts<CtxId, TermId> = &Kernel::new();
/// ```
pub trait ReadTermFacts<C, T>: ReadCtxFacts<C> {
    // == Typing judgements ==

    /// Get a term's flags in a given context
    fn tm_flags(&self, ctx: C, tm: T) -> Pred1;

    /// Check whether the term `tm` satisfies predicate `pred` in `ctx`
    ///
    /// For details, see the helper methods in [`ReadTermStore`].
    fn tm_satisfies(&self, ctx: C, tm: T, pred: Pred1) -> bool {
        self.tm_flags(ctx, tm).contains(pred)
    }

    /// Check whether the term `lhs` is equal to the term `rhs` in `ctx`
    ///
    /// Corresponds to `Ctx.KEq` in `gt3-lean`
    fn eq_in(&self, ctx: C, lhs: T, rhs: T) -> bool;

    /// Check whether the term `tm` has type `ty` in `ctx`
    ///
    /// Corresponds to `Ctx.KHasTy` in `gt3-lean`
    fn has_ty(&self, ctx: C, tm: T, ty: T) -> bool;

    /// Check whether the term `tm` is well-formed in `ctx`
    ///
    /// Corresponds to `Ctx.KIsWf` in `gt3-lean`
    fn is_wf(&self, ctx: C, tm: T) -> bool {
        self.tm_satisfies(ctx, tm, Pred1::IS_WF)
    }

    /// Check whether the term `tm` is a type in the context `ctx`
    ///
    /// Corresponds to `Ctx.KIsTy` in `gt3-lean`
    fn is_ty(&self, ctx: C, tm: T) -> bool {
        self.tm_satisfies(ctx, tm, Pred1::IS_TY)
    }

    /// Check whether the term `tm` is a proposition in the context `ctx`
    ///
    /// Corresponds to `Ctx.KIsProp` in `gt3-lean`
    fn is_prop(&self, ctx: C, tm: T) -> bool {
        self.tm_satisfies(ctx, tm, Pred1::IS_PROP)
    }

    /// Check whether the term `tm` is an inhabited type in the context `ctx`
    ///
    /// Corresponds to `Ctx.KIsInhab` in `gt3-lean`
    fn is_inhab(&self, ctx: C, tm: T) -> bool {
        self.tm_satisfies(ctx, tm, Pred1::IS_INHAB)
    }

    /// Check whether the term `tm` is an empty type in the context `ctx`
    ///
    /// TODO: reference Lean
    fn is_empty(&self, ctx: C, tm: T) -> bool {
        self.tm_satisfies(ctx, tm, Pred1::IS_EMPTY)
    }

    /// Check whether the term `tm` is the true proposition in the context `ctx`
    ///
    /// TODO: reference Lean
    fn is_tt(&self, ctx: C, tm: T) -> bool {
        self.tm_satisfies(ctx, tm, Pred1::IS_TT)
    }

    /// Check whether the term `tm` is the false proposition in the context `ctx`
    ///
    /// TODO: reference Lean
    fn is_ff(&self, ctx: C, tm: T) -> bool {
        self.tm_satisfies(ctx, tm, Pred1::IS_FF)
    }

    /// Check whether the term `tm` is a typing universe in the context `ctx`
    ///
    /// TODO: reference Lean
    fn is_univ(&self, ctx: C, tm: T) -> bool {
        self.tm_satisfies(ctx, tm, Pred1::IS_UNIV)
    }
}

/// A datastore that can read quantified facts about terms-in-context.
///
/// This trait is `dyn`-safe:
/// ```rust
/// # use covalence::kernel::*;
/// let ker : &dyn ReadQuantFacts<CtxId, TermId> = &TermDb::new();
/// ```
/// Note that this trait is _not_ implemented by the kernel, to avoid re-compiling read-only
/// functions for different kernel wrappers:
/// ```rust,compile_fail
/// # use covalence::kernel::*;
/// let ker : &dyn ReadQuantFacts<CtxId, TermId> = &Kernel::new();
/// ```
pub trait ReadQuantFacts<C, T>: ReadTermFacts<C, T> {
    /// Check whether the term `tm` satisfies predicate `pred` under a binder in `ctx`
    ///
    /// For details about the specific predicates, see helper methods like
    /// [`forall_is_ty`](#method.forall_is_ty).
    fn forall_satisfies(&self, ctx: C, binder: T, tm: T, pred: Pred1) -> bool
    where
        C: Copy,
    {
        match pred.to_valid().deduce() {
            Pred1::IS_WF => self.forall_is_wf(ctx, binder, tm),
            Pred1::IS_TY => self.forall_is_ty(ctx, binder, tm),
            Pred1::IS_PROP => self.forall_is_prop(ctx, binder, tm),
            Pred1::IS_INHAB => self.forall_is_inhab(ctx, binder, tm),
            Pred1::IS_EMPTY => self.forall_is_empty(ctx, binder, tm),
            Pred1::IS_TT => self.forall_is_tt(ctx, binder, tm),
            Pred1::IS_FF => self.forall_is_ff(ctx, binder, tm),
            Pred1::IS_CONTR => self.forall_is_contr(ctx, binder, tm),
            pred => self.is_ty(ctx, binder) && self.tm_satisfies(ctx, tm, pred),
        }
    }

    /// Check whether the terms `lhs`, `rhs` are equal in `ctx` under a binder `binder`
    ///
    /// TODO: reference Lean
    fn forall_eq_in(&self, ctx: C, binder: T, lhs: T, rhs: T) -> bool;

    /// Check whether the term `tm` has type `ty` in `ctx` under a binder `binder`
    ///
    /// Corresponds to `Ctx.KHasTyUnder` in `gt3-lean`
    fn forall_has_ty(&self, ctx: C, binder: T, tm: T, ty: T) -> bool;

    /// Check whether the term `tm` is well-formed in `ctx` under a binder `binder`
    ///
    /// TODO: reference Lean
    fn forall_is_wf(&self, ctx: C, binder: T, tm: T) -> bool;

    /// Check whether the term `tm` is a valid type in `ctx` under a binder `binder`
    ///
    /// Corresponds to `Ctx.KIsTyUnder` in `gt3-lean`
    fn forall_is_ty(&self, ctx: C, binder: T, tm: T) -> bool;

    /// Check whether the term `tm` is a valid type in `ctx` under a binder `binder`
    ///
    /// Corresponds to `Ctx.KIsTyUnder` in `gt3-lean`
    fn forall_is_prop(&self, ctx: C, binder: T, tm: T) -> bool;

    /// Check whether the term `tm` is always inhabited in `ctx` under a binder `binder`
    ///
    /// TODO: reference Lean
    fn forall_is_inhab(&self, ctx: C, binder: T, tm: T) -> bool;

    /// Check whether the term `tm` is always true in `ctx` under a binder `binder`
    ///
    /// TODO: reference Lean
    fn forall_is_tt(&self, ctx: C, binder: T, tm: T) -> bool;

    /// Check whether the term `tm` is always inhabited in `ctx` under a binder `binder`
    ///
    /// TODO: reference Lean
    fn forall_is_empty(&self, ctx: C, binder: T, tm: T) -> bool;

    /// Check whether the term `tm` is always inhabited in `ctx` under a binder `binder`
    ///
    /// TODO: reference Lean
    fn forall_is_ff(&self, ctx: C, binder: T, tm: T) -> bool;

    /// Check whether the term `tm` is always contradictory in `ctx` under a binder `binder`
    ///
    /// TODO: reference Lean
    fn forall_is_contr(&self, ctx: C, binder: T, tm: T) -> bool;
}

/// A database of terms, contexts, and facts which we can read from
///
/// This trait is `dyn`-safe:
/// ```rust
/// # use covalence::kernel::*;
/// let ker : &dyn ReadFacts<CtxId, TermId> = &TermDb::new();
/// ```
/// Note that this trait is _not_ implemented by the kernel, to avoid re-compiling read-only
/// functions for different kernel wrappers:
/// ```rust,compile_fail
/// # use covalence::kernel::*;
/// let ker : &dyn ReadFacts<CtxId, TermId> = &Kernel::new();
/// ```
pub trait ReadFacts<C, T>: ReadCtxFacts<C> + ReadQuantFacts<C, T> {}

impl<D: ReadCtxFacts<C> + ReadQuantFacts<C, T>, C, T> ReadFacts<C, T> for D {}

/// A database of terms, contexts, and facts which we can read from
///
/// This trait is `dyn`-safe:
/// ```rust
/// # use covalence::kernel::*;
/// let ker : &dyn ReadTermStore<CtxId, TermId> = &TermDb::new();
/// ```
/// Note that this trait is _not_ implemented by the kernel, to avoid re-compiling read-only
/// functions for different kernel wrappers:
/// ```rust,compile_fail
/// # use covalence::kernel::*;
/// let ker : &dyn ReadTermStore<CtxId, TermId> = &Kernel::new();
/// ```
pub trait ReadTermStore<C, T>:
    ReadCtx<C, T> + ReadCtxRel<C> + ReadTermIndex<CtxId = C, TermId = T> + ReadFacts<C, T>
{
}

impl<C, T, D> ReadTermStore<C, T> for D
where
    C: Copy,
    T: Copy,
    D: ReadCtx<C, T> + ReadCtxRel<C> + ReadTermIndex<CtxId = C, TermId = T> + ReadFacts<C, T>,
{
}

/// A term database which we can read from
pub trait ReadTermDb<C, T> {
    type Reader: ReadTermStore<C, T>;

    /// Get a read-only cursor into this term database
    fn read(&self) -> &Self::Reader;
}

/// A term database which we can read from and write to
pub trait RwTermDb<C, T>: ReadTermDb<C, T> + WriteTermIndex<CtxId = C, TermId = T> {}

impl<C, T, D: ReadTermDb<C, T> + WriteTermIndex<CtxId = C, TermId = T> + ?Sized> RwTermDb<C, T>
    for D
{
}

/// A trait implemented by a mutable datastore that can hold _unchecked_ facts about terms in a
/// context.
///
/// This trait is `dyn`-safe:
/// ```rust
/// # use covalence::kernel::*;
/// let db : &dyn WriteFacts<CtxId, TermId> = &TermDb::default();
/// ```
/// We note that it is _not_ implemented by `Kernel`, since that would be unsafe:
/// ```rust,compile_fail
/// # use covalence::kernel::*;
/// let db : &dyn WriteFacts<CtxId, TermId> = &Kernel::new();
/// ```
pub trait WriteFacts<C, T> {
    // == Context predicates ==

    /// Mark a context as contradictory
    fn set_is_contr_unchecked(&mut self, ctx: C);

    /// Set a context's parent
    fn set_parent_unchecked(&mut self, ctx: C, parent: C);

    // == Typing judgements ==

    /// Set a term's flags
    fn set_tm_flags_unchecked(&mut self, ctx: C, tm: T, pred: Pred1);

    /// Set two terms as equal in a given context
    fn set_eq_unchecked(&mut self, ctx: C, lhs: T, rhs: T);

    /// Set the type of a term
    fn set_has_ty_unchecked(&mut self, ctx: C, tm: T, ty: T);

    /// Mark a term as well-formed
    fn set_is_wf_unchecked(&mut self, ctx: C, tm: T) {
        self.set_tm_flags_unchecked(ctx, tm, Pred1::IS_WF);
    }

    /// Mark a term as a type
    fn set_is_ty_unchecked(&mut self, ctx: C, tm: T) {
        self.set_tm_flags_unchecked(ctx, tm, Pred1::IS_TY);
    }

    /// Mark a term as a proposition
    fn set_is_prop_unchecked(&mut self, ctx: C, tm: T) {
        self.set_tm_flags_unchecked(ctx, tm, Pred1::IS_PROP);
    }

    /// Mark a term as an inhabited type
    fn set_is_inhab_unchecked(&mut self, ctx: C, tm: T) {
        self.set_tm_flags_unchecked(ctx, tm, Pred1::IS_INHAB);
    }

    /// Mark a term as an empty type
    fn set_is_empty_unchecked(&mut self, ctx: C, tm: T) {
        self.set_tm_flags_unchecked(ctx, tm, Pred1::IS_EMPTY);
    }

    /// Mark a term as the true proposition
    fn set_is_tt_unchecked(&mut self, ctx: C, tm: T) {
        self.set_tm_flags_unchecked(ctx, tm, Pred1::IS_TT);
    }

    /// Mark a term as the false proposition
    fn set_is_ff_unchecked(&mut self, ctx: C, tm: T) {
        self.set_tm_flags_unchecked(ctx, tm, Pred1::IS_FF);
    }

    /// Mark two terms as equal under a binder
    fn set_forall_eq_unchecked(&mut self, ctx: C, binder: T, lhs: T, rhs: T);

    /// Mark a term as well-formed under a binder
    fn set_forall_is_wf_unchecked(&mut self, ctx: C, binder: T, tm: T);

    /// Mark a term as a valid type under a binder
    fn set_forall_is_ty_unchecked(&mut self, ctx: C, binder: T, tm: T);

    /// Mark a term as a proposition under a binder
    fn set_forall_is_prop_unchecked(&mut self, ctx: C, binder: T, tm: T);

    /// Set the type of a term under a binder
    fn set_forall_has_ty_unchecked(&mut self, ctx: C, binder: T, tm: T, ty: T);

    /// Mark a term as an inhabited type under a binder
    fn set_forall_is_inhab_unchecked(&mut self, ctx: C, binder: T, tm: T);

    /// Mark a term as an empty type under a binder
    fn set_forall_is_empty_unchecked(&mut self, ctx: C, binder: T, tm: T);

    /// Mark a term as an inhabited type under a binder
    fn set_exists_is_inhab_unchecked(&mut self, ctx: C, binder: T, tm: T);

    // == Variable and assumption manipulation ==

    /// Add a variable to the given context
    fn add_var_unchecked(&mut self, ctx: C, ty: Val<C, T>) -> Fv<C>;

    // == Cached information ==

    /// Set the bound-variable index of a term
    fn set_bvi_unchecked(&mut self, ctx: C, tm: T, bvi: Bv);
}

impl<C: Copy, T: Copy, D: ReadTermIndex<CtxId = C, TermId = T> + ReadTermFacts<C, T> + ?Sized>
    ReadTermFacts<C, Val<C, T>> for D
{
    fn tm_flags(&self, ctx: C, tm: Val<C, T>) -> Pred1 {
        if let Some(tm) = self.lookup_import(ctx, tm) {
            self.tm_flags(ctx, tm)
        } else {
            Pred1::empty()
        }
    }

    fn tm_satisfies(&self, ctx: C, tm: Val<C, T>, pred: Pred1) -> bool {
        self.lookup_import(ctx, tm)
            .is_some_and(|tm| self.tm_satisfies(ctx, tm, pred))
    }

    fn eq_in(&self, ctx: C, lhs: Val<C, T>, rhs: Val<C, T>) -> bool {
        self.cons_eq(lhs, rhs)
            || if let Some(lhs) = self.lookup_import(ctx, lhs)
                && let Some(rhs) = self.lookup_import(ctx, rhs)
            {
                self.eq_in(ctx, lhs, rhs)
            } else {
                false
            }
    }

    fn has_ty(&self, ctx: C, tm: Val<C, T>, ty: Val<C, T>) -> bool {
        self.lookup_import(ctx, tm).is_some_and(|tm| {
            self.lookup_import(ctx, ty)
                .is_some_and(|ty| self.has_ty(ctx, tm, ty))
        })
    }
}

impl<C: Copy, T: Copy, D: ReadTermIndex<CtxId = C, TermId = T> + ReadQuantFacts<C, T> + ?Sized>
    ReadQuantFacts<C, Val<C, T>> for D
{
    fn forall_eq_in(&self, ctx: C, binder: Val<C, T>, lhs: Val<C, T>, rhs: Val<C, T>) -> bool {
        self.lookup_import(ctx, binder).is_some_and(|binder| {
            self.is_ty(ctx, binder) && self.cons_eq(lhs, rhs)
                || self.lookup_import(ctx, lhs).is_some_and(|lhs| {
                    self.lookup_import(ctx, rhs)
                        .is_some_and(|rhs| self.forall_eq_in(ctx, binder, lhs, rhs))
                })
        })
    }

    fn forall_is_wf(&self, ctx: C, binder: Val<C, T>, ty: Val<C, T>) -> bool {
        self.lookup_import(ctx, binder).is_some_and(|binder| {
            self.lookup_import(ctx, ty)
                .is_some_and(|ty| self.forall_is_wf(ctx, binder, ty))
        })
    }

    fn forall_is_ty(&self, ctx: C, binder: Val<C, T>, ty: Val<C, T>) -> bool {
        self.lookup_import(ctx, binder).is_some_and(|binder| {
            self.lookup_import(ctx, ty)
                .is_some_and(|ty| self.forall_is_ty(ctx, binder, ty))
        })
    }

    fn forall_is_prop(&self, ctx: C, binder: Val<C, T>, ty: Val<C, T>) -> bool {
        self.lookup_import(ctx, binder).is_some_and(|binder| {
            self.lookup_import(ctx, ty)
                .is_some_and(|ty| self.forall_is_prop(ctx, binder, ty))
        })
    }

    fn forall_has_ty(&self, ctx: C, binder: Val<C, T>, tm: Val<C, T>, ty: Val<C, T>) -> bool {
        self.lookup_import(ctx, binder).is_some_and(|binder| {
            self.lookup_import(ctx, tm).is_some_and(|tm| {
                self.lookup_import(ctx, ty)
                    .is_some_and(|ty| self.forall_has_ty(ctx, binder, tm, ty))
            })
        })
    }

    fn forall_is_inhab(&self, ctx: C, binder: Val<C, T>, tm: Val<C, T>) -> bool {
        self.lookup_import(ctx, binder).is_some_and(|binder| {
            self.lookup_import(ctx, tm)
                .is_some_and(|tm| self.forall_is_inhab(ctx, binder, tm))
        })
    }

    fn forall_is_empty(&self, ctx: C, binder: Val<C, T>, tm: Val<C, T>) -> bool {
        self.lookup_import(ctx, binder).is_some_and(|binder| {
            self.lookup_import(ctx, tm)
                .is_some_and(|tm| self.forall_is_empty(ctx, binder, tm))
        })
    }

    fn forall_is_tt(&self, ctx: C, binder: Val<C, T>, tm: Val<C, T>) -> bool {
        self.lookup_import(ctx, binder).is_some_and(|binder| {
            self.lookup_import(ctx, tm)
                .is_some_and(|tm| self.forall_is_tt(ctx, binder, tm))
        })
    }

    fn forall_is_ff(&self, ctx: C, binder: Val<C, T>, tm: Val<C, T>) -> bool {
        self.lookup_import(ctx, binder).is_some_and(|binder| {
            self.lookup_import(ctx, tm)
                .is_some_and(|tm| self.forall_is_ff(ctx, binder, tm))
        })
    }

    fn forall_is_contr(&self, ctx: C, binder: Val<C, T>, tm: Val<C, T>) -> bool {
        self.lookup_import(ctx, binder).is_some_and(|binder| {
            self.lookup_import(ctx, tm)
                .is_some_and(|tm| self.forall_is_contr(ctx, binder, tm))
        })
    }
}
