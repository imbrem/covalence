use crate::data::term::{Bv, Fv, NodeT, ULvl, Val};

/// A trait implemented by a datastore that can read hash-consed terms and universe levels
///
/// This trait is `dyn`-safe:
/// ```rust
/// # use covalence_kernel::*;
/// let ker : &dyn ReadTerm<CtxId, TermId> = &Kernel::new();
/// ```
pub trait ReadTerm<C, T> {
    // == Terms ==

    /// Get the node corresponding to a term
    fn node(&self, ctx: C, tm: T) -> &NodeT<C, T>;

    /// Lookup a term in the store
    ///
    /// Canonicalizes the term's children if found
    fn lookup(&self, ctx: C, tm: &mut NodeT<C, T>) -> Option<T>;

    /// Lookup an import of a term into another context, returning a handle to it if it exists
    fn lookup_import(&self, ctx: C, val: Val<C, T>) -> Option<T>;

    // == Variables ==

    /// Get the number of variables this context has
    fn num_vars(&self, ctx: C) -> u32;

    /// Lookup the type of a variable in its own context
    fn get_var_ty(&self, var: Fv<C>) -> T;

    /// Get whether a variable is a ghost variable
    ///
    /// Ghost variables cannot appear in terms, and so in general are ill-typed, but their type is
    /// inhabited.
    fn var_is_ghost(&self, var: Fv<C>) -> bool;
}

/// A trait implemented by a datastore that can manipulate hash-consed terms and universe levels
///
/// This trait is `dyn`-safe:
/// ```rust
/// # use covalence_kernel::*;
/// let ker : &dyn TermStore<CtxId, TermId> = &Kernel::new();
/// ```
pub trait TermStore<C, T> : ReadTerm<C, T> {
    // == Term management ==

    /// Create a new context in this store
    ///
    /// # Example
    /// ```rust
    /// # use covalence_kernel::*;
    /// # use covalence_kernel::api::error::kernel_error;
    /// # let mut ker = Kernel::new();
    /// let ctx = ker.new_ctx();
    /// assert_eq!(ker.num_vars(ctx), 0);
    /// ```
    fn new_ctx(&mut self) -> C;

    /// Create a new context in this store with the given parent
    ///
    /// # Example
    /// ```rust
    /// # use covalence_kernel::*;
    /// # use covalence_kernel::api::error::kernel_error;
    /// # let mut ker = Kernel::new();
    /// let parent = ker.new_ctx();
    /// let child = ker.with_parent(parent);
    /// // This is true since both contexts are currently empty
    /// assert!(ker.is_subctx(parent, child));
    /// assert!(ker.is_subctx(child, parent));
    /// let s = ker.add(child, Node::U(ULvl::SET));
    /// let x = ker.add_var(child, s, &mut ()).unwrap();
    /// ```
    fn with_parent(&mut self, parent: C) -> C;

    /// Insert a term into the store, returning a handle to it
    fn add(&mut self, ctx: C, tm: NodeT<C, T>) -> T;

    /// Import a term into another context, returning a handle to it
    ///
    /// This automatically traverses import chains, e.g.
    /// - If `src[tm] := import(src2, tm)`, then `import(ctx, src, tm) => import(ctx, src2, tm)`
    /// - _Otherwise_, `import(ctx, ctx, tm)` returns `tm`
    fn import(&mut self, ctx: C, val: Val<C, T>) -> T;

    // == Variable management ==

    /// Get the type of a variable in the given context
    ///
    /// Imports if necessary
    fn var_ty(&mut self, ctx: C, var: Fv<C>) -> T;

    // == Universe management ==

    /// Get the successor of a given universe level
    fn succ(&mut self, level: ULvl) -> ULvl;

    /// Get the maximum of two universe levels
    fn umax(&mut self, lhs: ULvl, rhs: ULvl) -> ULvl;

    /// Get the impredicatibe maximum of two universe levels
    fn imax(&mut self, lhs: ULvl, rhs: ULvl) -> ULvl;

    // == Congruence management ==

    /// Propagate congruence information _within_ a context
    fn propagate_in(&mut self, ctx: C) -> usize;
}

/// A type of quantifier for a fact
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub enum QuantK {
    /// An existential quantifier
    Exists,
    /// A universal quantifier
    Forall,
}

/// A quantifier for a fact
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub enum Quant<T> {
    /// An existential quantifier
    Exists(T),
    /// A universal quantifier
    Forall(T),
}

impl<T> Quant<T> {
    pub fn binder(self) -> T {
        match self {
            Quant::Exists(binder) | Quant::Forall(binder) => binder,
        }
    }
}

/// A trait implemented by a datastore that can read facts about terms in a context.
///
/// This trait is `dyn`-safe:
/// ```rust
/// # use covalence_kernel::*;
/// let ker : &dyn ReadFacts<CtxId, TermId> = &Kernel::new();
/// ```
pub trait ReadFacts<C, T> {
    // == Context information ==
    /// Get whether a context is a root context
    ///
    /// Note that a root context has no assumptions _or_ variables.
    ///
    /// TODO: reference Lean
    fn is_root(&self, ctx: C) -> bool;

    /// Get whether a context is contradictory
    ///
    /// TODO: reference lean
    fn is_contr(&self, ctx: C) -> bool;

    // == Syntax information ==
    /// Get an upper bound on the de-Bruijn indices visible in `tm`
    ///
    /// TODO: reference lean
    fn bvi(&self, ctx: C, tm: T) -> Bv;

    // == Context information ==

    /// Check whether `lo` is an ancestor of `hi`
    ///
    /// Note that a context `ctx` is always an ancestor of itself
    ///
    /// # Examples
    /// ```rust
    /// # use covalence_kernel::*;
    /// # let mut ker = Kernel::new();
    /// let parent = ker.new_ctx();
    /// let child = ker.with_parent(parent);
    /// assert!(ker.is_ancestor(parent, child));
    /// assert!(ker.is_ancestor(parent, parent));
    /// assert!(ker.is_ancestor(child, child));
    /// assert!(!ker.is_ancestor(child, parent));
    /// ```
    fn is_ancestor(&self, lo: C, hi: C) -> bool;

    /// Check whether `lo` is _strict_ ancestor of `hi`
    ///
    /// A context `ctx` is never a strict ancestor of itself
    ///
    /// # Examples
    /// ```rust
    /// # use covalence_kernel::*;
    /// # let mut ker = Kernel::new();
    /// let parent = ker.new_ctx();
    /// let child = ker.with_parent(parent);
    /// assert!(ker.is_strict_ancestor(parent, child));
    /// assert!(!ker.is_strict_ancestor(parent, parent));
    /// assert!(!ker.is_strict_ancestor(child, child));
    /// assert!(!ker.is_strict_ancestor(child, parent));
    /// ```
    fn is_strict_ancestor(&self, lo: C, hi: C) -> bool;

    /// Check whether `lo` is a subcontext of `hi`
    ///
    /// This means that every variable in `lo` is contained in `hi`.
    ///
    /// Unlike [`is_ancestor`](#method.is_ancestor), this is _not_ monotonic: a context may be
    /// modified so that it is not longer a subcontext of another, whereas if `lo` is an ancestor of
    /// `hi`, all valid edits to a kernel will preserve this fact.
    ///
    /// # Examples
    /// ```rust
    /// # use covalence_kernel::*;
    /// # let mut ker = Kernel::new();
    /// let parent = ker.new_ctx();
    /// let child = ker.with_parent(parent);
    /// let grandchild = ker.with_parent(child);
    /// for x in [parent, child, grandchild] {
    ///     for y in [parent, child, grandchild] {
    ///         assert!(ker.is_subctx(x, y));
    ///     }
    /// }
    /// let n = ker.add(child, Node::Nats);
    /// let x = ker.add_var(child, n, &mut ()).unwrap();
    /// // ∅ is a subset of everything
    /// assert!(ker.is_subctx(parent, child));
    /// // {x} is not a subset of ∅
    /// assert!(!ker.is_subctx(child, parent));
    /// // These both contain exactly x
    /// assert!(ker.is_subctx(child, grandchild));
    /// assert!(ker.is_subctx(grandchild, child));
    /// ```
    fn is_subctx(&self, lo: C, hi: C) -> bool;

    /// Check whether `lo` is a subcontext of `hi`'s parent(s)
    ///
    /// # Examples
    /// ```rust
    /// # use covalence_kernel::*;
    /// # use covalence_kernel::api::error::kernel_error;
    /// # let mut ker = Kernel::new();
    /// let ctx = ker.new_ctx();
    /// // The empty context is a subctx of everything
    /// assert!(ker.is_subctx_of_parents(ctx, ctx));
    /// let unit = ker.add(ctx, Node::Unit);
    /// let x = ker.with_param(ctx, unit, &mut ()).unwrap();
    /// let child = x.ctx;
    /// assert!(ker.is_subctx_of_parents(ctx, child));
    /// assert!(!ker.is_subctx_of_parents(child, ctx));
    /// // Child is nonempty, so is not a subctx of its parent (ctx)
    /// assert!(!ker.is_subctx_of_parents(child, child));
    /// ```
    fn is_subctx_of_parents(&self, lo: C, hi: C) -> bool;

    /// Check whether `lo`'s parent(s) are a subcontext of `hi`
    ///
    /// # Examples
    /// ```rust
    /// # use covalence_kernel::*;
    /// # use covalence_kernel::api::error::kernel_error;
    /// # let mut ker = Kernel::new();
    /// let ctx = ker.new_ctx();
    /// // The empty context is a subctx of everything
    /// assert!(ker.parents_are_subctx(ctx, ctx));
    /// let unit = ker.add(ctx, Node::Unit);
    /// let x = ker.with_param(ctx, unit, &mut ()).unwrap();
    /// let child = x.ctx;
    /// assert!(ker.parents_are_subctx(ctx, child));
    /// assert!(ker.parents_are_subctx(child, ctx));
    /// assert!(ker.parents_are_subctx(child, child));
    /// let unit_ = ker.add(child, Node::Unit);
    /// let y = ker.with_param(child, unit_, &mut ()).unwrap();
    /// let grandchild = y.ctx;
    /// assert!(ker.parents_are_subctx(ctx, grandchild));
    /// assert!(ker.parents_are_subctx(grandchild, child));
    /// // child is a parent of grandchild, but not of ctx!
    /// assert!(!ker.parents_are_subctx(grandchild, ctx));
    /// ```
    fn parents_are_subctx(&self, lo: C, hi: C) -> bool;

    // == Term predicates ==

    /// Check whether the term `tm` depends on the variable `var` in context `ctx`
    fn has_var(&self, ctx: C, tm: T, var: Fv<C>) -> bool;

    /// Check whether the term `tm` depends on any variable from the context `vars`
    fn has_var_from(&self, ctx: C, tm: T, vars: C) -> bool;

    /// Check whether the term `tm` may depend on the variable `var` in context `ctx`
    fn may_have_var(&self, ctx: C, tm: T, var: Fv<C>) -> bool;

    /// Check whether the term `tm` may depend on any variable from the context `vars`
    fn may_have_var_from(&self, ctx: C, tm: T, vars: C) -> bool;

    // == Syntacitc relations ==

    /// Check whether two values are syntactically equal
    ///
    /// `lhs` is syntactically equal to `rhs` if they are the same term, modulo imports
    fn syn_eq(&self, lhs: Val<C, T>, rhs: Val<C, T>) -> bool;

    /// Check whether two values are definitionally equal
    ///
    /// `lhs` is definitionally equal to `rhs` if they are equal after fully unfolding all `close`,
    /// `subst1`, and `wkn`. This function is a (safe) approximation: it can return `false`
    /// incorrectly.
    fn def_eq(&self, lhs: Val<C, T>, rhs: Val<C, T>) -> bool;

    // == Typing judgements ==

    /// Check whether the term `lhs` is equal to the term `rhs` in `ctx`
    ///
    /// Corresponds to `Ctx.KEq` in `gt3-lean`
    fn eq_in(&self, ctx: C, lhs: T, rhs: T) -> bool;

    /// Check whether the term `tm` is well-formed in `ctx`
    /// Corresponds to `Ctx.KIsWf` in `gt3-lean`
    fn is_wf(&self, ctx: C, tm: T) -> bool;

    /// Check whether the term `tm` is a type in the context `ctx`
    ///
    /// Corresponds to `Ctx.KIsTy` in `gt3-lean`
    fn is_ty(&self, ctx: C, tm: T) -> bool;

    /// Check whether the term `tm` is a proposition in the context `ctx`
    ///
    /// Corresponds to `Ctx.KIsProp` in `gt3-lean`
    fn is_prop(&self, ctx: C, tm: T) -> bool;

    /// Check whether the term `tm` has type `ty` in `ctx`
    ///
    /// Corresponds to `Ctx.KHasTy` in `gt3-lean`
    fn has_ty(&self, ctx: C, tm: T, ty: T) -> bool;

    /// Check whether the term `tm` is an inhabited type in the context `ctx`
    ///
    /// Corresponds to `Ctx.KIsInhab` in `gt3-lean`
    fn is_inhab(&self, ctx: C, tm: T) -> bool;

    /// Check whether the term `tm` is an empty type in the context `ctx`
    ///
    /// TODO: reference Lean
    fn is_empty(&self, ctx: C, tm: T) -> bool;

    /// Check whether the terms `lhs`, `rhs` are equal in `ctx` under a binder `binder`
    ///
    /// TODO: reference Lean
    fn forall_eq_in(&self, ctx: C, binder: T, lhs: T, rhs: T) -> bool;

    /// Check whether the term `tm` is well-formed in `ctx` under a binder `binder`
    ///
    /// TODO: reference Lean
    fn forall_is_wf(&self, ctx: C, binder: T, ty: T) -> bool;

    /// Check whether the term `tm` is a valid type in `ctx` under a binder `binder`
    ///
    /// Corresponds to `Ctx.KIsTyUnder` in `gt3-lean`
    fn forall_is_ty(&self, ctx: C, binder: T, ty: T) -> bool;

    /// Check whether the term `tm` is a valid type in `ctx` under a binder `binder`
    ///
    /// Corresponds to `Ctx.KIsTyUnder` in `gt3-lean`
    fn forall_is_prop(&self, ctx: C, binder: T, ty: T) -> bool;

    /// Check whether the term `tm` has type `ty` in `ctx` under a binder `binder`
    ///
    /// Corresponds to `Ctx.KHasTyUnder` in `gt3-lean`
    fn forall_has_ty(&self, ctx: C, binder: T, tm: T, ty: T) -> bool;

    /// Check whether the term `tm` is always inhabited in `ctx` under a binder `binder`
    ///
    /// TODO: reference Lean
    fn forall_is_inhab(&self, ctx: C, binder: T, tm: T) -> bool;

    /// Check whether the term `tm` is always inhabited in `ctx` under a binder `binder`
    ///
    /// TODO: reference Lean
    fn forall_is_empty(&self, ctx: C, binder: T, tm: T) -> bool;

    /// Check whether there exists a value of type `binder` such that `lhs`, `rhs` are equal in
    /// `ctx`
    ///
    /// TODO: reference Lean
    fn exists_eq_in(&self, ctx: C, binder: T, lhs: T, rhs: T) -> bool;

    /// Check whether there exists a value of type `binder` such that `tm` is well-formed
    ///
    /// TODO: reference Lean
    fn exists_is_wf(&self, ctx: C, binder: T, ty: T) -> bool;

    /// Check whether there exists a value of type `binder` such that `tm` is a type
    ///
    /// Corresponds to `Ctx.KIsTyUnder` in `gt3-lean`
    fn exists_is_ty(&self, ctx: C, binder: T, ty: T) -> bool;

    /// Check whether there exists a value of type `binder` such that `tm` is a proposition
    ///
    /// Corresponds to `Ctx.KIsTyUnder` in `gt3-lean`
    fn exists_is_prop(&self, ctx: C, binder: T, ty: T) -> bool;

    /// Check whether there exists a value of type `binder` such that `tm` has type `ty`
    ///
    /// Corresponds to `Ctx.KHasTyUnder` in `gt3-lean`
    fn exists_has_ty(&self, ctx: C, binder: T, tm: T, ty: T) -> bool;

    /// Check whether there exists a value of type `binder` such that the term `tm` is inhabited
    ///
    /// TODO: reference Lean
    fn exists_is_inhab(&self, ctx: C, binder: T, tm: T) -> bool;

    /// Check whether there exists a value of type `binder` such that the term `tm` is empty
    ///
    /// TODO: reference Lean
    fn exists_is_empty(&self, ctx: C, binder: T, tm: T) -> bool;

    // == Universe levels ==
    /// Check whether one universe is less than or equal to another
    fn u_le(&self, lo: ULvl, hi: ULvl) -> bool;

    /// Check whether one universe is strictly less than another
    fn u_lt(&self, lo: ULvl, hi: ULvl) -> bool;

    /// Check whether the impredicative maximum of two universes is less than or equal to another
    fn imax_le(&self, lo_lhs: ULvl, lo_rhs: ULvl, hi: ULvl) -> bool;
}

/// A trait implemented by a mutable datastore that can hold _unchecked_ facts about terms in a
/// context.
///
/// This trait is `dyn`-safe:
/// ```rust
/// # use covalence_kernel::api::store::*;
/// # use covalence_kernel::store::EggTermDb;
/// # use covalence_kernel::*;
/// let db : &dyn WriteFacts<CtxId, TermId> = &EggTermDb::default();
/// ```
/// We note that it is _not_ implemented by `Kernel`, since that would be unsafe:
/// ```rust,compile_fail
/// # use covalence_kernel::api::store::*;
/// # use covalence_kernel::*;
/// let db : &dyn WriteFacts<CtxId, TermId> = &Kernel::new();
/// ```
pub trait WriteFacts<C, T> {
    // == Context predicates ==

    /// Mark a context as contradictory
    fn set_is_contr_unchecked(&mut self, ctx: C);

    /// Set a context's parent
    fn set_parent_unchecked(&mut self, ctx: C, parent: C);

    // == Typing judgements ==

    /// Set two terms as equal in a given context
    fn set_eq_unchecked(&mut self, ctx: C, lhs: T, rhs: T);

    /// Mark a term as well-formed
    fn set_is_wf_unchecked(&mut self, ctx: C, tm: T);

    /// Mark a term as a type
    fn set_is_ty_unchecked(&mut self, ctx: C, tm: T);

    /// Mark a term as a proposition
    fn set_is_prop_unchecked(&mut self, ctx: C, tm: T);

    /// Set the type of a term
    fn set_has_ty_unchecked(&mut self, ctx: C, tm: T, ty: T);

    /// Mark a term as an inhabited type
    fn set_is_inhab_unchecked(&mut self, ctx: C, tm: T);

    /// Mark a term as an empty type
    fn set_is_empty_unchecked(&mut self, ctx: C, tm: T);

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

    /// Mark two terms as equal under a binder
    fn set_exists_eq_unchecked(&mut self, ctx: C, binder: T, lhs: T, rhs: T);

    /// Mark a term as well-formed under a binder
    fn set_exists_is_wf_unchecked(&mut self, ctx: C, binder: T, tm: T);

    /// Mark a term as a valid type under a binder
    fn set_exists_is_ty_unchecked(&mut self, ctx: C, binder: T, tm: T);

    /// Mark a term as a proposition under a binder
    fn set_exists_is_prop_unchecked(&mut self, ctx: C, binder: T, tm: T);

    /// Set the type of a term under a binder
    fn set_exists_has_ty_unchecked(&mut self, ctx: C, binder: T, tm: T, ty: T);

    /// Mark a term as an inhabited type under a binder
    fn set_exists_is_inhab_unchecked(&mut self, ctx: C, binder: T, tm: T);

    /// Mark a term as an empty type under a binder
    fn set_exists_is_empty_unchecked(&mut self, ctx: C, binder: T, tm: T);

    // == Variable and assumption manipulation ==

    /// Add an assumption to the given context
    ///
    /// This adds the assumption that `ty` is inhabited; and marks it as so.
    fn assume_unchecked(&mut self, ctx: C, ty: T) -> Fv<C>;

    /// Add a variable to the given context
    fn add_var_unchecked(&mut self, ctx: C, ty: T) -> Fv<C>;

    // == Cached information ==

    /// Set the bound-variable index of a term
    fn set_bvi_unchecked(&mut self, ctx: C, tm: T, bvi: Bv);
}
