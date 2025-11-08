use std::fmt::{self, Display};

use crate::data::term::Fv;
use thiserror::Error;

/// A datastore that can read contexts
///
/// This trait is `dyn`-safe:
/// ```rust
/// # use covalence::kernel::*;
/// let ker : &dyn ReadCtx<CtxId, VarId = TmId> = &TermDb::new();
/// ```
pub trait ReadCtx<C> {
    type VarId;

    /// Get the number of variables this context has
    fn num_vars(&self, ctx: C) -> u32;

    /// Lookup the type of a variable
    fn var_ty(&self, var: Fv<C>) -> Self::VarId;
}

/// A datastore that can read relationships between contexts
///
/// This trait is `dyn`-safe:
/// ```rust
/// # use covalence::kernel::*;
/// let ker : &dyn ReadCtxGraph<CtxId> = &TermDb::new();
/// ```
pub trait ReadCtxGraph<C> {
    /// Get whether a context is a root context
    ///
    /// Note that a root context has no assumptions _or_ variables.
    ///
    /// TODO: reference Lean
    fn is_root(&self, ctx: C) -> bool;

    /// Get the number of parents this context has
    fn num_parents(&self, ctx: C) -> u32;

    /// Get the `n`th parent of this context, if any
    fn parent(&self, ctx: C, n: u32) -> Option<C>;

    /// Get whether `parent` is a parent of `child`
    fn is_parent(&self, parent: C, child: C) -> bool;

    /// Check whether `lo` is an ancestor of `hi`
    ///
    /// Note that a context `ctx` is always an ancestor of itself
    ///
    /// # Examples
    /// ```text
    /// BROKEN!
    /// # use covalence::kernel::*;
    /// # let mut ker = Kernel::default();
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
    /// ```text
    /// BROKEN!
    /// # use covalence::kernel::*;
    /// # let mut ker = Kernel::default();
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
    /// ```text
    /// BROKEN!
    /// # use covalence::kernel::*;
    /// # let mut ker = Kernel::default();
    /// let parent = ker.new_ctx();
    /// let child = ker.with_parent(parent);
    /// let grandchild = ker.with_parent(child);
    /// for x in [parent, child, grandchild] {
    ///     for y in [parent, child, grandchild] {
    ///         assert!(ker.is_subctx(x, y));
    ///     }
    /// }
    /// let n = ker.nats(child);
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
    /// ```text
    /// BROKEN!
    /// # use covalence::kernel::*;
    /// # let mut ker = Kernel::new();
    /// let ctx = ker.new_ctx();
    /// // The empty context is a subctx of everything
    /// assert!(ker.is_subctx_of_parents(ctx, ctx));
    /// let unit = ker.tt(ctx);
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
    /// ```text
    /// BROKEN!
    /// # use covalence::kernel::*;
    /// # let mut ker = Kernel::new();
    /// let ctx = ker.new_ctx();
    /// // The empty context is a subctx of everything
    /// assert!(ker.parents_are_subctx(ctx, ctx));
    /// let unit = ker.tt(ctx);
    /// let x = ker.with_param(ctx, unit, &mut ()).unwrap();
    /// let child = x.ctx;
    /// assert!(ker.parents_are_subctx(ctx, child));
    /// assert!(ker.parents_are_subctx(child, ctx));
    /// assert!(ker.parents_are_subctx(child, child));
    /// let y = ker.with_param(child, unit, &mut ()).unwrap();
    /// let grandchild = y.ctx;
    /// assert!(ker.parents_are_subctx(ctx, grandchild));
    /// assert!(ker.parents_are_subctx(grandchild, child));
    /// // child is a parent of grandchild, but not of ctx!
    /// assert!(!ker.parents_are_subctx(grandchild, ctx));
    /// ```
    fn parents_are_subctx(&self, lo: C, hi: C) -> bool;
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Error)]
pub struct AddParentFailure;

impl Display for AddParentFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "failed to add parent to context")
    }
}

/// A datastore that can add parents to contexts _without checking validity_
///
/// This trait is `dyn`-safe:
/// ```rust
/// # use covalence::kernel::*;
/// let ker : &dyn AddParentUnchecked<CtxId> = &TermDb::new();
/// ```
pub trait AddParentUnchecked<C> {
    /// Add a parent to this context
    fn add_parent_unchecked(&mut self, ctx: C, parent: C) -> Result<(), AddParentFailure>;
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Error)]
pub struct AddVarFailure;

impl Display for AddVarFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "failed to add variable to context")
    }
}

/// A datastore which can add variables to contexts _without checking validity_
///
/// This trait is `dyn`-safe:
/// ```rust
/// # use covalence::kernel::*;
/// let db : &dyn AddVarUnchecked<CtxId, TmId> = &TermDb::default();
/// ```
pub trait AddVarUnchecked<C, T> {
    /// Add a variable to the given context
    fn add_var_unchecked(&mut self, ctx: C, ty: T) -> Result<Fv<C>, AddVarFailure>;
}
