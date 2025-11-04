use covalence_core::strategy::Strategy;
pub use covalence_core::*;

use data::term::*;

pub use covalence_core::data as data;

/// Writing for the `covalence` kernel
pub trait Write<C, T>: WriteTrusted<C, T> + WriteTermIndex<CtxId = C, TermId = T>
where
    C: Copy,
    T: Copy,
{
    /// Construct the universe of propositions in a given context
    ///
    /// # Examples
    /// ```rust
    /// # use covalence::kernel::*;
    /// # let mut ker = Kernel::new();
    /// # let ctx = ker.new_ctx();
    /// let prop = ker.prop(ctx);
    /// assert!(ker.is_ty(ctx, prop));
    /// assert!(ker.is_inhab(ctx, prop));
    /// // Note: the _type_ of propositions is _not_ itself a proposition!
    /// assert!(!ker.is_prop(ctx, prop));
    /// ```
    fn prop(&mut self, ctx: C) -> Val<C, T> {
        self.add_ix(ctx, NodeT::U(ULvl::PROP))
    }

    /// Construct the true proposition in a given context
    ///
    /// # Examples
    /// ```rust
    /// # use covalence::kernel::*;
    /// # let mut ker = Kernel::new();
    /// # let ctx = ker.new_ctx();
    /// let tt = ker.tt(ctx);
    /// assert!(ker.is_prop(ctx, tt));
    /// assert!(ker.is_tt(ctx, tt));
    /// assert!(!ker.is_ff(ctx, tt));
    /// ```
    fn tt(&mut self, ctx: C) -> Val<C, T> {
        self.add_ix(ctx, NodeT::Unit)
    }

    /// Construct the false proposition in a given context
    ///
    /// # Examples
    /// ```rust
    /// # use covalence::kernel::*;
    /// # let mut ker = Kernel::new();
    /// # let ctx = ker.new_ctx();
    /// let ff = ker.ff(ctx);
    /// assert!(ker.is_prop(ctx, ff));
    /// assert!(!ker.is_tt(ctx, ff));
    /// assert!(ker.is_ff(ctx, ff));
    /// ```
    fn ff(&mut self, ctx: C) -> Val<C, T> {
        self.add_ix(ctx, NodeT::Empty)
    }

    /// Construct the universe of sets in a given context
    ///
    /// # Examples
    /// ```rust
    /// # use covalence::kernel::*;
    /// # let mut ker = Kernel::new();
    /// # let ctx = ker.new_ctx();
    /// let sets = ker.sets(ctx);
    /// assert!(ker.is_ty(ctx, sets));
    /// assert!(ker.is_inhab(ctx, sets));
    /// ```
    fn sets(&mut self, ctx: C) -> Val<C, T> {
        self.add_ix(ctx, NodeT::U(ULvl::SET))
    }

    /// Construct the type of natural numbers in a given context
    ///
    /// # Examples
    /// ```rust
    /// # use covalence::kernel::*;
    /// # let mut ker = Kernel::new();
    /// # let ctx = ker.new_ctx();
    /// let nats = ker.nats(ctx);
    /// assert!(ker.is_ty(ctx, nats));
    /// assert!(ker.is_inhab(ctx, nats));
    /// ```
    fn nats(&mut self, ctx: C) -> Val<C, T> {
        self.add_ix(ctx, NodeT::Nats)
    }

    /// Construct a small natural number in a given context
    ///
    /// # Examples
    /// ```rust
    /// # use covalence::kernel::*;
    /// # let mut ker = Kernel::new();
    /// # let ctx = ker.new_ctx();
    /// let n = ker.n64(ctx, 50);
    /// assert!(ker.is_wf(ctx, n));
    /// assert!(!ker.is_ty(ctx, n));
    /// let m = ker.n64(ctx, 3);
    /// assert!(ker.is_wf(ctx, m));
    /// assert!(!ker.is_ty(ctx, m));
    /// assert_ne!(n, m);
    /// assert!(!ker.eq_in(ctx, n, m));
    /// ```
    fn n64(&mut self, ctx: C, n: u64) -> Val<C, T> {
        self.add_ix(ctx, NodeT::N64(n))
    }
}

/// Derivations supported by the `covalence` kernel
pub trait Derive<C, T, S>:
    WriteTrusted<C, T>
    + DeriveTrusted<C, T, S>
    + ReadTermDb<C, T>
    + WriteTermIndex<CtxId = C, TermId = T>
where
    C: Copy + PartialEq,
    T: Copy + PartialEq,
    S: Strategy<C, T, Self>,
{
    /// Insert a new context with the given parameter
    ///
    /// TODO: reference Lean
    fn with_param(
        &mut self,
        parent: C,
        param: Val<C, T>,
        strategy: &mut S,
    ) -> Result<Fv<C>, S::Fail> {
        let ctx = self.with_parent(parent);
        let var = self.add_var(ctx, param, strategy)?;
        Ok(var)
    }
}

impl<C, T, K> Write<C, T> for K
where
    C: Copy,
    T: Copy,
    K: WriteTrusted<C, T> + WriteTermIndex<CtxId = C, TermId = T>,
{
}

impl<C, T, S, K> Derive<C, T, S> for K
where
    C: Copy + PartialEq,
    T: Copy + PartialEq,
    K: WriteTrusted<C, T>
        + DeriveTrusted<C, T, S>
        + ReadTermDb<C, T>
        + WriteTermIndex<CtxId = C, TermId = T>,
    S: Strategy<C, T, K>,
{
}
