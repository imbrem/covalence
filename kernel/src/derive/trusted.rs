use smallvec::SmallVec;

use crate::term::{Bv, Close, GNode, Gv, Import, ULvl};

/// A trait implemented by a datastore that can manipulate hash-consed terms and universe levels
pub trait TermStore<C, T> {
    // == Term management ==

    /// Create a new context in this store
    fn new_ctx(&mut self) -> C;

    /// Create a new context in this store with the given parent
    fn with_parent(&mut self, parent: C) -> C;

    /// Insert a term into the store, returning a handle to it
    fn add(&mut self, ctx: C, tm: GNode<C, T>) -> T;

    /// Import a term into another context, returning a handle to it
    ///
    /// This automatically traverses import chains, e.g.
    /// - If `src[tm] := import(src2, tm)`, then `import(ctx, src, tm) => import(ctx, src2, tm)`
    /// - _Otherwise_, `import(ctx, ctx, tm)` returns `tm`
    fn import(&mut self, ctx: C, src: C, tm: T) -> T;

    /// Get the node corresponding to a term
    fn node(&self, ctx: C, tm: T) -> &GNode<C, T>;

    /// Lookup a term in the store
    ///
    /// Canonicalizes the term's children if found
    fn lookup(&self, ctx: C, tm: &mut GNode<C, T>) -> Option<T>;

    /// Lookup an import of a term into another context, returning a handle to it if it exists
    fn lookup_import(&self, ctx: C, src: C, tm: T) -> Option<T>;

    // == Variable management ==

    /// Get the number of assumptions this context has
    fn num_assumptions(&self, ctx: C) -> usize;

    /// Get the number of variables this context has
    fn num_vars(&self, ctx: C) -> usize;

    /// Get this context's `n`th assumption
    fn assumption(&self, ctx: C, ix: usize) -> Option<T>;

    /// Get the type of a variable in the given context
    ///
    /// Imports if necessary
    fn var_ty(&mut self, ctx: C, var: Gv<C>) -> T;

    /// Lookup the type of a variable in its own context
    fn get_var_ty(&self, var: Gv<C>) -> T;

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

/// A trait implemented by a datastore that can read facts about terms in a context.
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

    /// Get a context's parent, if any
    fn parent(&self, ctx: C) -> Option<C>;

    // == Syntax information ==
    /// Get an upper bound on the de-Bruijn indices visible in `tm`
    ///
    /// TODO: reference lean
    fn bvi(&self, ctx: C, tm: T) -> Bv;

    // == Context information ==

    /// Check whether `lo` is a subcontext of `hi`
    ///
    /// This always returns `true` if `lo` is a root context, even if `hi` has no parent
    ///
    /// If `lo` is _not_ a root context, this in fact guarantees that `lo` is a _stable_ subcontext
    /// of `hi`: adding variables to `lo` will automatically make those variables valid to use in
    /// `hi`.
    fn is_subctx(&self, lo: C, hi: C) -> bool;

    /// Check whether `lo` is a subcontext of `hi`'s parent
    ///
    /// This always returns `true` if `lo` is a root context, even if `hi` has no parent
    ///
    /// If `lo` is _not_ a root context, this in fact guarantees that `lo` is a _stable_ subcontext
    /// of `hi`: adding variables to `lo` will automatically make those variables valid to use in
    /// `hi`.
    fn is_subctx_of_parent(&self, lo: C, hi: C) -> bool;

    // == Predicates ==
    /// Check whether the term `tm` is well-formed in `ctx`
    /// Corresponds to `Ctx.KIsWf` in `gt3-lean`
    fn is_wf(&self, ctx: C, tm: T) -> bool;

    /// Check whether the term `tm` is a type in the context `ctx`
    ///
    /// Corresponds to `Ctx.KIsTy` in `gt3-lean`
    fn is_ty(&self, ctx: C, tm: T) -> bool;

    /// Check whether the term `tm` is an inhabited type in the context `ctx`
    ///
    /// Corresponds to `Ctx.KIsInhab` in `gt3-lean`
    fn is_inhab(&self, ctx: C, tm: T) -> bool;

    /// Check whether the term `tm` is an empty type in the context `ctx`
    ///
    /// TODO: reference lean
    fn is_empty(&self, ctx: C, tm: T) -> bool;

    /// Check whether the term `tm` is a proposition in the context `ctx`
    ///
    /// Corresponds to `Ctx.KIsProp` in `gt3-lean`
    fn is_prop(&self, ctx: C, tm: T) -> bool;

    /// Check whether the term `tm` depends on the variable `var` in context `ctx`
    fn has_var(&self, ctx: C, tm: T, var: Gv<C>) -> bool;

    // == Relations ==
    /// Check whether the term `lhs` in `lctx` is _syntactically_ equal to the term `rhs` in `rctx`
    fn syn_eq(&self, lctx: C, lhs: T, rctx: C, rhs: T) -> bool;

    /// Check whether the term `lhs` is equal to the term `rhs` in `ctx`
    ///
    /// Corresponds to `Ctx.KEq` in `gt3-lean`
    fn eq_in(&self, ctx: C, lhs: T, rhs: T) -> bool;

    /// Check whether the term `tm` has type `ty` in `ctx`
    ///
    /// Corresponds to `Ctx.KHasTy` in `gt3-lean`
    fn has_ty(&self, ctx: C, tm: T, ty: T) -> bool;

    /// Check whether the term `tm` is a valid type in `ctx` under a binder `binder`
    ///
    /// Corresponds to `Ctx.KIsTyUnder` in `gt3-lean`
    fn is_ty_under(&self, ctx: C, binder: T, ty: T) -> bool;

    /// Check whether the term `tm` has type `ty` in `ctx` under a binder `binder`
    ///
    /// Corresponds to `Ctx.KHasTyUnder` in `gt3-lean`
    fn has_ty_under(&self, ctx: C, binder: T, tm: T, ty: T) -> bool;

    /// Check whether the term `tm` is always inhabited in `ctx` under a binder `binder`
    ///
    /// TODO: reference Lean
    fn forall_inhab_under(&self, ctx: C, binder: T, ty: T) -> bool;

    /// Check whether there exists a value of type `binder` such that the term `tm` is inhabited
    ///
    /// TODO: reference Lean
    fn exists_inhab_under(&self, ctx: C, binder: T, ty: T) -> bool;

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
pub trait WriteFacts<C, T> {
    // == Context predicates ==

    /// Mark a context as contradictory
    fn set_is_contr(&mut self, ctx: C);

    // == Predicates ==

    /// Mark a term as well-formed
    fn set_is_wf_unchecked(&mut self, ctx: C, tm: T);

    /// Mark a term as a type
    fn set_is_ty_unchecked(&mut self, ctx: C, tm: T);

    /// Mark a term as an inhabited type
    fn set_is_inhab_unchecked(&mut self, ctx: C, tm: T);

    /// Mark a term as an empty type
    fn set_is_empty_unchecked(&mut self, ctx: C, tm: T);

    /// Mark a term as a proposition
    fn set_is_prop_unchecked(&mut self, ctx: C, tm: T);

    // == Relations ==

    /// Set two terms as equal in a given context
    fn set_eq_unchecked(&mut self, ctx: C, lhs: T, rhs: T);

    /// Set the type of a term
    fn set_has_ty_unchecked(&mut self, ctx: C, tm: T, ty: T);

    /// Mark a term as a valid type under a binder
    fn set_is_ty_under_unchecked(&mut self, ctx: C, binder: T, tm: T);

    /// Check whether the term `tm` is always inhabited in `ctx` under a binder `binder`
    ///
    /// TODO: reference Lean
    fn set_forall_inhab_under_unchecked(&mut self, ctx: C, binder: T, ty: T) -> bool;

    /// Check whether there exists a value of type `binder` such that the term `tm` is inhabited
    ///
    /// TODO: reference Lean
    fn set_exists_inhab_under_unchecked(&mut self, ctx: C, binder: T, ty: T) -> bool;

    /// Set the type of a term under a binder
    fn set_has_ty_under_unchecked(&mut self, ctx: C, binder: T, tm: T, ty: T);

    // == Variable and assumption manipulation ==

    /// Add an assumption to the given context
    ///
    /// This adds the assumption that `ty` is inhabited; and marks it as so.
    ///
    /// For this to be valid, `ty` should be a valid type _in the parent context_!
    fn assume_unchecked(&mut self, ctx: C, ty: T);

    /// Add a variable to the given context
    fn add_var_unchecked(&mut self, ctx: C, ty: T) -> Gv<C>;

    // == Cached information ==

    /// Set the bound-variable index of a term
    fn set_bvi_unchecked(&mut self, ctx: C, tm: T, bvi: Bv);
}

/// A trait implemented by a mutable datastore that can hold _unchecked_ facts about contexts
pub trait WriteCtxFacts<C, T> {}

/// A typing derivation in a given context
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct HasTyIn<T> {
    pub tm: T,
    pub ty: T,
}

impl<T> HasTyIn<T> {
    /// Convert to a goal
    pub fn goal<C>(self, ctx: C) -> Goal<C, T> {
        Goal::HasTy(HasTy {
            ctx,
            tm: self.tm,
            ty: self.ty,
        })
    }

    /// Succeed
    pub fn finish_rule<C, S, K>(self, ctx: C, strategy: &mut S) -> HasTyIn<T>
    where
        T: Copy,
        S: Strategy<C, T, K>,
    {
        strategy.finish_rule(self.goal(ctx));
        self
    }
}

/// A typing derivation in a given context under a binder
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct HasTyUnderIn<T> {
    pub binder: T,
    pub tm: T,
    pub ty: T,
}

impl<T> HasTyUnderIn<T> {
    /// Convert to a goal
    pub fn goal<C>(self, ctx: C) -> Goal<C, T> {
        Goal::HasTyUnder(HasTyUnder {
            ctx,
            binder: self.binder,
            tm: self.tm,
            ty: self.ty,
        })
    }

    /// Succeed
    pub fn finish_rule<C, S, K>(self, ctx: C, strategy: &mut S) -> HasTyUnderIn<T>
    where
        T: Copy,
        S: Strategy<C, T, K>,
    {
        strategy.finish_rule(self.goal(ctx));
        self
    }
}

/// A term is an inhabited type
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct IsInhabIn<T>(pub T);

impl<T> IsInhabIn<T> {
    /// Convert to a goal
    pub fn goal<C>(self, ctx: C) -> Goal<C, T> {
        Goal::IsInhab(IsInhab { ctx, tm: self.0 })
    }

    /// Succeed
    pub fn finish_rule<C, S, K>(self, ctx: C, strategy: &mut S) -> IsInhabIn<T>
    where
        T: Copy,
        S: Strategy<C, T, K>,
    {
        strategy.finish_rule(self.goal(ctx));
        self
    }
}

/// An equation between two terms
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct Eqn<T> {
    pub lhs: T,
    pub rhs: T,
}

impl<T> Eqn<T> {
    /// Convert to a goal
    pub fn goal<C>(self, ctx: C) -> Goal<C, T> {
        Goal::EqIn(EqIn {
            ctx,
            lhs: self.lhs,
            rhs: self.rhs,
        })
    }

    /// Succeed
    pub fn finish_rule<C, S, K>(self, ctx: C, strategy: &mut S) -> Eqn<T>
    where
        T: Copy,
        S: Strategy<C, T, K>,
    {
        strategy.finish_rule(self.goal(ctx));
        self
    }
}

/// A statement of well-formedness
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct IsWf<C, T> {
    pub ctx: C,
    pub tm: T,
}

/// A term is a valid type
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct IsTy<C, T> {
    pub ctx: C,
    pub tm: T,
}

/// A term is an inhabited type
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct IsInhab<C, T> {
    pub ctx: C,
    pub tm: T,
}

/// A term is an empty type
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct IsEmpty<C, T> {
    pub ctx: C,
    pub tm: T,
}

/// A term is a proposition
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct IsProp<C, T> {
    pub ctx: C,
    pub tm: T,
}

/// A typing derivation
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct HasTy<C, T> {
    pub ctx: C,
    pub tm: T,
    pub ty: T,
}

/// A term is a type under a binder
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct IsTyUnder<C, T> {
    pub ctx: C,
    pub binder: T,
    pub tm: T,
}

/// A typing derivation under a binder
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct HasTyUnder<C, T> {
    pub ctx: C,
    pub binder: T,
    pub tm: T,
    pub ty: T,
}

/// A universally quantified statement of inhabitance
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct ForallInhabUnder<C, T> {
    pub ctx: C,
    pub binder: T,
    pub ty: T,
}

/// An existentially quantified statement of inhabitance
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct ExistsInhabUnder<C, T> {
    pub ctx: C,
    pub binder: T,
    pub ty: T,
}

/// Equality in a context
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct EqIn<C, T> {
    pub ctx: C,
    pub lhs: T,
    pub rhs: T,
}

/// A goal for a strategy
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub enum Goal<C, T> {
    /// A context is contradictory
    IsContr(C),
    /// A term is well-formed in the given context
    IsWf(IsWf<C, T>),
    /// A term is a type in the given context
    IsTy(IsTy<C, T>),
    /// A type is inhabited in the given context
    IsInhab(IsInhab<C, T>),
    /// A type is empty in the given context
    IsEmpty(IsEmpty<C, T>),
    /// A term is a proposition in the given context
    IsProp(IsProp<C, T>),
    /// A term has a type in the given context
    HasTy(HasTy<C, T>),
    /// A term is a type under a binder in the given context
    IsTyUnder(IsTyUnder<C, T>),
    /// A term has a type under a binder in the given context
    HasTyUnder(HasTyUnder<C, T>),
    /// A term is always inhabited under a binder in the given context
    ForallInhabUnder(ForallInhabUnder<C, T>),
    /// There exists a value of the binder type such that the term is inhabited in the given context
    ExistsInhabUnder(ExistsInhabUnder<C, T>),
    /// Two terms are equal in the given context
    EqIn(EqIn<C, T>),
}

impl<C, T> From<IsWf<C, T>> for Goal<C, T> {
    fn from(g: IsWf<C, T>) -> Self {
        Goal::IsWf(g)
    }
}

impl<C, T> From<IsTy<C, T>> for Goal<C, T> {
    fn from(g: IsTy<C, T>) -> Self {
        Goal::IsTy(g)
    }
}

impl<C, T> From<IsInhab<C, T>> for Goal<C, T> {
    fn from(g: IsInhab<C, T>) -> Self {
        Goal::IsInhab(g)
    }
}

impl<C, T> From<IsEmpty<C, T>> for Goal<C, T> {
    fn from(g: IsEmpty<C, T>) -> Self {
        Goal::IsEmpty(g)
    }
}

impl<C, T> From<IsProp<C, T>> for Goal<C, T> {
    fn from(g: IsProp<C, T>) -> Self {
        Goal::IsProp(g)
    }
}

impl<C, T> From<HasTy<C, T>> for Goal<C, T> {
    fn from(g: HasTy<C, T>) -> Self {
        Goal::HasTy(g)
    }
}

impl<C, T> From<IsTyUnder<C, T>> for Goal<C, T> {
    fn from(g: IsTyUnder<C, T>) -> Self {
        Goal::IsTyUnder(g)
    }
}

impl<C, T> From<HasTyUnder<C, T>> for Goal<C, T> {
    fn from(g: HasTyUnder<C, T>) -> Self {
        Goal::HasTyUnder(g)
    }
}

impl<C, T> From<ForallInhabUnder<C, T>> for Goal<C, T> {
    fn from(g: ForallInhabUnder<C, T>) -> Self {
        Goal::ForallInhabUnder(g)
    }
}

impl<C, T> From<ExistsInhabUnder<C, T>> for Goal<C, T> {
    fn from(g: ExistsInhabUnder<C, T>) -> Self {
        Goal::ExistsInhabUnder(g)
    }
}

impl<C, T> From<EqIn<C, T>> for Goal<C, T> {
    fn from(g: EqIn<C, T>) -> Self {
        Goal::EqIn(g)
    }
}

impl<C, T> Goal<C, T> {
    /// Check whether this goal is true
    pub fn check<R: ReadFacts<C, T> + ?Sized>(self, ker: &R) -> bool {
        match self {
            Goal::IsContr(c) => ker.is_contr(c),
            Goal::IsWf(g) => ker.is_wf(g.ctx, g.tm),
            Goal::IsTy(g) => ker.is_ty(g.ctx, g.tm),
            Goal::IsInhab(g) => ker.is_inhab(g.ctx, g.tm),
            Goal::IsEmpty(g) => ker.is_empty(g.ctx, g.tm),
            Goal::IsProp(g) => ker.is_prop(g.ctx, g.tm),
            Goal::HasTy(g) => ker.has_ty(g.ctx, g.tm, g.ty),
            Goal::IsTyUnder(g) => ker.is_ty_under(g.ctx, g.binder, g.tm),
            Goal::HasTyUnder(g) => ker.has_ty_under(g.ctx, g.binder, g.tm, g.ty),
            Goal::ForallInhabUnder(g) => ker.forall_inhab_under(g.ctx, g.binder, g.ty),
            Goal::ExistsInhabUnder(g) => ker.exists_inhab_under(g.ctx, g.binder, g.ty),
            Goal::EqIn(g) => ker.eq_in(g.ctx, g.lhs, g.rhs),
        }
    }
}

/// A strategy tells a kernel how to derive facts about terms in a context
pub trait Strategy<C, T, K: ?Sized> {
    /// The type returned by the strategy on failure
    type Fail;

    /// Attempt to prove a goal
    fn prove_goal(
        &mut self,
        ker: &mut K,
        goal: Goal<C, T>,
        msg: &'static str,
        attempt_no: usize,
    ) -> Result<(), Self::Fail>;

    /// Called when the top goal in the stack has failed
    ///
    /// This is usually called by returning an `Err` from `prove_has_ty`, but might be called on
    /// continue due to a wrapping strategy triggering the failure.
    fn on_failure(&mut self, _goal: Goal<C, T>, _err: Option<&mut Self::Fail>) {}

    /// Called when the top goal in the stack has succeeded
    fn on_success(&mut self, _goal: Goal<C, T>) {}

    /// Begin a goal
    fn start_goal(&mut self, _goal: Goal<C, T>) -> Result<(), Self::Fail> {
        Ok(())
    }

    //TODO: register side conditions as well?

    /// Begin a derivation
    fn start_rule(&mut self, _rule: &'static str) -> Result<(), Self::Fail> {
        Ok(())
    }

    /// End a successful derivation
    fn finish_rule(&mut self, _result: Goal<C, T>) {}

    /// An irrecoverable failure of a derivation
    fn fail(&mut self, msg: &'static str) -> Self::Fail;
}

impl<C, T, K : ?Sized> Strategy<C, T, K> for () {
    type Fail = &'static str;

    fn prove_goal(
        &mut self,
        _ker: &mut K,
        _goal: Goal<C, T>,
        msg: &'static str,
        _attempt_no: usize,
    ) -> Result<(), Self::Fail> {
        Err(msg)
    }

    fn fail(&mut self, msg: &'static str) -> Self::Fail {
        msg
    }
}

pub trait Ensure<C: Copy, T: Copy + PartialEq>: ReadFacts<C, T> + TermStore<C, T> {
    /// Attempt to prove a goal
    fn ensure_goal<S>(
        &mut self,
        goal: Goal<C, T>,
        strategy: &mut S,
        msg: &'static str,
    ) -> Result<(), S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_goal(goal)?;
        let mut attempt_no = 0;
        while !goal.check(self) {
            strategy
                .prove_goal(self, goal, msg, attempt_no)
                .map_err(|mut err| {
                    strategy.on_failure(goal, Some(&mut err));
                    err
                })?;
            attempt_no += 1;
        }
        strategy.on_success(goal);
        Ok(())
    }

    /// Attempt to prove that a context is contradictory
    fn ensure_is_contr<S>(
        &mut self,
        ctx: C,
        strategy: &mut S,
        msg: &'static str,
    ) -> Result<(), S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        self.ensure_goal(Goal::IsContr(ctx), strategy, msg)
    }

    /// Attempt to prove that a term is well-formed in a context
    fn ensure_is_wf<S>(
        &mut self,
        ctx: C,
        tm: T,
        strategy: &mut S,
        msg: &'static str,
    ) -> Result<(), S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        self.ensure_goal(IsWf { ctx, tm }.into(), strategy, msg)
    }

    /// Attempt to prove that a term is a type in a context
    fn ensure_is_ty<S>(
        &mut self,
        ctx: C,
        tm: T,
        strategy: &mut S,
        msg: &'static str,
    ) -> Result<(), S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        self.ensure_goal(IsTy { ctx, tm }.into(), strategy, msg)
    }

    /// Attempt to prove that a term is an inhabited type in a context
    fn ensure_is_inhab<S>(
        &mut self,
        ctx: C,
        tm: T,
        strategy: &mut S,
        msg: &'static str,
    ) -> Result<(), S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        self.ensure_goal(IsInhab { ctx, tm }.into(), strategy, msg)
    }

    /// Attempt to prove that a term is an empty type in a context
    fn ensure_is_empty<S>(
        &mut self,
        ctx: C,
        tm: T,
        strategy: &mut S,
        msg: &'static str,
    ) -> Result<(), S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        self.ensure_goal(IsEmpty { ctx, tm }.into(), strategy, msg)
    }

    /// Attempt to prove that a term is a proposition in a context
    fn ensure_is_prop<S>(
        &mut self,
        ctx: C,
        tm: T,
        strategy: &mut S,
        msg: &'static str,
    ) -> Result<(), S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        self.ensure_goal(IsProp { ctx, tm }.into(), strategy, msg)
    }

    /// Attempt to prove that a term has a given type in a context
    fn ensure_has_ty<S>(
        &mut self,
        ctx: C,
        tm: T,
        ty: T,
        strategy: &mut S,
        msg: &'static str,
    ) -> Result<(), S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        self.ensure_goal(HasTy { ctx, tm, ty }.into(), strategy, msg)
    }

    /// Attempt to prove that a term is a type in a context under a binder
    fn ensure_is_ty_under<S>(
        &mut self,
        ctx: C,
        binder: T,
        tm: T,
        strategy: &mut S,
        msg: &'static str,
    ) -> Result<(), S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        self.ensure_goal(IsTyUnder { ctx, binder, tm }.into(), strategy, msg)
    }

    /// Attempt to prove that a term has a given type in a context under a binder
    fn ensure_has_ty_under<S>(
        &mut self,
        ctx: C,
        binder: T,
        tm: T,
        ty: T,
        strategy: &mut S,
        msg: &'static str,
    ) -> Result<(), S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        self.ensure_goal(
            HasTyUnder {
                ctx,
                binder,
                tm,
                ty,
            }
            .into(),
            strategy,
            msg,
        )
    }

    /// Attempt to prove that a term is always inhabited in a context under a binder
    fn ensure_forall_inhab_under<S>(
        &mut self,
        ctx: C,
        binder: T,
        ty: T,
        strategy: &mut S,
        msg: &'static str,
    ) -> Result<(), S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        self.ensure_goal(ForallInhabUnder { ctx, binder, ty }.into(), strategy, msg)
    }

    /// Attempt to prove that there exists a value of the binder type such that the term is
    /// inhabited
    fn ensure_exists_inhab_under<S>(
        &mut self,
        ctx: C,
        binder: T,
        ty: T,
        strategy: &mut S,
        msg: &'static str,
    ) -> Result<(), S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        self.ensure_goal(ExistsInhabUnder { ctx, binder, ty }.into(), strategy, msg)
    }

    /// Attempt to prove that two terms are equal in a context
    fn ensure_eq_in<S>(
        &mut self,
        ctx: C,
        lhs: T,
        rhs: T,
        strategy: &mut S,
        msg: &'static str,
    ) -> Result<(), S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        self.ensure_goal(EqIn { ctx, lhs, rhs }.into(), strategy, msg)
    }

    /// Ensure that all assumptions in a context are valid under a binder
    fn ensure_assumptions_valid_under<S>(
        &mut self,
        ctx: C,
        binder: T,
        target: C,
        strategy: &mut S,
        msg: &'static str,
    ) -> Result<(), S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        let assumptions: SmallVec<[T; 16]> = (0..self.num_assumptions(target))
            .map(|i| self.assumption(target, i).unwrap())
            .collect();
        for &assumption in &assumptions {
            let ty = self.import(ctx, target, assumption);
            self.ensure_forall_inhab_under(ctx, binder, ty, strategy, msg)?;
        }
        // TODO: rather than checking assumptions match directly, it may make more sense to:
        // - re-collect assumptions
        // - sort and dedup both lists
        // - check equal
        //
        // This would require `T` to be `PartialOrd` (in fact, `Ord`) as well.
        //
        // In this case, it may make sense to move things to an extension trait?
        for (i, assumption) in assumptions.iter().enumerate() {
            if self.assumption(target, i) != Some(*assumption) {
                return Err(strategy.fail(kernel_error::ENSURE_ASSUMPTIONS_VALID_UNDER_CHANGED));
            }
        }
        Ok(())
    }
}

impl<C, T, K> Ensure<C, T> for K
where
    C: Copy,
    T: Copy + PartialEq,
    K: ReadFacts<C, T> + TermStore<C, T>,
{
}

/// Typing rules for deriving facts about terms from those already in the datastore
pub trait Derive<C, T> {
    /// Assume a new hypothesis in this context
    fn assume<S>(
        &mut self,
        ctx: C,
        ty: T,
        subctx: C,
        strategy: &mut S,
    ) -> Result<IsInhabIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Add a new variable to this context with the given type
    fn add_var<S>(&mut self, ctx: C, ty: T, strategy: &mut S) -> Result<Gv<C>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Compute the substitution of a term
    ///
    /// Given terms `bound` and `body`
    /// - If `body` is locally-closed, return it unchanged
    /// - Otherwise, `let bound in body`
    ///
    /// TODO: reference Lean
    fn subst(&mut self, ctx: C, bound: T, body: T) -> T;

    /// Compute the closure of a term
    ///
    /// Given term `tm` in context `ctx`
    /// - If `tm` does not depend on the variable `var`, return `tm`
    /// - Otherwise, return `close var tm`
    fn close(&mut self, ctx: C, var: Gv<C>, tm: T) -> T;

    /// Compute the closure of an imported term
    ///
    /// Given term `tm` in context `src`
    /// - If `src` has no parameter, or `tm` does not depend on the parameter of `src`, return the
    ///   import of `tm` into `ctx`
    /// - Otherwise, return `close src (import src tm)`
    fn close_import(&mut self, ctx: C, src: Gv<C>, tm: T) -> T;

    /// The substitution of a term is equal to its lazy substitution
    fn lazy_subst_eq(&mut self, ctx: C, bound: T, body: T) -> Eqn<T>;

    /// The closure of a term is equal to its lazy closure
    fn lazy_close_eq(&mut self, ctx: C, var: Gv<C>, tm: T) -> Eqn<T>;

    /// An
    fn lazy_import_eq(&mut self, ctx: C, src: C, tm: T) -> Eqn<T>;

    /// The closure of an imported term is equal to its lazy imported closure
    fn lazy_close_import_eq(&mut self, ctx: C, src: Gv<C>, tm: T) -> Eqn<T>;

    /// Check a term has type `B` under a binder `A`
    ///
    /// Checks that:
    /// - `binder` is a valid type in `Γ`
    /// - `src` is a child of `ctx` with parameter `x : binder`
    /// - `tm` has type `ty` in context `src`
    ///
    /// If so, then `close x tm` has type `close x ty` under `binder` in `ctx`
    ///
    /// TODO: reference Lean
    ///
    /// # Examples
    /// ```rust
    /// # use covalence_kernel::kernel::*;
    /// # use covalence_kernel::derive::kernel_error;
    /// # let mut ker = Kernel::new();
    /// # let ctx = ker.new_ctx();
    /// let emp = ker.add(ctx, Node::Empty);
    /// let x = ker.with_param(ctx, emp, &mut ()).unwrap();
    /// let tm = ker.add(ctx, Node::Fv(x));
    /// let res = ker.derive_close_has_ty_under(ctx, x, tm, emp, &mut ()).unwrap();
    /// let close_x = ker.close(ctx, x, tm);
    /// assert_eq!(res.tm, close_x);
    /// assert_eq!(res.ty, emp);
    /// ```
    fn derive_close_has_ty_under<S>(
        &mut self,
        ctx: C,
        src: Gv<C>,
        tm: T,
        ty: T,
        strategy: &mut S,
    ) -> Result<HasTyUnderIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Typecheck a variable
    ///
    /// Corresponds to the rule
    /// ```text
    /// Γ ok
    /// Γ(x) = A
    /// ===
    /// Γ ⊢ x : A
    /// ```
    /// or, in Lean,
    /// ```lean
    /// theorem Ctx.KHasTy.fv {Γ x A} (hΓ : Ok Γ) (hA : Lookup Γ x A) : KHasTy Γ A.erase (.fv x)
    /// ```
    fn derive_fv<S>(&mut self, ctx: C, var: Gv<C>, strategy: &mut S) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Typecheck a typing universe
    ///
    /// Corresponds to the rule
    /// ```text
    /// Γ ok
    /// ===
    /// Γ ⊢ U_ℓ : U_(ℓ + 1)
    /// ```
    /// or, in Lean,
    /// ```lean
    /// theorem Ctx.KHasTy.univ {Γ ℓ} (h : Ok Γ) : KHasTy Γ (.univ (ℓ + 1)) (.univ ℓ)
    /// ```
    fn derive_univ(&mut self, ctx: C, lvl: ULvl) -> HasTyIn<T>;

    /// Typecheck the unit type
    ///
    /// Corresponds to the rule
    /// ```text
    /// Γ ok
    /// ===
    /// Γ ⊢ 1 : U_ℓ
    /// ```
    /// or, in Lean,
    /// ```lean
    /// theorem Ctx.KHasTy.unit {Γ ℓ} (h : Ok Γ) : KHasTy Γ (.univ ℓ) .unit
    /// ```
    fn derive_unit(&mut self, ctx: C, lvl: ULvl) -> HasTyIn<T>;

    /// Typecheck the unique value of the unit type
    ///
    /// Corresponds to the rule
    /// ```text
    /// Γ ok
    /// ===
    /// Γ ⊢ * : 1
    /// ```
    /// or, in Lean,
    /// ```lean
    /// theorem Ctx.KHasTy.null {Γ} (h : Ok Γ) : KHasTy Γ .unit .null
    /// ```
    fn derive_nil(&mut self, ctx: C) -> HasTyIn<T>;

    /// Typecheck the unit type
    ///
    /// Corresponds to the rule
    /// ```text
    /// Γ ok
    /// ===
    /// Γ ⊢ 0 : U_ℓ
    /// ```
    /// or, in Lean,
    /// ```lean
    /// theorem Ctx.KHasTy.empty {Γ ℓ} (h : Ok Γ) : KHasTy Γ (.univ ℓ) .empty
    /// ```
    fn derive_empty(&mut self, ctx: C, lvl: ULvl) -> HasTyIn<T>;

    /// Typecheck an equation between terms
    ///
    /// Corresponds to the rule
    /// ```text
    /// Γ ⊢ a : A
    /// Γ ⊢ b : A
    /// ===
    /// Γ ⊢ a = b : 2
    /// ```
    /// or, in Lean,
    /// ```lean
    /// theorem Ctx.KHasTy.eqn
    ///   {Γ A a b} (ha : KHasTy Γ A a) (hb : KHasTy Γ A b)
    ///   : KHasTy Γ (.univ 0) (.eqn a b)
    /// ```
    fn derive_eqn<S>(
        &mut self,
        ctx: C,
        ty: T,
        lhs: T,
        rhs: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Typecheck a pi type
    ///
    /// Corresponds to the rule
    /// ```text
    /// Γ ⊢ A : U_m
    /// ∀x ∉ L . Γ , x : A ⊢ B^x : U_n
    /// imax(m, n) ≤ ℓ
    /// ===
    /// Γ ⊢ Π_ℓ A . B : U_ℓ
    /// ```
    /// or, in Lean,
    /// ```lean
    /// theorem Ctx.KHasTy.pi {Γ A B m n ℓ}
    ///   (hA : KHasTy Γ (.univ m) A) (hB : KHasTyUnder Γ A (.univ n) B)
    ///   (hℓ : m.imax n ≤ ℓ)
    ///   : KHasTy Γ (.univ ℓ) (.pi A B)
    /// ```
    fn derive_pi<S>(
        &mut self,
        ctx: C,
        arg_lvl: ULvl,
        res_lvl: ULvl,
        lvl: ULvl,
        arg_ty: T,
        res_ty: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Typecheck a sigma type
    ///
    /// Corresponds to the rule
    /// ```text
    /// Γ ⊢ A : U_m
    /// ∀x ∉ L . Γ , x : A ⊢ B^x : U_n
    /// m ≤ ℓ
    /// n ≤ ℓ
    /// ===
    /// Γ ⊢ Σ_ℓ A . B : U_ℓ
    /// ```
    /// or, in Lean,
    /// ```lean
    /// theorem Ctx.KHasTy.sigma' {Γ A B m n ℓ}
    ///   (hA : KHasTy Γ (.univ m) A) (hB : KHasTyUnder Γ A (.univ n) B)
    ///   (hm : m ≤ ℓ) (hn : n ≤ ℓ)
    ///   : KHasTy Γ (.univ ℓ) (.sigma A B)
    /// ```
    fn derive_sigma<S>(
        &mut self,
        ctx: C,
        arg_lvl: ULvl,
        res_lvl: ULvl,
        lvl: ULvl,
        arg_ty: T,
        res_ty: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Typecheck an abstraction
    ///
    /// Corresponds to the rule
    /// ```text
    /// ∀x ∉ L . Γ, x : A ⊢ b^x : B^x
    /// ===
    /// Γ ⊢ λ A . b : Π A . B
    /// ```
    /// or, in Lean,
    /// ```lean
    /// theorem Ctx.KHasTy.abs {Γ A B b}
    ///   (hB : KHasTyUnder Γ A B b) : KHasTy Γ (.pi A B) (.abs A b)
    /// ```
    fn derive_abs<S>(
        &mut self,
        ctx: C,
        arg_ty: T,
        body: T,
        res_ty: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Typecheck an application
    ///
    /// Corresponds to the rule
    /// ```text
    /// Γ ⊢ f : Π A . B
    /// Γ ⊢ a : A
    /// ===
    /// Γ ⊢ f a : B^a
    /// ```
    /// or, in Lean,
    /// ```lean
    /// theorem Ctx.KHasTy.app {Γ A B f a}
    ///   (hA : KHasTy Γ (.pi A B) f) (hB : KHasTy Γ A a) : KHasTy Γ (B.lst 0 a) (.app f a)
    /// ```
    fn derive_app<S>(
        &mut self,
        ctx: C,
        arg_ty: T,
        res_ty: T,
        func: T,
        arg: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Typecheck a pair
    ///
    /// Corresponds to the rule
    /// ```text
    /// ∀x ∉ L . Γ, x : A ⊢ B^x ty
    /// Γ ⊢ a : A
    /// Γ ⊢ b : B^a
    /// ===
    /// Γ ⊢ (a, b) : Σ A . B
    /// ```
    /// or, in Lean,
    /// ```lean
    /// theorem Ctx.KHasTy.pair {Γ A B a b}
    ///   (hB : KIsTyUnder Γ A B) (ha : KHasTy Γ A a) (hb : KHasTy Γ (B.lst 0 a) b)
    /// ```
    fn derive_pair<S>(
        &mut self,
        ctx: C,
        arg_ty: T,
        res_ty: T,
        fst: T,
        snd: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Typecheck the first projection of a pair
    ///
    /// Corresponds to the rule
    /// ```text
    /// Γ ⊢ p : Σ A . B
    /// ===
    /// Γ ⊢ fst p : A
    /// ```
    /// or, in Lean,
    /// ```lean
    /// theorem Ctx.KHasTy.fst {Γ A B p} (hp : KHasTy Γ (.sigma A B) p) : KHasTy Γ A (.fst p)
    /// ```
    ///
    /// If `p :≡ (a, b)`, also inserts the equation `Γ ⊢ fst (a, b) = a`
    /// (see: `Ctx.KIsWf.beta_fst_pair`)
    fn derive_fst<S>(
        &mut self,
        ctx: C,
        arg_ty: T,
        res_ty: T,
        pair: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Typecheck the second projection of a pair
    ///
    /// Additionally typechecks the first projection using the rule for `fst`
    ///
    /// Corresponds to the rule
    /// ```text
    /// Γ ⊢ p : Σ A . B
    /// ===
    /// Γ ⊢ snd p : B^(fst p)
    /// + Γ ⊢ fst p : A
    /// ```
    /// or, in Lean,
    /// ```lean
    /// theorem Ctx.KHasTy.snd {Γ A B p} (hp : KHasTy Γ (.sigma A B) p)
    ///   : KHasTy Γ (B.lst 0 (.fst p)) (.snd p)
    ///
    /// -- Additional results:
    /// theorem Ctx.KHasTy.fst {Γ A B p} (hp : KHasTy Γ (.sigma A B) p) : KHasTy Γ A (.fst p)
    /// ```
    ///
    /// If `p :≡ (a, b)`, also inserts the equations `Γ ⊢ fst (a, b) ≡ a` and `Γ ⊢ snd (a, b) ≡ b`
    /// (see: `Ctx.KIsWf.beta_fst_pair`, `Ctx.KIsWf.beta_snd_pair`)
    fn derive_snd<S>(
        &mut self,
        ctx: C,
        arg_ty: T,
        res_ty: T,
        pair: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Typecheck a dependent if-then-else
    ///
    /// If the condition is inhabited, equates it to the (lazy substitution of) the then-branch
    ///
    /// If the condition is known empty, equates it to the (lazy substitution of) the else-branch
    ///
    /// TODO: reference Lean
    fn derive_dite<S>(
        &mut self,
        ctx: C,
        cond: T,
        then_br: T,
        else_br: T,
        ty: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    // TODO: dite with different branch types; fusion lore

    /// Typecheck a propositional truncation
    ///
    /// Inherits inhabitance/emptiness from the underlying type
    ///
    /// TODO: reference Lean
    fn derive_trunc<S>(&mut self, ctx: C, ty: T, strategy: &mut S) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Typecheck Hilbert's ε-operator
    ///
    /// TODO: reference Lean
    fn derive_choose<S>(
        &mut self,
        ctx: C,
        ty: T,
        pred: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Typecheck the natural numbers
    ///
    /// TODO: reference Lean
    fn derive_nats<S>(
        &mut self,
        ctx: C,
        lvl: ULvl,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Typecheck a 64-bit natural number
    ///
    /// TODO: reference Lean
    fn derive_n64(&mut self, ctx: C, n: u64) -> HasTyIn<T>;

    /// Typecheck the successor function on natural numbers
    ///
    /// TODO: reference Lean
    fn derive_succ<S>(&mut self, ctx: C, n: T, strategy: &mut S) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Typecheck the recursor on natural numbers
    ///
    /// TODO: reference Lean
    fn derive_natrec<S>(
        &mut self,
        ctx: C,
        mot: T,
        z: T,
        s: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Typecheck a let-binding
    ///
    /// If the body does not have a free variable, this also equates the binding to its body.
    ///
    /// TODO: reference Lean
    fn derive_let<S>(
        &mut self,
        ctx: C,
        bound: T,
        bound_ty: T,
        body: T,
        body_ty: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Beta reduction for abstractions
    ///
    /// For well-formed `Γ ⊢ tm ≡ (λ A . b) a`, `Γ ⊢ a : A`; `Γ ⊢ tm b ≡ b^a`
    ///
    /// TODO: reference Lean
    fn derive_beta_abs<S>(
        &mut self,
        ctx: C,
        tm: T,
        arg: T,
        strategy: &mut S,
    ) -> Result<Eqn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Beta reduction for natural number recursors at zero
    ///
    /// For well-formed `Γ ⊢ tm ≡ natrec C z s`; `Γ ⊢ tm 0 = z`
    ///
    /// TODO: reference Lean
    fn derive_beta_zero<S>(&mut self, ctx: C, tm: T, strategy: &mut S) -> Result<Eqn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Beta reduction for natural number recursors at successors
    ///
    /// For well-formed `Γ ⊢ tm ≡ natrec C z s` and `Γ ⊢ n : ℕ`; `Γ ⊢ tm (succ n) = s^n (tm n)`
    ///
    /// TODO: reference Lean
    fn derive_beta_succ<S>(
        &mut self,
        ctx: C,
        tm: T,
        n: T,
        strategy: &mut S,
    ) -> Result<Eqn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Specification for choice
    ///
    /// If `∃A . φ` (encoded as Σ A . φ inhab) then `Γ ⊢ φ^(choose A φ)`
    ///
    /// TODO: reference lean
    fn derive_choose_spec<S>(
        &mut self,
        ctx: C,
        ty: T,
        pred: T,
        strategy: &mut S,
    ) -> Result<IsInhabIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Extensionality for the unit type
    ///
    /// If `Γ ⊢ a : 1` then `Γ ⊢ a ≡ * : 1`
    ///
    /// TODO: reference Lean
    fn derive_unit_ext<S>(&mut self, ctx: C, a: T, strategy: &mut S) -> Result<Eqn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Extensionality for the true proposition
    ///
    /// If `Γ ⊢ a : 2` and `Γ ⊢ a inhab` then `Γ ⊢ a ≡ 1 : 2`
    ///
    /// TODO: reference Lean
    fn derive_prop_ext_tt<S>(&mut self, ctx: C, a: T, strategy: &mut S) -> Result<Eqn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Extensionality for the false proposition
    ///
    /// If `Γ ⊢ a : 2` and `Γ ⊢ a empty` then `Γ ⊢ a ≡ 0 : 2`
    ///
    /// TODO: reference Lean
    fn derive_prop_ext_ff<S>(&mut self, ctx: C, a: T, strategy: &mut S) -> Result<Eqn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Extensionality
    ///
    /// If `Γ ⊢ a = b` then `Γ ⊢ a ≡ b`
    ///
    /// TODO: reference Lean
    fn derive_ext<S>(
        &mut self,
        ctx: C,
        lhs: T,
        rhs: T,
        strategy: &mut S,
    ) -> Result<Eqn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Eta for functions
    ///
    /// If `Γ ⊢ f : Π A . B` then `Γ ⊢ f ≡ λx. f x : Π A . B`
    ///
    /// TODO: reference Lean
    fn derive_pi_eta<S>(
        &mut self,
        ctx: C,
        ty: T,
        f: T,
        strategy: &mut S,
    ) -> Result<Eqn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Eta for pairs
    ///
    /// If `Γ ⊢ p : Σ A . B` then `Γ ⊢ p ≡ (fst p, snd p) : Σ A . B`
    ///
    /// TODO: reference Lean
    fn derive_sigma_eta<S>(
        &mut self,
        ctx: C,
        ty: T,
        p: T,
        strategy: &mut S,
    ) -> Result<Eqn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;
}

/// The `covalence` kernel
///
/// This type is parametrized by its datastore `D`
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
pub struct Kernel<D>(D);

impl<D> Kernel<D> {
    /// Get an _immutable_ reference to the underlying datastore
    pub fn data(&self) -> &D {
        &self.0
    }
}

impl<C, T, D: ReadFacts<C, T>> ReadFacts<C, T> for Kernel<D> {
    fn is_root(&self, ctx: C) -> bool {
        self.0.is_root(ctx)
    }

    fn is_contr(&self, ctx: C) -> bool {
        self.0.is_contr(ctx)
    }

    fn parent(&self, ctx: C) -> Option<C> {
        self.0.parent(ctx)
    }

    fn bvi(&self, ctx: C, tm: T) -> Bv {
        self.0.bvi(ctx, tm)
    }

    fn is_subctx(&self, lo: C, hi: C) -> bool {
        self.0.is_subctx(lo, hi)
    }

    fn is_subctx_of_parent(&self, lo: C, hi: C) -> bool {
        self.0.is_subctx_of_parent(lo, hi)
    }

    fn is_wf(&self, ctx: C, tm: T) -> bool {
        self.0.is_wf(ctx, tm)
    }

    fn is_ty(&self, ctx: C, tm: T) -> bool {
        self.0.is_ty(ctx, tm)
    }

    fn is_inhab(&self, ctx: C, tm: T) -> bool {
        self.0.is_inhab(ctx, tm)
    }

    fn is_empty(&self, ctx: C, tm: T) -> bool {
        self.0.is_empty(ctx, tm)
    }

    fn is_prop(&self, ctx: C, tm: T) -> bool {
        self.0.is_prop(ctx, tm)
    }

    fn has_var(&self, ctx: C, tm: T, var: Gv<C>) -> bool {
        self.0.has_var(ctx, tm, var)
    }

    fn syn_eq(&self, lctx: C, lhs: T, rctx: C, rhs: T) -> bool {
        self.0.syn_eq(lctx, lhs, rctx, rhs)
    }

    fn eq_in(&self, ctx: C, lhs: T, rhs: T) -> bool {
        self.0.eq_in(ctx, lhs, rhs)
    }

    fn has_ty(&self, ctx: C, tm: T, ty: T) -> bool {
        self.0.has_ty(ctx, tm, ty)
    }

    fn is_ty_under(&self, ctx: C, binder: T, ty: T) -> bool {
        self.0.is_ty_under(ctx, binder, ty)
    }

    fn has_ty_under(&self, ctx: C, binder: T, tm: T, ty: T) -> bool {
        self.0.has_ty_under(ctx, binder, tm, ty)
    }

    fn u_le(&self, lo: ULvl, hi: ULvl) -> bool {
        self.0.u_le(lo, hi)
    }

    fn u_lt(&self, lo: ULvl, hi: ULvl) -> bool {
        self.0.u_lt(lo, hi)
    }

    fn imax_le(&self, lo_lhs: ULvl, lo_rhs: ULvl, hi: ULvl) -> bool {
        self.0.imax_le(lo_lhs, lo_rhs, hi)
    }

    fn forall_inhab_under(&self, ctx: C, binder: T, ty: T) -> bool {
        self.0.forall_inhab_under(ctx, binder, ty)
    }

    fn exists_inhab_under(&self, ctx: C, binder: T, ty: T) -> bool {
        self.0.exists_inhab_under(ctx, binder, ty)
    }
}

impl<C, T, D: TermStore<C, T>> TermStore<C, T> for Kernel<D> {
    fn new_ctx(&mut self) -> C {
        self.0.new_ctx()
    }

    fn with_parent(&mut self, parent: C) -> C {
        self.0.with_parent(parent)
    }

    fn add(&mut self, ctx: C, term: GNode<C, T>) -> T {
        self.0.add(ctx, term)
    }

    fn import(&mut self, ctx: C, src: C, tm: T) -> T {
        self.0.import(ctx, src, tm)
    }

    fn node(&self, ctx: C, term: T) -> &GNode<C, T> {
        self.0.node(ctx, term)
    }

    fn lookup(&self, ctx: C, term: &mut GNode<C, T>) -> Option<T> {
        self.0.lookup(ctx, term)
    }

    fn lookup_import(&self, ctx: C, src: C, tm: T) -> Option<T> {
        self.0.lookup_import(ctx, src, tm)
    }

    fn var_ty(&mut self, ctx: C, var: Gv<C>) -> T {
        self.0.var_ty(ctx, var)
    }

    fn get_var_ty(&self, var: Gv<C>) -> T {
        self.0.get_var_ty(var)
    }

    fn num_assumptions(&self, ctx: C) -> usize {
        self.0.num_assumptions(ctx)
    }

    fn assumption(&self, ctx: C, ix: usize) -> Option<T> {
        self.0.assumption(ctx, ix)
    }

    fn num_vars(&self, ctx: C) -> usize {
        self.0.num_vars(ctx)
    }

    fn succ(&mut self, level: ULvl) -> ULvl {
        self.0.succ(level)
    }

    fn umax(&mut self, lhs: ULvl, rhs: ULvl) -> ULvl {
        self.0.umax(lhs, rhs)
    }

    fn imax(&mut self, lhs: ULvl, rhs: ULvl) -> ULvl {
        self.0.imax(lhs, rhs)
    }

    fn propagate_in(&mut self, ctx: C) -> usize {
        self.0.propagate_in(ctx)
    }
}

impl<
    C: Copy + PartialEq,
    T: Copy + PartialEq,
    D: TermStore<C, T> + ReadFacts<C, T> + WriteFacts<C, T>,
> Derive<C, T> for Kernel<D>
{
    fn assume<S>(
        &mut self,
        ctx: C,
        ty: T,
        subctx: C,
        strategy: &mut S,
    ) -> Result<IsInhabIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("assume")?;
        if !self.is_subctx_of_parent(subctx, ctx) {
            return Err(strategy.fail(kernel_error::ASSUME_NOT_SUBCTX));
        }
        let in_subctx = self.import(subctx, ctx, ty);
        // If this type is already inhabited in a subcontext, there's no need to add it as an
        // assumption
        if !self.is_inhab(subctx, in_subctx) {
            self.ensure_is_ty(subctx, in_subctx, strategy, kernel_error::ASSUME_IS_TY)?;
            self.0.assume_unchecked(ctx, ty);
        }
        Ok(IsInhabIn(ty).finish_rule(ctx, strategy))
    }

    fn add_var<S>(&mut self, ctx: C, ty: T, strategy: &mut S) -> Result<Gv<C>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("add_var")?;
        self.ensure_is_inhab(ctx, ty, strategy, kernel_error::ADD_VAR_IS_INHAB)?;
        let var = self.0.add_var_unchecked(ctx, ty);
        debug_assert!(self.0.eq_in(ctx, self.0.get_var_ty(var), ty));
        let tm = self.0.add(ctx, GNode::Fv(var));
        self.0.set_has_ty_unchecked(ctx, tm, ty);
        HasTyIn { tm, ty }.finish_rule(ctx, strategy);
        Ok(var)
    }

    fn subst(&mut self, ctx: C, bound: T, body: T) -> T {
        if self.bvi(ctx, body) == Bv(0) {
            return body;
        }
        self.add(ctx, GNode::Let(Bv(0), [bound, body]))
    }

    fn close(&mut self, ctx: C, var: Gv<C>, tm: T) -> T {
        //TODO: optimize this, and cover more cases
        if self.bvi(ctx, tm) == Bv(0) && !self.has_var(ctx, tm, var) {
            return tm;
        }
        self.add(
            ctx,
            GNode::Close(Close {
                under: Bv(0),
                var,
                tm,
            }),
        )
    }

    fn close_import(&mut self, ctx: C, var: Gv<C>, tm: T) -> T {
        let import = self.import(ctx, var.ctx, tm);
        //TODO: optimize this, and cover more cases
        if self.bvi(var.ctx, tm) == Bv(0) && !self.has_var(var.ctx, tm, var) {
            return import;
        }
        self.add(
            ctx,
            GNode::Close(Close {
                under: Bv(0),
                var,
                tm: import,
            }),
        )
    }

    //TODO: implement _eager_ import (i.e. deep copy; name this properly. clone?)

    //TODO: implement _eager_ substitution; combine with import

    //TODO: implement _eager_ close; combine with import

    //TODO: equalities for eager substitution, close, import

    fn lazy_subst_eq(&mut self, ctx: C, bound: T, body: T) -> Eqn<T> {
        let eager = self.add(ctx, GNode::Let(Bv(0), [bound, body]));
        let lazy = self.subst(ctx, bound, body);
        self.0.set_eq_unchecked(ctx, eager, lazy);
        Eqn {
            lhs: eager,
            rhs: lazy,
        }
    }

    fn lazy_close_eq(&mut self, ctx: C, var: Gv<C>, tm: T) -> Eqn<T> {
        let eager = self.add(
            ctx,
            GNode::Close(Close {
                under: Bv(0),
                var,
                tm,
            }),
        );
        let lazy = self.close(ctx, var, tm);
        self.0.set_eq_unchecked(ctx, eager, lazy);
        Eqn {
            lhs: eager,
            rhs: lazy,
        }
    }

    fn lazy_import_eq(&mut self, ctx: C, src: C, tm: T) -> Eqn<T> {
        let eager = self.add(ctx, GNode::Import(Import { ctx: src, tm }));
        let lazy = self.import(ctx, src, tm);
        self.0.set_eq_unchecked(ctx, eager, lazy);
        Eqn {
            lhs: eager,
            rhs: lazy,
        }
    }

    fn lazy_close_import_eq(&mut self, ctx: C, var: Gv<C>, tm: T) -> Eqn<T> {
        let import = self.add(ctx, GNode::Import(Import { ctx: var.ctx, tm }));
        let eager = self.add(
            ctx,
            GNode::Close(Close {
                under: Bv(0),
                var,
                tm: import,
            }),
        );
        let lazy = self.close_import(ctx, var, tm);
        self.0.set_eq_unchecked(ctx, eager, lazy);
        Eqn {
            lhs: eager,
            rhs: lazy,
        }
    }

    fn derive_close_has_ty_under<S>(
        &mut self,
        ctx: C,
        var: Gv<C>,
        tm: T,
        ty: T,
        strategy: &mut S,
    ) -> Result<HasTyUnderIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_close_has_ty_under")?;
        let import_tm = self.import(var.ctx, ctx, tm);
        let import_ty = self.import(var.ctx, ctx, ty);
        self.ensure_has_ty(
            var.ctx,
            import_tm,
            import_ty,
            strategy,
            kernel_error::DERIVE_CLOSE_HAS_TY_UNDER_HAS_TY,
        )?;
        let binder = self.var_ty(ctx, var);
        debug_assert!(
            self.is_ty(var.ctx, self.get_var_ty(var)),
            "var is valid in its context"
        );
        if var.ctx != ctx {
            // What we're really checking here is that every variable in `import_ty` and `import_tm`
            // either exists in `ctx` (due to our later subcontext check) or is `var` itself.
            //
            // But we can check this directly, and so relax this check, and maybe should, later!
            if self.num_vars(var.ctx) != 1 {
                return Err(strategy.fail(kernel_error::DERIVE_CLOSE_HAS_TY_UNDER_TOO_MANY_VARS));
            }
            // Now we check all the variable's context assumptions are implied by `binder` under
            // `ctx`
            self.ensure_assumptions_valid_under(
                ctx,
                binder,
                var.ctx,
                strategy,
                kernel_error::DERIVE_CLOSE_HAS_TY_UNDER_INVALID_ASSUMPTION,
            )?;
            // Finally, we check that the variable's parent context is a subcontext of `ctx`
            //
            // `ensure_assumptions_valid_under` should not be able to change this, since the check
            // is stable, but if we move to an unstable check its correct to check _afterwards_
            // rather than before!
            if self
                .parent(var.ctx)
                .is_some_and(|parent| !self.is_subctx(parent, ctx))
            {
                return Err(strategy.fail(kernel_error::DERIVE_CLOSE_HAS_TY_UNDER_ILL_SCOPED));
            }
        }
        let close_tm = self.close(ctx, var, tm);
        let close_ty = self.close(ctx, var, ty);
        self.0
            .set_has_ty_under_unchecked(ctx, binder, close_tm, close_ty);
        Ok(HasTyUnderIn {
            tm: close_tm,
            ty: close_ty,
            binder,
        }
        .finish_rule(ctx, strategy))
    }

    fn derive_fv<S>(&mut self, ctx: C, var: Gv<C>, strategy: &mut S) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_fv")?;
        if !self.is_subctx(var.ctx, ctx) {
            return Err(strategy.fail(kernel_error::DERIVE_FV_ILL_SCOPED));
        }
        //NOTE: this will crash if the variable is not in fact valid!
        let tm = self.add(ctx, GNode::Fv(var));
        let ty = self.var_ty(ctx, var);
        self.0.set_has_ty_unchecked(ctx, tm, ty);
        Ok(HasTyIn { tm, ty }.finish_rule(ctx, strategy))
    }

    fn derive_univ(&mut self, ctx: C, lvl: ULvl) -> HasTyIn<T> {
        let tm = self.add(ctx, GNode::U(lvl));
        let ty_lvl = self.succ(lvl);
        let ty = self.add(ctx, GNode::U(ty_lvl));
        self.0.set_has_ty_unchecked(ctx, tm, ty);
        HasTyIn { tm, ty }
    }

    fn derive_unit(&mut self, ctx: C, lvl: ULvl) -> HasTyIn<T> {
        let tm = self.add(ctx, GNode::Unit);
        let ty = self.add(ctx, GNode::U(lvl));
        self.0.set_has_ty_unchecked(ctx, tm, ty);
        self.0.set_is_prop_unchecked(ctx, tm);
        self.0.set_is_inhab_unchecked(ctx, tm);
        HasTyIn { tm, ty }
    }

    fn derive_nil(&mut self, ctx: C) -> HasTyIn<T> {
        let tm = self.add(ctx, GNode::Null);
        let ty = self.add(ctx, GNode::Unit);
        self.0.set_has_ty_unchecked(ctx, tm, ty);
        HasTyIn { tm, ty }
    }

    fn derive_empty(&mut self, ctx: C, lvl: ULvl) -> HasTyIn<T> {
        let tm = self.add(ctx, GNode::Empty);
        let ty = self.add(ctx, GNode::U(lvl));
        self.0.set_has_ty_unchecked(ctx, tm, ty);
        self.0.set_is_prop_unchecked(ctx, tm);
        self.0.set_is_empty_unchecked(ctx, tm);
        HasTyIn { tm, ty }
    }

    fn derive_eqn<S>(
        &mut self,
        ctx: C,
        ty: T,
        lhs: T,
        rhs: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_eqn")?;
        self.ensure_has_ty(ctx, lhs, ty, strategy, kernel_error::DERIVE_EQN_LHS)?;
        self.ensure_has_ty(ctx, rhs, ty, strategy, kernel_error::DERIVE_EQN_RHS)?;
        let tm = self.add(ctx, GNode::Eqn([lhs, rhs]));
        let ty = self.add(ctx, GNode::U(ULvl::PROP));
        self.0.set_has_ty_unchecked(ctx, tm, ty);
        Ok(HasTyIn { tm, ty }.finish_rule(ctx, strategy))
    }

    fn derive_pi<S>(
        &mut self,
        ctx: C,
        arg_lvl: ULvl,
        res_lvl: ULvl,
        lvl: ULvl,
        arg_ty: T,
        res_ty: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_pi")?;
        if !self.imax_le(arg_lvl, res_lvl, lvl) {
            return Err(strategy.fail(kernel_error::DERIVE_PI_IMAX_LE));
        }
        let arg_lvl_ty = self.add(ctx, GNode::U(arg_lvl));
        let res_lvl_ty = self.add(ctx, GNode::U(res_lvl));
        self.ensure_has_ty(
            ctx,
            arg_ty,
            arg_lvl_ty,
            strategy,
            kernel_error::DERIVE_PI_ARG_TY,
        )?;
        self.ensure_has_ty_under(
            ctx,
            arg_ty,
            res_ty,
            res_lvl_ty,
            strategy,
            kernel_error::DERIVE_PI_RES_TY,
        )?;
        let ty = self.add(ctx, GNode::U(lvl));
        let tm = self.add(ctx, GNode::Pi([arg_ty, res_ty]));
        self.0.set_has_ty_unchecked(ctx, tm, ty);
        Ok(HasTyIn { tm, ty }.finish_rule(ctx, strategy))
    }

    fn derive_sigma<S>(
        &mut self,
        ctx: C,
        arg_lvl: ULvl,
        res_lvl: ULvl,
        lvl: ULvl,
        arg_ty: T,
        res_ty: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_sigma")?;
        if !self.u_le(arg_lvl, lvl) {
            return Err(strategy.fail(kernel_error::DERIVE_SIGMA_ARG_LVL_LE));
        }
        if !self.u_le(res_lvl, lvl) {
            return Err(strategy.fail(kernel_error::DERIVE_SIGMA_RES_LVL_LE));
        }
        let arg_lvl_ty = self.add(ctx, GNode::U(arg_lvl));
        let res_lvl_ty = self.add(ctx, GNode::U(res_lvl));
        self.ensure_has_ty(
            ctx,
            arg_ty,
            arg_lvl_ty,
            strategy,
            kernel_error::DERIVE_SIGMA_ARG_TY,
        )?;
        self.ensure_has_ty_under(
            ctx,
            arg_ty,
            res_ty,
            res_lvl_ty,
            strategy,
            kernel_error::DERIVE_SIGMA_RES_TY,
        )?;
        let ty = self.add(ctx, GNode::U(lvl));
        let tm = self.add(ctx, GNode::Sigma([arg_ty, res_ty]));
        self.0.set_has_ty_unchecked(ctx, tm, ty);
        Ok(HasTyIn { tm, ty }.finish_rule(ctx, strategy))
    }

    fn derive_abs<S>(
        &mut self,
        ctx: C,
        arg_ty: T,
        body: T,
        res_ty: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_abs")?;
        self.ensure_has_ty_under(
            ctx,
            arg_ty,
            body,
            res_ty,
            strategy,
            kernel_error::DERIVE_ABS_BODY,
        )?;
        let tm = self.add(ctx, GNode::Abs([arg_ty, body]));
        let ty = self.add(ctx, GNode::Pi([arg_ty, res_ty]));
        self.0.set_has_ty_unchecked(ctx, tm, ty);
        Ok(HasTyIn { tm, ty }.finish_rule(ctx, strategy))
    }

    fn derive_app<S>(
        &mut self,
        ctx: C,
        arg_ty: T,
        res_ty: T,
        func: T,
        arg: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_app")?;
        self.ensure_has_ty(ctx, arg, arg_ty, strategy, kernel_error::DERIVE_APP_ARG)?;
        let pi = self.add(ctx, GNode::Pi([arg_ty, res_ty]));
        self.ensure_has_ty(ctx, func, pi, strategy, kernel_error::DERIVE_APP_FUNC)?;
        let tm = self.add(ctx, GNode::App([func, arg]));
        let ty = self.subst(ctx, arg, res_ty);
        self.0.set_has_ty_unchecked(ctx, tm, ty);
        Ok(HasTyIn { tm, ty }.finish_rule(ctx, strategy))
    }

    fn derive_pair<S>(
        &mut self,
        ctx: C,
        arg_ty: T,
        res_ty: T,
        fst: T,
        snd: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_pair")?;
        self.ensure_is_ty_under(
            ctx,
            arg_ty,
            res_ty,
            strategy,
            kernel_error::DERIVE_PAIR_RES_TY,
        )?;
        self.ensure_has_ty(ctx, fst, arg_ty, strategy, kernel_error::DERIVE_PAIR_FST)?;
        let snd_ty = self.subst(ctx, fst, res_ty);
        self.ensure_has_ty(ctx, snd, snd_ty, strategy, kernel_error::DERIVE_PAIR_SND)?;
        let tm = self.add(ctx, GNode::Pair([fst, snd]));
        let ty = self.add(ctx, GNode::Sigma([arg_ty, res_ty]));
        self.0.set_has_ty_unchecked(ctx, tm, ty);
        Ok(HasTyIn { tm, ty }.finish_rule(ctx, strategy))
    }

    fn derive_fst<S>(
        &mut self,
        ctx: C,
        arg_ty: T,
        res_ty: T,
        pair: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_fst")?;
        let sigma = self.add(ctx, GNode::Sigma([arg_ty, res_ty]));
        self.ensure_has_ty(ctx, pair, sigma, strategy, kernel_error::DERIVE_FST_PAIR)?;
        let tm = self.add(ctx, GNode::Fst([pair]));
        self.0.set_has_ty_unchecked(ctx, tm, arg_ty);
        if let &GNode::Pair([a, _]) = self.node(ctx, pair) {
            self.0.set_eq_unchecked(ctx, tm, a);
        }
        Ok(HasTyIn { tm, ty: arg_ty }.finish_rule(ctx, strategy))
    }

    fn derive_snd<S>(
        &mut self,
        ctx: C,
        arg_ty: T,
        res_ty: T,
        pair: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_snd")?;
        let sigma = self.add(ctx, GNode::Sigma([arg_ty, res_ty]));
        self.ensure_has_ty(ctx, pair, sigma, strategy, kernel_error::DERIVE_SND_PAIR)?;
        let fst = self.add(ctx, GNode::Fst([pair]));
        self.0.set_has_ty_unchecked(ctx, fst, arg_ty);
        let tm = self.add(ctx, GNode::Snd([pair]));
        let ty = self.subst(ctx, fst, res_ty);
        self.0.set_has_ty_unchecked(ctx, tm, ty);
        if let &GNode::Pair([a, b]) = self.node(ctx, pair) {
            self.0.set_eq_unchecked(ctx, fst, a);
            self.0.set_eq_unchecked(ctx, tm, b);
        }
        Ok(HasTyIn { tm, ty }.finish_rule(ctx, strategy))
    }

    fn derive_dite<S>(
        &mut self,
        ctx: C,
        cond: T,
        then_br: T,
        else_br: T,
        ty: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_dite")?;
        self.ensure_is_prop(ctx, cond, strategy, kernel_error::DERIVE_DITE_COND)?;
        self.ensure_has_ty_under(
            ctx,
            cond,
            then_br,
            ty,
            strategy,
            kernel_error::DERIVE_DITE_THEN_BR,
        )?;
        let ff = self.add(ctx, GNode::Empty);
        let not_cond = self.add(ctx, GNode::Eqn([cond, ff]));
        self.ensure_has_ty_under(
            ctx,
            not_cond,
            else_br,
            ty,
            strategy,
            kernel_error::DERIVE_DITE_ELSE_BR,
        )?;
        let tm = self.add(ctx, GNode::Ite([cond, then_br, else_br]));
        self.0.set_has_ty_unchecked(ctx, tm, ty);
        if self.is_inhab(ctx, cond) {
            let null = self.add(ctx, GNode::Null);
            let then_br_null = self.subst(ctx, null, then_br);
            self.0.set_eq_unchecked(ctx, tm, then_br_null);
        } else if self.is_empty(ctx, cond) {
            let null = self.add(ctx, GNode::Null);
            let else_br_null = self.subst(ctx, null, else_br);
            self.0.set_eq_unchecked(ctx, tm, else_br_null);
        }
        Ok(HasTyIn { tm, ty }.finish_rule(ctx, strategy))
    }

    fn derive_trunc<S>(&mut self, ctx: C, ty: T, strategy: &mut S) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_trunc")?;
        self.ensure_is_ty(ctx, ty, strategy, kernel_error::DERIVE_TRUNC_TY)?;
        let tm = self.add(ctx, GNode::Trunc([ty]));
        let prop = self.add(ctx, GNode::U(ULvl::PROP));
        self.0.set_has_ty_unchecked(ctx, tm, prop);
        if self.is_inhab(ctx, ty) {
            self.0.set_is_inhab_unchecked(ctx, tm);
        }
        if self.is_empty(ctx, ty) {
            self.0.set_is_empty_unchecked(ctx, tm);
        }
        Ok(HasTyIn { tm, ty: prop }.finish_rule(ctx, strategy))
    }

    fn derive_choose<S>(
        &mut self,
        ctx: C,
        ty: T,
        pred: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_choose")?;
        self.ensure_is_inhab(ctx, ty, strategy, kernel_error::DERIVE_CHOOSE_TY)?;
        let prop = self.add(ctx, GNode::U(ULvl::PROP));
        self.ensure_has_ty_under(
            ctx,
            ty,
            pred,
            prop,
            strategy,
            kernel_error::DERIVE_CHOOSE_PRED,
        )?;
        let tm = self.add(ctx, GNode::Choose([ty, pred]));
        self.0.set_has_ty_unchecked(ctx, tm, ty);
        Ok(HasTyIn { tm, ty }.finish_rule(ctx, strategy))
    }

    fn derive_nats<S>(&mut self, ctx: C, lvl: ULvl, strategy: &mut S) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_nats")?;
        if !self.u_le(ULvl::SET, lvl) {
            return Err(strategy.fail(kernel_error::DERIVE_NATS_SET_LE_LVL));
        }
        let tm = self.add(ctx, GNode::Nats);
        let ty = self.add(ctx, GNode::U(lvl));
        self.0.set_has_ty_unchecked(ctx, tm, ty);
        Ok(HasTyIn { tm, ty }.finish_rule(ctx, strategy))
    }

    fn derive_n64(&mut self, ctx: C, n: u64) -> HasTyIn<T> {
        let tm = self.add(ctx, GNode::N64(n));
        let ty = self.add(ctx, GNode::Nats);
        self.0.set_has_ty_unchecked(ctx, tm, ty);
        HasTyIn { tm, ty }
    }

    fn derive_succ<S>(&mut self, ctx: C, n: T, strategy: &mut S) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_succ")?;
        let nats = self.add(ctx, GNode::Nats);
        self.ensure_has_ty(ctx, n, nats, strategy, kernel_error::DERIVE_SUCC_N)?;
        let tm = self.add(ctx, GNode::Succ([n]));
        self.0.set_has_ty_unchecked(ctx, tm, nats);
        Ok(HasTyIn { tm, ty: nats }.finish_rule(ctx, strategy))
    }

    fn derive_natrec<S>(
        &mut self,
        ctx: C,
        mot: T,
        z: T,
        s: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_natrec")?;
        let nats = self.add(ctx, GNode::Nats);
        self.ensure_is_ty_under(ctx, nats, mot, strategy, kernel_error::DERIVE_NATREC_MOT)?;
        debug_assert!(
            self.bvi(ctx, mot) <= Bv(1),
            "a term which is well-typed under a binder cannot have a bvi greater than one"
        );
        let zero = self.add(ctx, GNode::N64(0));
        let mot_zero = self.subst(ctx, mot, zero);
        self.ensure_has_ty(ctx, z, mot_zero, strategy, kernel_error::DERIVE_NATREC_Z)?;
        let bv_one = self.add(ctx, GNode::Bv(Bv(1)));
        let succ_bv_one = self.add(ctx, GNode::Succ([bv_one]));
        debug_assert_eq!(self.bvi(ctx, succ_bv_one), Bv(2));
        let mot_succ_bv_one = self.subst(ctx, mot, succ_bv_one);
        debug_assert!(self.bvi(ctx, mot_succ_bv_one) <= Bv(2));
        let mot_to_mot_succ = self.add(ctx, GNode::Pi([mot, mot_succ_bv_one]));
        debug_assert!(self.bvi(ctx, mot_to_mot_succ) <= Bv(1));
        self.ensure_has_ty_under(
            ctx,
            nats,
            s,
            mot_to_mot_succ,
            strategy,
            kernel_error::DERIVE_NATREC_S,
        )?;

        let tm = self.add(ctx, GNode::Natrec([mot, z, s]));
        let ty = self.add(ctx, GNode::Pi([nats, mot]));
        self.0.set_has_ty_unchecked(ctx, tm, ty);
        Ok(HasTyIn { tm, ty: nats }.finish_rule(ctx, strategy))
    }

    fn derive_let<S>(
        &mut self,
        ctx: C,
        bound: T,
        bound_ty: T,
        body: T,
        body_ty: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_let")?;
        self.ensure_has_ty(
            ctx,
            bound,
            bound_ty,
            strategy,
            kernel_error::DERIVE_LET_BOUND,
        )?;
        self.ensure_has_ty_under(
            ctx,
            bound_ty,
            body,
            body_ty,
            strategy,
            kernel_error::DERIVE_LET_BODY,
        )?;
        let tm = self.add(ctx, GNode::Let(Bv(0), [bound, body]));
        let ty = self.subst(ctx, bound, body_ty);
        self.0.set_has_ty_unchecked(ctx, tm, ty);
        let tm_s = self.subst(ctx, bound, body);
        self.0.set_eq_unchecked(ctx, tm, tm_s);
        Ok(HasTyIn { tm, ty }.finish_rule(ctx, strategy))
    }

    fn derive_beta_abs<S>(
        &mut self,
        ctx: C,
        tm: T,
        arg: T,
        strategy: &mut S,
    ) -> Result<Eqn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_beta_abs")?;
        let &GNode::Abs([arg_ty, body]) = self.node(ctx, tm) else {
            return Err(strategy.fail("derive_beta_abs: tm ≡ abs A b"));
        };
        self.ensure_is_wf(ctx, tm, strategy, "derive_beta_abs: tm wf")?;
        self.ensure_has_ty(ctx, arg, arg_ty, strategy, "derive_beta_abs: arg")?;
        let tm_app = self.add(ctx, GNode::App([tm, arg]));
        let tm_subst = self.subst(ctx, arg, body);
        self.0.set_eq_unchecked(ctx, tm_app, tm_subst);
        Ok(Eqn {
            lhs: tm_app,
            rhs: tm_subst,
        }
        .finish_rule(ctx, strategy))
    }

    fn derive_beta_zero<S>(&mut self, ctx: C, tm: T, strategy: &mut S) -> Result<Eqn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_beta_zero")?;
        let &GNode::Natrec([_mot, z, _s]) = self.node(ctx, tm) else {
            return Err(strategy.fail("derive_beta_zero: tm ≡ natrec C z s"));
        };
        self.ensure_is_wf(ctx, tm, strategy, "derive_beta_zero: tm wf")?;
        let zero = self.add(ctx, GNode::N64(0));
        let tm_zero = self.add(ctx, GNode::App([tm, zero]));
        self.0.set_eq_unchecked(ctx, tm_zero, z);
        Ok(Eqn {
            lhs: tm_zero,
            rhs: zero,
        }
        .finish_rule(ctx, strategy))
    }

    fn derive_beta_succ<S>(
        &mut self,
        ctx: C,
        tm: T,
        n: T,
        strategy: &mut S,
    ) -> Result<Eqn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_beta_succ")?;
        let &GNode::Natrec([_mot, _z, s]) = self.node(ctx, tm) else {
            return Err(strategy.fail("derive_beta_zero: tm ≡ natrec C z s"));
        };
        self.ensure_is_wf(ctx, tm, strategy, "derive_beta_zero: tm wf")?;
        let nats = self.add(ctx, GNode::Nats);
        self.ensure_has_ty(ctx, n, nats, strategy, "derive_beta_succ: n")?;
        let tm_n = self.add(ctx, GNode::App([tm, n]));
        let s_n = self.subst(ctx, n, s);
        let s_n_tm_n = self.add(ctx, GNode::App([s_n, tm_n]));
        let succ_n = self.add(ctx, GNode::Succ([n]));
        let tm_succ_n = self.add(ctx, GNode::App([tm, succ_n]));
        self.0.set_eq_unchecked(ctx, tm_succ_n, s_n_tm_n);
        Ok(Eqn {
            lhs: tm_succ_n,
            rhs: s_n_tm_n,
        }
        .finish_rule(ctx, strategy))
    }

    fn derive_choose_spec<S>(
        &mut self,
        ctx: C,
        ty: T,
        pred: T,
        strategy: &mut S,
    ) -> Result<IsInhabIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_choose_spec")?;
        self.ensure_exists_inhab_under(ctx, ty, pred, strategy, "derive_choose_spec: exists")?;
        let choose = self.add(ctx, GNode::Choose([ty, pred]));
        let pred_choose = self.subst(ctx, choose, pred);
        self.0.set_has_ty_unchecked(ctx, choose, ty);
        self.0.set_is_prop_unchecked(ctx, pred_choose);
        self.0.set_is_inhab_unchecked(ctx, pred_choose);
        Ok(IsInhabIn(pred_choose).finish_rule(ctx, strategy))
    }

    fn derive_unit_ext<S>(&mut self, ctx: C, a: T, strategy: &mut S) -> Result<Eqn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_unit_ext")?;
        let unit = self.add(ctx, GNode::Unit);
        self.ensure_has_ty(ctx, a, unit, strategy, "derive_unit_ext: a")?;
        let null = self.add(ctx, GNode::Null);
        self.0.set_eq_unchecked(ctx, a, null);
        Ok(Eqn { lhs: a, rhs: null }.finish_rule(ctx, strategy))
    }

    fn derive_prop_ext_tt<S>(&mut self, ctx: C, a: T, strategy: &mut S) -> Result<Eqn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_prop_ext_tt")?;
        self.ensure_is_prop(ctx, a, strategy, "derive_prop_ext_tt: a prop")?;
        self.ensure_is_inhab(ctx, a, strategy, "derive_prop_ext_tt: a inhab")?;
        let unit = self.add(ctx, GNode::Unit);
        self.0.set_eq_unchecked(ctx, a, unit);
        Ok(Eqn { lhs: a, rhs: unit }.finish_rule(ctx, strategy))
    }

    fn derive_prop_ext_ff<S>(&mut self, ctx: C, a: T, strategy: &mut S) -> Result<Eqn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_prop_ext_ff")?;
        self.ensure_is_prop(ctx, a, strategy, "derive_prop_ext_ff: a prop")?;
        self.ensure_is_empty(ctx, a, strategy, "derive_prop_ext_ff: a empty")?;
        let empty = self.add(ctx, GNode::Empty);
        self.0.set_eq_unchecked(ctx, a, empty);
        Ok(Eqn { lhs: a, rhs: empty }.finish_rule(ctx, strategy))
    }

    fn derive_ext<S>(&mut self, ctx: C, lhs: T, rhs: T, strategy: &mut S) -> Result<Eqn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_ext")?;
        let eqn = self.add(ctx, GNode::Eqn([lhs, rhs]));
        self.ensure_is_inhab(ctx, eqn, strategy, "derive_ext: eqn inhab")?;
        self.0.set_eq_unchecked(ctx, lhs, rhs);
        Ok(Eqn { lhs, rhs }.finish_rule(ctx, strategy))
    }

    fn derive_pi_eta<S>(&mut self, ctx: C, ty: T, f: T, strategy: &mut S) -> Result<Eqn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_pi_eta")?;
        let &GNode::Pi([arg_ty, _res_ty]) = self.node(ctx, ty) else {
            return Err(strategy.fail("derive_pi_eta: ty ≡ pi A B"));
        };
        self.ensure_has_ty(ctx, f, ty, strategy, "derive_pi_eta: f")?;
        let bv_zero = self.add(ctx, GNode::Bv(Bv(0)));
        let app_f_bv_zero = self.add(ctx, GNode::App([f, bv_zero]));
        let eta = self.add(ctx, GNode::Abs([arg_ty, app_f_bv_zero]));
        self.0.set_eq_unchecked(ctx, f, eta);
        Ok(Eqn { lhs: f, rhs: eta }.finish_rule(ctx, strategy))
    }

    fn derive_sigma_eta<S>(
        &mut self,
        ctx: C,
        ty: T,
        p: T,
        strategy: &mut S,
    ) -> Result<Eqn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_sigma_eta")?;
        let &GNode::Sigma(_) = self.node(ctx, ty) else {
            return Err(strategy.fail("derive_sigma_eta: ty ≡ sigma A B"));
        };
        self.ensure_has_ty(ctx, p, ty, strategy, "derive_sigma_eta: p")?;
        let fst_p = self.add(ctx, GNode::Fst([p]));
        let snd_p = self.add(ctx, GNode::Snd([p]));
        let eta = self.add(ctx, GNode::Pair([fst_p, snd_p]));
        self.0.set_eq_unchecked(ctx, p, eta);
        Ok(Eqn { lhs: p, rhs: eta }.finish_rule(ctx, strategy))
    }
}

pub trait KernelAPI<C: Copy, T: Copy + PartialEq>:
    Derive<C, T> + Ensure<C, T> + TermStore<C, T> + ReadFacts<C, T>
{
}

impl<K, C: Copy, T: Copy + PartialEq> KernelAPI<C, T> for K where
    K: Derive<C, T> + Ensure<C, T> + TermStore<C, T> + ReadFacts<C, T>
{
}

/// Kernel error messages
pub mod kernel_error {
    /// Not implemented
    pub const NOT_IMPLEMENTED: &'static str = "covalence: not implemented";
    /// Strategy did not return a valid subcontext
    pub const ASSUME_NOT_SUBCTX: &'static str = "assume: not a subcontext of parent";
    /// Strategy changed assumptions in ensure_assumptions_valid_under
    pub const ENSURE_ASSUMPTIONS_VALID_UNDER_CHANGED: &'static str =
        "ensure_assumptions_valid_under: assumptions changed";
    /// An assumption must be a valid type
    pub const ASSUME_IS_TY: &'static str = "assume: ty is not a valid type";
    /// To add a variable, its type must be inhabited
    pub const ADD_VAR_IS_INHAB: &'static str = "add_var: ty is not inhabited";
    /// When we add a variable, it should be _well-scoped_: only contain variables from the current
    /// context
    ///
    /// Later, this restriction may be lifted slightly to allow _semi-well-scoped_ terms.
    pub const DERIVE_FV_ILL_SCOPED: &'static str = "derive_fv: var is ill-scoped";
    pub const DERIVE_CLOSE_HAS_TY_UNDER_ILL_SCOPED: &'static str =
        "derive_close_has_ty_under: variable's context is not a subcontext of the current context";
    pub const DERIVE_CLOSE_HAS_TY_UNDER_TOO_MANY_VARS: &'static str =
        "derive_close_has_ty_under: variable's context must define exactly one variable";
    pub const DERIVE_CLOSE_HAS_TY_UNDER_INVALID_ASSUMPTION: &'static str =
        "derive_close_has_ty_under: assumption is not valid";
    pub const DERIVE_CLOSE_HAS_TY_UNDER_HAS_TY: &'static str = "derive_close_has_ty_under: tm";
    pub const DERIVE_EQN_LHS: &'static str = "derive_eqn: lhs";
    pub const DERIVE_EQN_RHS: &'static str = "derive_eqn: rhs";
    pub const DERIVE_PI_IMAX_LE: &'static str =
        "derive_pi: cannot deduce that imax(arg_lvl, res_lvl) ≤ lvl";
    pub const DERIVE_PI_ARG_TY: &'static str = "derive_pi: arg_ty";
    pub const DERIVE_PI_RES_TY: &'static str = "derive_pi: res_ty";
    pub const DERIVE_SIGMA_ARG_LVL_LE: &'static str =
        "derive_sigma: cannot deduce that arg_lvl ≤ lvl";
    pub const DERIVE_SIGMA_RES_LVL_LE: &'static str =
        "derive_sigma: cannot deduce that res_lvl ≤ lvl";
    pub const DERIVE_SIGMA_ARG_TY: &'static str = "derive_sigma: arg_ty";
    pub const DERIVE_SIGMA_RES_TY: &'static str = "derive_sigma: res_ty";
    pub const DERIVE_ABS_BODY: &'static str = "derive_abs: body";
    pub const DERIVE_APP_ARG: &'static str = "derive_app: arg";
    pub const DERIVE_APP_FUNC: &'static str = "derive_app: func";
    pub const DERIVE_PAIR_RES_TY: &'static str = "derive_pair: res_ty";
    pub const DERIVE_PAIR_FST: &'static str = "derive_pair: fst";
    pub const DERIVE_PAIR_SND: &'static str = "derive_pair: snd";
    pub const DERIVE_FST_PAIR: &'static str = "derive_fst: pair";
    pub const DERIVE_SND_PAIR: &'static str = "derive_snd: pair";
    pub const DERIVE_DITE_COND: &'static str = "derive_dite: cond";
    pub const DERIVE_DITE_THEN_BR: &'static str = "derive_dite: then_br";
    pub const DERIVE_DITE_ELSE_BR: &'static str = "derive_dite: else_br";
    pub const DERIVE_TRUNC_TY: &'static str = "derive_trunc: ty";
    pub const DERIVE_CHOOSE_TY: &'static str = "derive_choose: ty";
    pub const DERIVE_CHOOSE_PRED: &'static str = "derive_choose: pred";
    pub const DERIVE_NATS_SET_LE_LVL: &'static str = "derive_nats: cannot deduce that SET ≤ lvl";
    pub const DERIVE_SUCC_N: &'static str = "derive_succ: n";
    pub const DERIVE_NATREC_MOT: &'static str = "derive_natrec: mot";
    pub const DERIVE_NATREC_Z: &'static str = "derive_natrec: z";
    pub const DERIVE_NATREC_S: &'static str = "derive_natrec: s";
    pub const DERIVE_LET_BOUND: &'static str = "derive_let: bound";
    pub const DERIVE_LET_BODY: &'static str = "derive_let: body";
    pub const DERIVE_BETA_ABS_TM_EQ_ABS: &'static str = "derive_beta_abs: tm ≡ abs A b";
    pub const DERIVE_BETA_ABS_TM_WF: &'static str = "derive_beta_abs: tm wf";
    pub const DERIVE_BETA_ABS_ARG: &'static str = "derive_beta_abs: arg";
    pub const DERIVE_BETA_ZERO_TM_EQ_NATREC: &'static str = "derive_beta_zero: tm ≡ natrec C z s";
    pub const DERIVE_BETA_ZERO_TM_WF: &'static str = "derive_beta_zero: tm wf";
    pub const DERIVE_BETA_SUCC_TM_EQ_NATREC: &'static str = "derive_beta_zero: tm ≡ natrec C z s";
    pub const DERIVE_BETA_SUCC_TM_WF: &'static str = "derive_beta_zero: tm wf";
    pub const DERIVE_BETA_SUCC_N: &'static str = "derive_beta_succ: n";
    pub const DERIVE_CHOOSE_SPEC_EXISTS: &'static str = "derive_choose_spec: exists";
    pub const DERIVE_UNIT_EXT_A: &'static str = "derive_unit_ext: a";
    pub const DERIVE_PROP_EXT_TT_PROP: &'static str = "derive_prop_ext_tt: a prop";
    pub const DERIVE_PROP_EXT_TT_INHAB: &'static str = "derive_prop_ext_tt: a inhab";
    pub const DERIVE_PROP_EXT_FF_PROP: &'static str = "derive_prop_ext_ff: a prop";
    pub const DERIVE_PROP_EXT_FF_EMPTY: &'static str = "derive_prop_ext_ff: a empty";
    pub const DERIVE_EXT_EQN_INHAB: &'static str = "derive_ext: eqn inhab";
    pub const DERIVE_PI_ETA_TY_EQ_PI: &'static str = "derive_pi_eta: ty ≡ pi A B";
    pub const DERIVE_PI_ETA_F: &'static str = "derive_pi_eta: f";
    pub const DERIVE_SIGMA_ETA_TY_EQ_SIGMA: &'static str = "derive_sigma_eta: ty ≡ sigma A B";
    pub const DERIVE_SIGMA_ETA_P: &'static str = "derive_sigma_eta: p";
}
