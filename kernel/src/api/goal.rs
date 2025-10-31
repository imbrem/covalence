use crate::api::derive::*;
use crate::api::store::*;

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

    /// Check this result
    pub fn check<C, K>(self, ctx: C, ker: &K) -> bool
    where
        K: ReadFacts<C, T>,
    {
        ker.has_ty(ctx, self.tm, self.ty)
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

    /// Check this result
    pub fn check<C, K>(self, ctx: C, ker: &K) -> bool
    where
        K: ReadFacts<C, T>,
    {
        ker.has_ty_under(ctx, self.binder, self.tm, self.ty)
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

    /// Check this result
    pub fn check<C, K>(self, ctx: C, ker: &K) -> bool
    where
        K: ReadFacts<C, T>,
    {
        ker.is_inhab(ctx, self.0)
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

    /// Check this result
    pub fn check<C, K>(self, ctx: C, ker: &K) -> bool
    where
        K: ReadFacts<C, T>,
    {
        ker.eq_in(ctx, self.lhs, self.rhs)
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

/// A context is a subcontext of another
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct IsSubctx<C> {
    pub lo: C,
    pub hi: C,
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
    /// A context is a subcontext of another
    IsSubctx(IsSubctx<C>),
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
            Goal::IsSubctx(g) => ker.is_subctx(g.lo, g.hi),
        }
    }
}
