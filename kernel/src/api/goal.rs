use crate::api::derive::*;
use crate::api::store::*;

/// A goal for a strategy
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct Goal<C, T> {
    /// The context for this goal
    pub ctx: C,
    /// The binder for this goal, if any
    pub binder: Option<Quant<T>>,
    /// The relation
    pub rel: Option<GoalRel<T>>,
}

/// A goal in a given context
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub enum GoalRel<T> {
    /// Two terms are equal
    Eq(T, T),
    /// A term is well-formed
    IsWf(T),
    /// A term is a type
    IsTy(T),
    /// A term is a proposition
    IsProp(T),
    /// A term has a type
    HasTy(T, T),
    /// A term is inhabited
    IsInhab(T),
    /// A term is empty
    IsEmpty(T),
    /// A context is a contradiction
    Contr,
}

impl<C, T> Goal<C, T> {
    pub fn ok(ctx: C) -> Goal<C, T> {
        Goal {
            ctx,
            binder: None,
            rel: None,
        }
    }

    pub fn contr(ctx: C) -> Goal<C, T> {
        Goal {
            ctx,
            binder: None,
            rel: Some(GoalRel::Contr),
        }
    }
}

/// A typing derivation in a given context
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct HasTyIn<T> {
    pub tm: T,
    pub ty: T,
}

impl<T> HasTyIn<T> {
    /// Convert to a goal
    pub fn goal<C>(self, ctx: C) -> Goal<C, T> {
        HasTy {
            ctx,
            tm: self.tm,
            ty: self.ty,
        }
        .into()
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
        HasTyUnder {
            ctx,
            binder: self.binder,
            tm: self.tm,
            ty: self.ty,
        }
        .into()
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
        ker.forall_has_ty(ctx, self.binder, self.tm, self.ty)
    }
}

/// A term is an inhabited type
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct IsInhabIn<T>(pub T);

impl<T> IsInhabIn<T> {
    /// Convert to a goal
    pub fn goal<C>(self, ctx: C) -> Goal<C, T> {
        IsInhab { ctx, tm: self.0 }.into()
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
        EqIn {
            ctx,
            lhs: self.lhs,
            rhs: self.rhs,
        }
        .into()
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

impl<C, T> From<IsWf<C, T>> for Goal<C, T>
where
    C: Copy,
    T: Copy,
{
    fn from(g: IsWf<C, T>) -> Self {
        Goal {
            ctx: g.ctx,
            binder: None,
            rel: Some(GoalRel::IsWf(g.tm)),
        }
    }
}

impl<C, T> From<IsTy<C, T>> for Goal<C, T> {
    fn from(g: IsTy<C, T>) -> Self {
        Goal {
            ctx: g.ctx,
            binder: None,
            rel: Some(GoalRel::IsTy(g.tm)),
        }
    }
}

impl<C, T> From<IsInhab<C, T>> for Goal<C, T> {
    fn from(g: IsInhab<C, T>) -> Self {
        Goal {
            ctx: g.ctx,
            binder: None,
            rel: Some(GoalRel::IsInhab(g.tm)),
        }
    }
}

impl<C, T> From<IsEmpty<C, T>> for Goal<C, T> {
    fn from(g: IsEmpty<C, T>) -> Self {
        Goal {
            ctx: g.ctx,
            binder: Some(Quant::Forall(g.tm)),
            rel: Some(GoalRel::Contr),
        }
    }
}

impl<C, T> From<IsProp<C, T>> for Goal<C, T> {
    fn from(g: IsProp<C, T>) -> Self {
        Goal {
            ctx: g.ctx,
            binder: None,
            rel: Some(GoalRel::IsProp(g.tm)),
        }
    }
}

impl<C, T> From<HasTy<C, T>> for Goal<C, T> {
    fn from(g: HasTy<C, T>) -> Self {
        Goal {
            ctx: g.ctx,
            binder: None,
            rel: Some(GoalRel::HasTy(g.tm, g.ty)),
        }
    }
}

impl<C, T> From<IsTyUnder<C, T>> for Goal<C, T> {
    fn from(g: IsTyUnder<C, T>) -> Self {
        Goal {
            ctx: g.ctx,
            binder: Some(Quant::Forall(g.binder)),
            rel: Some(GoalRel::IsTy(g.tm)),
        }
    }
}

impl<C, T> From<HasTyUnder<C, T>> for Goal<C, T> {
    fn from(g: HasTyUnder<C, T>) -> Self {
        Goal {
            ctx: g.ctx,
            binder: Some(Quant::Forall(g.binder)),
            rel: Some(GoalRel::HasTy(g.tm, g.ty)),
        }
    }
}

impl<C, T> From<ForallInhabUnder<C, T>> for Goal<C, T> {
    fn from(g: ForallInhabUnder<C, T>) -> Self {
        Goal {
            ctx: g.ctx,
            binder: Some(Quant::Forall(g.binder)),
            rel: Some(GoalRel::IsInhab(g.ty)),
        }
    }
}

impl<C, T> From<ExistsInhabUnder<C, T>> for Goal<C, T> {
    fn from(g: ExistsInhabUnder<C, T>) -> Self {
        Goal {
            ctx: g.ctx,
            binder: Some(Quant::Exists(g.binder)),
            rel: Some(GoalRel::IsInhab(g.ty)),
        }
    }
}

impl<C, T> From<EqIn<C, T>> for Goal<C, T> {
    fn from(g: EqIn<C, T>) -> Self {
        Goal {
            ctx: g.ctx,
            binder: None,
            rel: Some(GoalRel::Eq(g.lhs, g.rhs)),
        }
    }
}

impl<T: Copy> Quant<T> {
    /// Check this quantifier in the given context
    pub fn check_in<C: Copy, R: ReadTermFacts<C, T> + ?Sized>(self, ctx: C, ker: &R) -> bool {
        ker.is_ty(ctx, self.binder())
    }
}

impl<C: Copy, T: Copy> Goal<C, T> {
    /// Check this relation's binder
    pub fn check_binder_in<R: ReadTermFacts<C, T> + ?Sized>(self, ker: &R) -> bool {
        self.binder
            .is_none_or(|binder| binder.check_in(self.ctx, ker))
    }

    /// Check whether this goal is true
    pub fn check_in<R: ReadFacts<C, T> + ?Sized>(self, ker: &R) -> bool {
        match (self.binder, self.rel) {
            (_, None) => self.check_binder_in(ker),
            (None, Some(GoalRel::Eq(lhs, rhs))) => ker.eq_in(self.ctx, lhs, rhs),
            (None, Some(GoalRel::IsWf(tm))) => ker.is_wf(self.ctx, tm),
            (None, Some(GoalRel::IsTy(tm))) => ker.is_wf(self.ctx, tm),
            (None, Some(GoalRel::IsProp(tm))) => ker.is_prop(self.ctx, tm),
            (None, Some(GoalRel::HasTy(tm, ty))) => ker.has_ty(self.ctx, tm, ty),
            (None, Some(GoalRel::IsInhab(tm))) => ker.is_inhab(self.ctx, tm),
            (None, Some(GoalRel::IsEmpty(tm))) => ker.is_empty(self.ctx, tm),
            (None, Some(GoalRel::Contr)) => ker.is_contr(self.ctx),
            (Some(Quant::Forall(binder)), Some(GoalRel::Eq(lhs, rhs))) => {
                ker.forall_eq_in(self.ctx, binder, lhs, rhs)
            }
            (Some(Quant::Forall(binder)), Some(GoalRel::IsWf(tm))) => {
                ker.forall_is_wf(self.ctx, binder, tm)
            }
            (Some(Quant::Forall(binder)), Some(GoalRel::IsTy(tm))) => {
                ker.forall_is_wf(self.ctx, binder, tm)
            }
            (Some(Quant::Forall(binder)), Some(GoalRel::IsProp(tm))) => {
                ker.forall_is_prop(self.ctx, binder, tm)
            }
            (Some(Quant::Forall(binder)), Some(GoalRel::HasTy(tm, ty))) => {
                ker.forall_has_ty(self.ctx, binder, tm, ty)
            }
            (Some(Quant::Forall(binder)), Some(GoalRel::IsInhab(tm))) => {
                ker.forall_is_inhab(self.ctx, binder, tm)
            }
            (Some(Quant::Forall(binder)), Some(GoalRel::IsEmpty(tm))) => {
                ker.forall_is_empty(self.ctx, binder, tm)
            }
            (Some(Quant::Forall(binder)), Some(GoalRel::Contr)) => ker.is_empty(self.ctx, binder),
            (Some(Quant::Exists(binder)), Some(GoalRel::Eq(lhs, rhs))) => {
                ker.exists_eq_in(self.ctx, binder, lhs, rhs)
            }
            (Some(Quant::Exists(binder)), Some(GoalRel::IsWf(tm))) => {
                ker.exists_is_wf(self.ctx, binder, tm)
            }
            (Some(Quant::Exists(binder)), Some(GoalRel::IsTy(tm))) => {
                ker.exists_is_ty(self.ctx, binder, tm)
            }
            (Some(Quant::Exists(binder)), Some(GoalRel::IsProp(tm))) => {
                ker.exists_is_prop(self.ctx, binder, tm)
            }
            (Some(Quant::Exists(binder)), Some(GoalRel::HasTy(tm, ty))) => {
                ker.exists_has_ty(self.ctx, binder, tm, ty)
            }
            (Some(Quant::Exists(binder)), Some(GoalRel::IsInhab(tm))) => {
                ker.exists_is_inhab(self.ctx, binder, tm)
            }
            (Some(Quant::Exists(binder)), Some(GoalRel::IsEmpty(tm))) => {
                ker.exists_is_empty(self.ctx, binder, tm)
            }
            (_, Some(GoalRel::Contr)) => ker.is_contr(self.ctx),
        }
    }
}
