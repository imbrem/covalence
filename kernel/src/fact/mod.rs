/*!
Facts which can be checked in the datastore
*/
use crate::api::store::*;
use crate::data::term::Val;

/// Logical composition for fact types
mod logic;

/// A fact which can be checked using a fact dataset
pub trait Fact<R: ?Sized> {
    /// Check whether this goal is true
    fn check(&self, db: &R) -> bool;
}

/// A fact about ("within") a given context
pub trait FactIn<C, R: ?Sized> {
    /// Check this fact in the given context
    fn check_in(&self, ctx: &C, db: &R) -> bool;
}

/// A quantified fact within a given context
pub trait FactUnder<C, Q, R: ?Sized> {
    /// Check this fact under the given quantifier in the given context
    fn check_under(&self, ctx: &C, binder: &Q, db: &R) -> bool;
}

/// A judgement about a given context, of the form `Γ ⊢ S`
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct Judgement<C, S> {
    /// The context for this judgement
    pub ctx: C,
    /// The statement asserted
    pub stmt: S,
}

impl<C, S, R: ?Sized> Fact<R> for Judgement<C, S>
where
    S: FactIn<C, R>,
{
    /// Check whether this judgement is true in the given context
    fn check(&self, db: &R) -> bool {
        self.stmt.check_in(&self.ctx, db)
    }
}

/// A quantified statement, of the form `Q . S`
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct Quantified<Q, S> {
    /// The quantifier for this statement
    pub binder: Q,
    /// The body of this statement
    pub body: S,
}

impl<C, Q, S, R: ?Sized> FactIn<C, R> for Quantified<Q, S>
where
    Q: FactIn<C, R>,
    S: FactUnder<C, Q, R>,
{
    /// Check this quantified statement in the given context
    fn check_in(&self, ctx: &C, db: &R) -> bool {
        self.body.check_under(ctx, &self.binder, db)
    }
}

/// A quantifier for a fact
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub enum Quant<T> {
    /// No quantifier
    Free,
    /// An existential quantifier
    Exists(T),
    /// A universal quantifier
    Forall(T),
}

impl<T> Quant<T> {
    /// Get the binder type of this quantifier
    pub fn binder(self) -> Option<T> {
        match self {
            Quant::Free => None,
            Quant::Exists(binder) | Quant::Forall(binder) => Some(binder),
        }
    }
}

pub type Goal<C, T> = Judgement<C, Quantified<Quant<T>, Option<GoalIn<T>>>>;

/// A judgement about terms
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub enum GoalIn<T> {
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
        Judgement {
            ctx,
            stmt: Quantified {
                binder: Quant::Free,
                body: None,
            },
        }
    }

    pub fn contr(ctx: C) -> Goal<C, T> {
        Judgement {
            ctx,
            stmt: Quantified {
                binder: Quant::Free,
                body: Some(GoalIn::Contr),
            },
        }
    }
}

/// An equation in a context
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct Eqn<C, T> {
    pub ctx: C,
    pub lhs: T,
    pub rhs: T,
}

pub type EqnV<C, T> = Eqn<C, Val<C, T>>;

/// A statement of well-formedness
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct IsWf<C, T> {
    pub ctx: C,
    pub tm: T,
}

pub type IsWfV<C, T> = IsWf<C, Val<C, T>>;

/// A term is a valid type
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct IsTy<C, T> {
    pub ctx: C,
    pub tm: T,
}

pub type IsTyV<C, T> = IsTy<C, Val<C, T>>;

/// A term is an inhabited type
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct IsInhab<C, T> {
    pub ctx: C,
    pub tm: T,
}

pub type IsInhabV<C, T> = IsInhab<C, Val<C, T>>;

/// A term is an empty type
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct IsEmpty<C, T> {
    pub ctx: C,
    pub tm: T,
}

pub type IsEmptyV<C, T> = IsEmpty<C, Val<C, T>>;

/// A term is a proposition
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct IsProp<C, T> {
    pub ctx: C,
    pub tm: T,
}

pub type IsPropV<C, T> = IsProp<C, Val<C, T>>;

/// A typing derivation
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct HasTy<C, T> {
    pub ctx: C,
    pub tm: T,
    pub ty: T,
}

pub type HasTyV<C, T> = HasTy<C, Val<C, T>>;

/// A term is a type under a binder
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct IsTyUnder<C, T> {
    pub ctx: C,
    pub binder: T,
    pub tm: T,
}

pub type IsTyUnderV<C, T> = IsTyUnder<C, Val<C, T>>;

/// A typing derivation under a binder
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct HasTyUnder<C, T> {
    pub ctx: C,
    pub binder: T,
    pub tm: T,
    pub ty: T,
}

pub type HasTyUnderV<C, T> = HasTyUnder<C, Val<C, T>>;

/// A universally quantified statement of inhabitance
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct ForallInhabUnder<C, T> {
    pub ctx: C,
    pub binder: T,
    pub ty: T,
}

pub type ForallInhabUnderV<C, T> = ForallInhabUnder<C, Val<C, T>>;

/// An existentially quantified statement of inhabitance
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct ExistsInhabUnder<C, T> {
    pub ctx: C,
    pub binder: T,
    pub ty: T,
}

pub type ExistsInhabUnderV<C, T> = ExistsInhabUnder<C, Val<C, T>>;

/// A context is a subcontext of another
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct IsSubctx<C> {
    pub lo: C,
    pub hi: C,
}

impl<C, T> From<Eqn<C, T>> for Goal<C, T> {
    fn from(g: Eqn<C, T>) -> Self {
        Judgement {
            ctx: g.ctx,
            stmt: Quantified {
                binder: Quant::Free,
                body: Some(GoalIn::Eq(g.lhs, g.rhs)),
            },
            // binder: Quant::Null,
            // rel: Some(GoalIn::Eq(g.lhs, g.rhs)),
        }
    }
}

impl<C, T> From<IsWf<C, T>> for Goal<C, T>
where
    C: Copy,
    T: Copy,
{
    fn from(g: IsWf<C, T>) -> Self {
        Judgement {
            ctx: g.ctx,
            stmt: Quantified {
                binder: Quant::Free,
                body: Some(GoalIn::IsWf(g.tm)),
            },
            // binder: Quant::Null,
            // rel: Some(GoalIn::IsWf(g.tm)),
        }
    }
}

impl<C, T> From<IsTy<C, T>> for Goal<C, T> {
    fn from(g: IsTy<C, T>) -> Self {
        Judgement {
            ctx: g.ctx,
            stmt: Quantified {
                binder: Quant::Free,
                body: Some(GoalIn::IsTy(g.tm)),
            },
            // binder: Quant::Null,
            // rel: Some(GoalIn::IsTy(g.tm)),
        }
    }
}

impl<C, T> From<IsInhab<C, T>> for Goal<C, T> {
    fn from(g: IsInhab<C, T>) -> Self {
        Judgement {
            ctx: g.ctx,
            stmt: Quantified {
                binder: Quant::Free,
                body: Some(GoalIn::IsInhab(g.tm)),
            },
            // binder: Quant::Null,
            // rel: Some(GoalIn::IsInhab(g.tm)),
        }
    }
}

impl<C, T> From<IsEmpty<C, T>> for Goal<C, T> {
    fn from(g: IsEmpty<C, T>) -> Self {
        Judgement {
            ctx: g.ctx,
            stmt: Quantified {
                binder: Quant::Forall(g.tm),
                body: Some(GoalIn::Contr),
            },
        }
    }
}

impl<C, T> From<IsProp<C, T>> for Goal<C, T> {
    fn from(g: IsProp<C, T>) -> Self {
        Goal {
            ctx: g.ctx,
            stmt: Quantified {
                binder: Quant::Free,
                body: Some(GoalIn::IsProp(g.tm)),
            },
        }
    }
}

impl<C, T> From<HasTy<C, T>> for Goal<C, T> {
    fn from(g: HasTy<C, T>) -> Self {
        Goal {
            ctx: g.ctx,
            stmt: Quantified {
                binder: Quant::Free,
                body: Some(GoalIn::HasTy(g.tm, g.ty)),
            },
        }
    }
}

impl<C, T> From<IsTyUnder<C, T>> for Goal<C, T> {
    fn from(g: IsTyUnder<C, T>) -> Self {
        Goal {
            ctx: g.ctx,
            stmt: Quantified {
                binder: Quant::Forall(g.binder),
                body: Some(GoalIn::IsTy(g.tm)),
            },
            // binder: Quant::Forall(g.binder),
            // rel: Some(GoalIn::IsTy(g.tm)),
        }
    }
}

impl<C, T> From<HasTyUnder<C, T>> for Goal<C, T> {
    fn from(g: HasTyUnder<C, T>) -> Self {
        Judgement {
            ctx: g.ctx,
            stmt: Quantified {
                binder: Quant::Forall(g.binder),
                body: Some(GoalIn::HasTy(g.tm, g.ty)),
            },
            // binder: Quant::Forall(g.binder),
            // rel: Some(GoalIn::HasTy(g.tm, g.ty)),
        }
    }
}

impl<C, T> From<ForallInhabUnder<C, T>> for Goal<C, T> {
    fn from(g: ForallInhabUnder<C, T>) -> Self {
        Judgement {
            ctx: g.ctx,
            stmt: Quantified {
                binder: Quant::Forall(g.binder),
                body: Some(GoalIn::IsInhab(g.ty)),
            },
            // binder: Quant::Forall(g.binder),
            // rel: Some(GoalIn::IsInhab(g.ty)),
        }
    }
}

impl<C, T> From<ExistsInhabUnder<C, T>> for Goal<C, T> {
    fn from(g: ExistsInhabUnder<C, T>) -> Self {
        Judgement {
            ctx: g.ctx,
            stmt: Quantified {
                binder: Quant::Exists(g.binder),
                body: Some(GoalIn::IsInhab(g.ty)),
            },
            // binder: Quant::Exists(g.binder),
            // rel: Some(GoalIn::IsInhab(g.ty)),
        }
    }
}

impl<T: Copy> Quant<T> {
    /// Check this quantifier in the given context
    pub fn check_in<C: Copy, R: ReadTermFacts<C, T> + ?Sized>(self, ctx: C, ker: &R) -> bool {
        if let Some(binder) = self.binder() {
            ker.is_ty(ctx, binder)
        } else {
            true
        }
    }
}

impl<C, T, R> FactIn<C, R> for Quant<T>
where
    C: Copy,
    T: Copy,
    R: ReadFacts<C, T> + ?Sized,
{
    /// Check this quantifier in the given context
    fn check_in(&self, &ctx: &C, ker: &R) -> bool {
        match self {
            Quant::Free => true,
            Quant::Exists(binder) | Quant::Forall(binder) => ker.is_ty(ctx, *binder),
        }
    }
}

impl<C, T, R> FactUnder<C, Quant<T>, R> for GoalIn<T>
where
    C: Copy,
    T: Copy,
    R: ReadFacts<C, T> + ?Sized,
{
    /// Check whether this goal is true
    fn check_under(&self, &ctx: &C, &binder: &Quant<T>, ker: &R) -> bool {
        match (binder, *self) {
            (Quant::Free, GoalIn::Eq(lhs, rhs)) => ker.eq_in(ctx, lhs, rhs),
            (Quant::Free, GoalIn::IsWf(tm)) => ker.is_wf(ctx, tm),
            (Quant::Free, GoalIn::IsTy(tm)) => ker.is_wf(ctx, tm),
            (Quant::Free, GoalIn::IsProp(tm)) => ker.is_prop(ctx, tm),
            (Quant::Free, GoalIn::HasTy(tm, ty)) => ker.has_ty(ctx, tm, ty),
            (Quant::Free, GoalIn::IsInhab(tm)) => ker.is_inhab(ctx, tm),
            (Quant::Free, GoalIn::IsEmpty(tm)) => ker.is_empty(ctx, tm),
            (Quant::Free, GoalIn::Contr) => ker.is_contr(ctx),
            (Quant::Forall(binder), GoalIn::Eq(lhs, rhs)) => {
                ker.forall_eq_in(ctx, binder, lhs, rhs)
            }
            (Quant::Forall(binder), GoalIn::IsWf(tm)) => ker.forall_is_wf(ctx, binder, tm),
            (Quant::Forall(binder), GoalIn::IsTy(tm)) => ker.forall_is_ty(ctx, binder, tm),
            (Quant::Forall(binder), GoalIn::IsProp(tm)) => ker.forall_is_prop(ctx, binder, tm),
            (Quant::Forall(binder), GoalIn::HasTy(tm, ty)) => {
                ker.forall_has_ty(ctx, binder, tm, ty)
            }
            (Quant::Forall(binder), GoalIn::IsInhab(tm)) => ker.forall_is_inhab(ctx, binder, tm),
            (Quant::Forall(binder), GoalIn::IsEmpty(tm)) => ker.forall_is_empty(ctx, binder, tm),
            (Quant::Forall(binder), GoalIn::Contr) => ker.is_empty(ctx, binder),
            (Quant::Exists(binder), GoalIn::Eq(lhs, rhs)) => {
                ker.exists_eq_in(ctx, binder, lhs, rhs)
            }
            (Quant::Exists(binder), GoalIn::IsWf(tm)) => ker.exists_is_wf(ctx, binder, tm),
            (Quant::Exists(binder), GoalIn::IsTy(tm)) => ker.exists_is_ty(ctx, binder, tm),
            (Quant::Exists(binder), GoalIn::IsProp(tm)) => ker.exists_is_prop(ctx, binder, tm),
            (Quant::Exists(binder), GoalIn::HasTy(tm, ty)) => {
                ker.exists_has_ty(ctx, binder, tm, ty)
            }
            (Quant::Exists(binder), GoalIn::IsInhab(tm)) => ker.exists_is_inhab(ctx, binder, tm),
            (Quant::Exists(binder), GoalIn::IsEmpty(tm)) => ker.exists_is_empty(ctx, binder, tm),
            (Quant::Exists(_), GoalIn::Contr) => ker.is_contr(ctx),
        }
    }
}
