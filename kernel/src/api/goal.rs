use crate::api::store::*;
use crate::data::term::Val;

/// A fact in a given context
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct Fact<C, T> {
    /// The context for this goal
    pub ctx: C,
    /// The binder for this goal, if any
    pub binder: Option<Quant<T>>,
    /// The relation
    pub rel: Option<FactIn<T>>,
}

/// A fact about terms
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub enum FactIn<T> {
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

impl<C, T> Fact<C, T> {
    pub fn ok(ctx: C) -> Fact<C, T> {
        Fact {
            ctx,
            binder: None,
            rel: None,
        }
    }

    pub fn contr(ctx: C) -> Fact<C, T> {
        Fact {
            ctx,
            binder: None,
            rel: Some(FactIn::Contr),
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

impl<C, T> From<Eqn<C, T>> for Fact<C, T> {
    fn from(g: Eqn<C, T>) -> Self {
        Fact {
            ctx: g.ctx,
            binder: None,
            rel: Some(FactIn::Eq(g.lhs, g.rhs)),
        }
    }
}

impl<C, T> From<IsWf<C, T>> for Fact<C, T>
where
    C: Copy,
    T: Copy,
{
    fn from(g: IsWf<C, T>) -> Self {
        Fact {
            ctx: g.ctx,
            binder: None,
            rel: Some(FactIn::IsWf(g.tm)),
        }
    }
}

impl<C, T> From<IsTy<C, T>> for Fact<C, T> {
    fn from(g: IsTy<C, T>) -> Self {
        Fact {
            ctx: g.ctx,
            binder: None,
            rel: Some(FactIn::IsTy(g.tm)),
        }
    }
}

impl<C, T> From<IsInhab<C, T>> for Fact<C, T> {
    fn from(g: IsInhab<C, T>) -> Self {
        Fact {
            ctx: g.ctx,
            binder: None,
            rel: Some(FactIn::IsInhab(g.tm)),
        }
    }
}

impl<C, T> From<IsEmpty<C, T>> for Fact<C, T> {
    fn from(g: IsEmpty<C, T>) -> Self {
        Fact {
            ctx: g.ctx,
            binder: Some(Quant::Forall(g.tm)),
            rel: Some(FactIn::Contr),
        }
    }
}

impl<C, T> From<IsProp<C, T>> for Fact<C, T> {
    fn from(g: IsProp<C, T>) -> Self {
        Fact {
            ctx: g.ctx,
            binder: None,
            rel: Some(FactIn::IsProp(g.tm)),
        }
    }
}

impl<C, T> From<HasTy<C, T>> for Fact<C, T> {
    fn from(g: HasTy<C, T>) -> Self {
        Fact {
            ctx: g.ctx,
            binder: None,
            rel: Some(FactIn::HasTy(g.tm, g.ty)),
        }
    }
}

impl<C, T> From<IsTyUnder<C, T>> for Fact<C, T> {
    fn from(g: IsTyUnder<C, T>) -> Self {
        Fact {
            ctx: g.ctx,
            binder: Some(Quant::Forall(g.binder)),
            rel: Some(FactIn::IsTy(g.tm)),
        }
    }
}

impl<C, T> From<HasTyUnder<C, T>> for Fact<C, T> {
    fn from(g: HasTyUnder<C, T>) -> Self {
        Fact {
            ctx: g.ctx,
            binder: Some(Quant::Forall(g.binder)),
            rel: Some(FactIn::HasTy(g.tm, g.ty)),
        }
    }
}

impl<C, T> From<ForallInhabUnder<C, T>> for Fact<C, T> {
    fn from(g: ForallInhabUnder<C, T>) -> Self {
        Fact {
            ctx: g.ctx,
            binder: Some(Quant::Forall(g.binder)),
            rel: Some(FactIn::IsInhab(g.ty)),
        }
    }
}

impl<C, T> From<ExistsInhabUnder<C, T>> for Fact<C, T> {
    fn from(g: ExistsInhabUnder<C, T>) -> Self {
        Fact {
            ctx: g.ctx,
            binder: Some(Quant::Exists(g.binder)),
            rel: Some(FactIn::IsInhab(g.ty)),
        }
    }
}

impl<T: Copy> Quant<T> {
    /// Check this quantifier in the given context
    pub fn check_in<C: Copy, R: ReadFacts<C, T> + ?Sized>(self, ctx: C, ker: &R) -> bool {
        ker.is_ty(ctx, self.binder())
    }
}

impl<C: Copy, T: Copy> Fact<C, T> {
    /// Check this relation's binder
    pub fn check_binder_in<R: ReadFacts<C, T> + ?Sized>(self, ker: &R) -> bool {
        self.binder
            .is_none_or(|binder| binder.check_in(self.ctx, ker))
    }

    /// Check whether this goal is true
    pub fn check_in<R: ReadFacts<C, T> + ?Sized>(self, ker: &R) -> bool {
        match (self.binder, self.rel) {
            (_, None) => self.check_binder_in(ker),
            (None, Some(FactIn::Eq(lhs, rhs))) => ker.eq_in(self.ctx, lhs, rhs),
            (None, Some(FactIn::IsWf(tm))) => ker.is_wf(self.ctx, tm),
            (None, Some(FactIn::IsTy(tm))) => ker.is_wf(self.ctx, tm),
            (None, Some(FactIn::IsProp(tm))) => ker.is_prop(self.ctx, tm),
            (None, Some(FactIn::HasTy(tm, ty))) => ker.has_ty(self.ctx, tm, ty),
            (None, Some(FactIn::IsInhab(tm))) => ker.is_inhab(self.ctx, tm),
            (None, Some(FactIn::IsEmpty(tm))) => ker.is_empty(self.ctx, tm),
            (None, Some(FactIn::Contr)) => ker.is_contr(self.ctx),
            (Some(Quant::Forall(binder)), Some(FactIn::Eq(lhs, rhs))) => {
                ker.forall_eq_in(self.ctx, binder, lhs, rhs)
            }
            (Some(Quant::Forall(binder)), Some(FactIn::IsWf(tm))) => {
                ker.forall_is_wf(self.ctx, binder, tm)
            }
            (Some(Quant::Forall(binder)), Some(FactIn::IsTy(tm))) => {
                ker.forall_is_wf(self.ctx, binder, tm)
            }
            (Some(Quant::Forall(binder)), Some(FactIn::IsProp(tm))) => {
                ker.forall_is_prop(self.ctx, binder, tm)
            }
            (Some(Quant::Forall(binder)), Some(FactIn::HasTy(tm, ty))) => {
                ker.forall_has_ty(self.ctx, binder, tm, ty)
            }
            (Some(Quant::Forall(binder)), Some(FactIn::IsInhab(tm))) => {
                ker.forall_is_inhab(self.ctx, binder, tm)
            }
            (Some(Quant::Forall(binder)), Some(FactIn::IsEmpty(tm))) => {
                ker.forall_is_empty(self.ctx, binder, tm)
            }
            (Some(Quant::Forall(binder)), Some(FactIn::Contr)) => ker.is_empty(self.ctx, binder),
            (Some(Quant::Exists(binder)), Some(FactIn::Eq(lhs, rhs))) => {
                ker.exists_eq_in(self.ctx, binder, lhs, rhs)
            }
            (Some(Quant::Exists(binder)), Some(FactIn::IsWf(tm))) => {
                ker.exists_is_wf(self.ctx, binder, tm)
            }
            (Some(Quant::Exists(binder)), Some(FactIn::IsTy(tm))) => {
                ker.exists_is_ty(self.ctx, binder, tm)
            }
            (Some(Quant::Exists(binder)), Some(FactIn::IsProp(tm))) => {
                ker.exists_is_prop(self.ctx, binder, tm)
            }
            (Some(Quant::Exists(binder)), Some(FactIn::HasTy(tm, ty))) => {
                ker.exists_has_ty(self.ctx, binder, tm, ty)
            }
            (Some(Quant::Exists(binder)), Some(FactIn::IsInhab(tm))) => {
                ker.exists_is_inhab(self.ctx, binder, tm)
            }
            (Some(Quant::Exists(binder)), Some(FactIn::IsEmpty(tm))) => {
                ker.exists_is_empty(self.ctx, binder, tm)
            }
            (Some(Quant::Exists(_)), Some(FactIn::Contr)) => ker.is_contr(self.ctx),
        }
    }
}

impl<C: Copy, T: Copy> Quant<Val<C, T>> {
    /// Attempt to lookup this quantifier in the given context
    pub fn lookup<R: ReadTerm<C, T> + ?Sized>(self, ctx: C, ker: &R) -> Option<Quant<T>> {
        match self {
            Quant::Forall(binder) => Some(Quant::Forall(ker.lookup_val(ctx, binder)?)),
            Quant::Exists(binder) => Some(Quant::Exists(ker.lookup_val(ctx, binder)?)),
        }
    }
}

impl<C: Copy, T: Copy> Fact<C, Val<C, T>> {
    /// Attempt to convert this goal to one in it's context
    pub fn lookup<R: ReadTermStore<C, T> + ?Sized>(self, ker: &R) -> Option<Fact<C, T>> {
        let binder = if let Some(binder) = self.binder {
            Some(binder.lookup(self.ctx, ker)?)
        } else {
            None
        };
        let rel = match self.rel {
            None => None,
            Some(FactIn::Eq(lhs, rhs)) => {
                if ker.deref_eq(lhs, rhs) {
                    None
                } else {
                    Some(FactIn::Eq(
                        ker.lookup_val(self.ctx, lhs)?,
                        ker.lookup_val(self.ctx, rhs)?,
                    ))
                }
            }
            Some(FactIn::IsWf(tm)) => Some(FactIn::IsWf(ker.lookup_val(self.ctx, tm)?)),
            Some(FactIn::IsTy(tm)) => Some(FactIn::IsTy(ker.lookup_val(self.ctx, tm)?)),
            Some(FactIn::IsProp(tm)) => Some(FactIn::IsProp(ker.lookup_val(self.ctx, tm)?)),
            Some(FactIn::HasTy(tm, ty)) => Some(FactIn::HasTy(
                ker.lookup_val(self.ctx, tm)?,
                ker.lookup_val(self.ctx, ty)?,
            )),
            Some(FactIn::IsInhab(tm)) => Some(FactIn::IsInhab(ker.lookup_val(self.ctx, tm)?)),
            Some(FactIn::IsEmpty(tm)) => Some(FactIn::IsEmpty(ker.lookup_val(self.ctx, tm)?)),
            Some(FactIn::Contr) => Some(FactIn::Contr),
        };
        Some(Fact {
            ctx: self.ctx,
            binder,
            rel,
        })
    }

    /// Check whether this goal is true
    pub fn check<R: ReadTermStore<C, T> + ?Sized>(self, ker: &R) -> bool {
        self.lookup(ker).is_some_and(|goal| goal.check_in(ker))
    }
}
