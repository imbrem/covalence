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

/// A _sequent_: a pair `Γ ⊢ S` of a context and a statement
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct Seq<C, S> {
    /// The context for this sequent
    pub ctx: C,
    /// The statement asserted
    pub stmt: S,
}

impl<C, S, R: ?Sized> Fact<R> for Seq<C, S>
where
    S: FactIn<C, R>,
{
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

/// An atomic formula on terms supported by the kernel
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub enum Atom<T> {
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

/// A universal quantifier
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct Forall<T>(T);

/// A quantified atomic formula
pub type QAtom<T> = Quantified<Option<Forall<T>>, Atom<T>>;

/// An atomic sequent
pub type AtomSeq<C, T> = Seq<C, Atom<T>>;

/// A quantified atomic sequent
pub type QAtomSeq<C, T> = Seq<C, QAtom<T>>;

impl<C, T> QAtomSeq<C, T> {
    pub fn contr(ctx: C) -> QAtomSeq<C, T> {
        Seq {
            ctx,
            stmt: Quantified {
                binder: None,
                body: Atom::Contr,
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

impl<C, T> From<Eqn<C, T>> for QAtomSeq<C, T> {
    fn from(g: Eqn<C, T>) -> Self {
        Seq {
            ctx: g.ctx,
            stmt: Quantified {
                binder: None,
                body: Atom::Eq(g.lhs, g.rhs),
            },
            // binder: Quant::Null,
            // rel: Some(GoalIn::Eq(g.lhs, g.rhs)),
        }
    }
}

impl<C, T> From<IsWf<C, T>> for QAtomSeq<C, T>
where
    C: Copy,
    T: Copy,
{
    fn from(g: IsWf<C, T>) -> Self {
        Seq {
            ctx: g.ctx,
            stmt: Quantified {
                binder: None,
                body: Atom::IsWf(g.tm),
            },
            // binder: Quant::Null,
            // rel: Some(GoalIn::IsWf(g.tm)),
        }
    }
}

impl<C, T> From<IsTy<C, T>> for QAtomSeq<C, T> {
    fn from(g: IsTy<C, T>) -> Self {
        Seq {
            ctx: g.ctx,
            stmt: Quantified {
                binder: None,
                body: Atom::IsTy(g.tm),
            },
            // binder: Quant::Null,
            // rel: Some(GoalIn::IsTy(g.tm)),
        }
    }
}

impl<C, T> From<IsInhab<C, T>> for QAtomSeq<C, T> {
    fn from(g: IsInhab<C, T>) -> Self {
        Seq {
            ctx: g.ctx,
            stmt: Quantified {
                binder: None,
                body: Atom::IsInhab(g.tm),
            },
            // binder: Quant::Null,
            // rel: Some(GoalIn::IsInhab(g.tm)),
        }
    }
}

impl<C, T> From<IsEmpty<C, T>> for QAtomSeq<C, T> {
    fn from(g: IsEmpty<C, T>) -> Self {
        Seq {
            ctx: g.ctx,
            stmt: Quantified {
                binder: None,
                body: Atom::IsEmpty(g.tm),
            },
        }
    }
}

impl<C, T: Copy> From<IsProp<C, T>> for QAtomSeq<C, T> {
    fn from(g: IsProp<C, T>) -> Self {
        QAtomSeq {
            ctx: g.ctx,
            stmt: Quantified {
                binder: None,
                body: Atom::IsProp(g.tm),
            },
        }
    }
}

impl<C, T> From<HasTy<C, T>> for QAtomSeq<C, T> {
    fn from(g: HasTy<C, T>) -> Self {
        QAtomSeq {
            ctx: g.ctx,
            stmt: Quantified {
                binder: None,
                body: Atom::HasTy(g.tm, g.ty),
            },
        }
    }
}

impl<C, T> From<IsTyUnder<C, T>> for QAtomSeq<C, T> {
    fn from(g: IsTyUnder<C, T>) -> Self {
        QAtomSeq {
            ctx: g.ctx,
            stmt: Quantified {
                binder: Some(Forall(g.binder)),
                body: Atom::IsTy(g.tm),
            },
        }
    }
}

impl<C, T> From<HasTyUnder<C, T>> for QAtomSeq<C, T> {
    fn from(g: HasTyUnder<C, T>) -> Self {
        Seq {
            ctx: g.ctx,
            stmt: Quantified {
                binder: Some(Forall(g.binder)),
                body: Atom::HasTy(g.tm, g.ty),
            },
        }
    }
}

impl<C, T> From<ForallInhabUnder<C, T>> for QAtomSeq<C, T> {
    fn from(g: ForallInhabUnder<C, T>) -> Self {
        Seq {
            ctx: g.ctx,
            stmt: Quantified {
                binder: Some(Forall(g.binder)),
                body: Atom::IsInhab(g.ty),
            },
        }
    }
}

impl<C, T, R> FactIn<C, R> for Forall<T>
where
    C: Copy,
    T: Copy,
    R: ReadFacts<C, T> + ?Sized,
{
    /// Check this quantifier in the given context
    fn check_in(&self, &ctx: &C, ker: &R) -> bool {
        ker.is_ty(ctx, self.0)
    }
}

impl<C, T, R> FactIn<C, R> for Atom<T>
where
    C: Copy,
    T: Copy,
    R: ReadTermFacts<C, T> + ?Sized,
{
    /// Check whether this goal is true
    fn check_in(&self, &ctx: &C, ker: &R) -> bool {
        match *self {
            Atom::Eq(lhs, rhs) => ker.eq_in(ctx, lhs, rhs),
            Atom::IsWf(tm) => ker.is_wf(ctx, tm),
            Atom::IsTy(tm) => ker.is_ty(ctx, tm),
            Atom::IsProp(tm) => ker.is_prop(ctx, tm),
            Atom::HasTy(tm, ty) => ker.has_ty(ctx, tm, ty),
            Atom::IsInhab(tm) => ker.is_inhab(ctx, tm),
            Atom::IsEmpty(tm) => ker.is_empty(ctx, tm),
            Atom::Contr => ker.is_contr(ctx),
        }
    }
}

impl<C, T, R> FactUnder<C, Forall<T>, R> for Atom<T>
where
    C: Copy,
    T: Copy,
    R: ReadTermFacts<C, T> + ?Sized,
{
    /// Check whether this goal is true
    fn check_under(&self, &ctx: &C, &Forall(binder): &Forall<T>, ker: &R) -> bool {
        match *self {
            Atom::Eq(lhs, rhs) => ker.forall_eq_in(ctx, binder, lhs, rhs),
            Atom::IsWf(tm) => ker.forall_is_wf(ctx, binder, tm),
            Atom::IsTy(tm) => ker.forall_is_ty(ctx, binder, tm),
            Atom::IsProp(tm) => ker.forall_is_prop(ctx, binder, tm),
            Atom::HasTy(tm, ty) => ker.forall_has_ty(ctx, binder, tm, ty),
            Atom::IsInhab(tm) => ker.forall_is_inhab(ctx, binder, tm),
            Atom::IsEmpty(tm) => ker.forall_is_empty(ctx, binder, tm),
            Atom::Contr => ker.is_empty(ctx, binder),
        }
    }
}

impl<C, T, R> FactUnder<C, Option<Forall<T>>, R> for Atom<T>
where
    C: Copy,
    T: Copy,
    R: ReadTermFacts<C, T> + ?Sized,
{
    /// Check whether this goal is true
    fn check_under(&self, &ctx: &C, binder: &Option<Forall<T>>, ker: &R) -> bool {
        match binder {
            None => self.check_in(&ctx, ker),
            Some(binder) => self.check_under(&ctx, binder, ker),
        }
    }
}
