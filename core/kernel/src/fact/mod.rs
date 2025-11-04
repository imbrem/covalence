/*!
Facts which can be checked in the datastore
*/
use std::ops::{Deref, DerefMut};

use covalence_data::{
    ctx::ReadCtxFacts,
    store::{CtxId, Ix, ReadLocalFacts, ReadLocalStore},
};

pub use crate::data::fact::*;

/// A database which can check facts
pub trait CheckFact<F: ?Sized> {
    /// Check whether the given fact holds in this database
    fn check(&self, fact: &F) -> bool;
}

/// A database which can check facts about ("within") a given context
pub trait CheckFactIn<C, F: ?Sized> {
    /// Check this fact in the given context
    fn check_in(&self, ctx: C, db: &F) -> bool;
}

/// A database which can check quantified facts within a given context
pub trait CheckFactUnder<C, Q, F: ?Sized> {
    /// Check this fact under the given quantifier in the given context
    fn check_under(&self, ctx: C, binder: &Q, fact: &F) -> bool;
}

/// A _sequent_: a pair `Γ ⊢ S` of a context and a statement
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct Seq<C, S> {
    /// The context for this sequent
    pub ctx: C,
    /// The statement asserted
    pub stmt: S,
}

impl<C, S, R: ?Sized> CheckFact<Seq<C, S>> for R
where
    C: Copy,
    R: CheckFactIn<C, S>,
{
    fn check(&self, fact: &Seq<C, S>) -> bool {
        self.check_in(fact.ctx, &fact.stmt)
    }
}

impl<C, S> Deref for Seq<C, S> {
    type Target = S;

    fn deref(&self) -> &Self::Target {
        &self.stmt
    }
}

impl<C, S> DerefMut for Seq<C, S> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.stmt
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

impl<C, Q, S, R: ?Sized> CheckFactIn<C, Quantified<Q, S>> for R
where
    C: Copy,
    R: CheckFactUnder<C, Q, S>,
{
    /// Check this quantified statement in the given context
    fn check_in(&self, ctx: C, fact: &Quantified<Q, S>) -> bool {
        self.check_under(ctx, &fact.binder, &fact.body)
    }
}

/// An atomic formula on terms supported by the kernel
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub enum Atom<T> {
    /// A nullary predicate on contexts
    Pred0(Pred0),
    /// A unary predicate on terms-in-context
    Pred1(Pred1, T),
    /// An equation
    Eqn(T, T),
    /// A term has a type
    HasTy(T, T),
}

impl<T> Atom<T> {
    /// A term is well-scoped
    pub const fn is_scoped(tm: T) -> Self {
        Atom::Pred1(IS_SCOPED, tm)
    }

    /// A term is well-formed
    pub const fn is_wf(tm: T) -> Self {
        Atom::Pred1(IS_WF, tm)
    }

    /// A term is a valid type
    pub const fn is_ty(tm: T) -> Self {
        Atom::Pred1(IS_TY, tm)
    }

    /// A term is a proposition
    pub const fn is_prop(tm: T) -> Self {
        Atom::Pred1(IS_PROP, tm)
    }

    /// A term is an inhabited type
    pub const fn is_inhab(tm: T) -> Self {
        Atom::Pred1(IS_INHAB, tm)
    }

    /// A term is an empty type
    pub const fn is_empty(tm: T) -> Self {
        Atom::Pred1(IS_EMPTY, tm)
    }

    /// A term is equal to the true proposition
    pub const fn is_true(tm: T) -> Self {
        Atom::Pred1(IS_TT, tm)
    }

    /// A term is equal to the false proposition
    pub const fn is_false(tm: T) -> Self {
        Atom::Pred1(IS_FF, tm)
    }

    /// A term is a valid typing universe
    pub const fn is_univ(tm: T) -> Self {
        Atom::Pred1(IS_UNIV, tm)
    }
}

/// A universal quantifier
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct Forall<T>(T);

/// A potentially-quantified atomic formula
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
                body: Atom::Pred0(Pred0::IS_CONTR),
            },
        }
    }
}
/// A unary predicate holds on a term-in-context
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct HoldsIn<T> {
    pub pred: Pred1,
    pub tm: T,
}

impl<T> HoldsIn<T> {
    pub const fn is_scoped(tm: T) -> Self {
        HoldsIn {
            pred: IS_SCOPED,
            tm,
        }
    }

    pub const fn is_wf(tm: T) -> Self {
        HoldsIn { pred: IS_WF, tm }
    }

    pub const fn is_ty(tm: T) -> Self {
        HoldsIn { pred: IS_TY, tm }
    }

    pub const fn is_prop(tm: T) -> Self {
        HoldsIn { pred: IS_PROP, tm }
    }

    pub const fn is_inhab(tm: T) -> Self {
        HoldsIn { pred: IS_INHAB, tm }
    }

    pub const fn is_empty(tm: T) -> Self {
        HoldsIn { pred: IS_EMPTY, tm }
    }

    pub const fn is_true(tm: T) -> Self {
        HoldsIn { pred: IS_TT, tm }
    }

    pub const fn is_false(tm: T) -> Self {
        HoldsIn { pred: IS_FF, tm }
    }

    pub const fn is_univ(tm: T) -> Self {
        HoldsIn { pred: IS_UNIV, tm }
    }

    pub const fn is_contr(tm: T) -> Self {
        HoldsIn { pred: IS_CONTR, tm }
    }
}

/// A unary predicate holds on a term
pub type Holds<C, T> = Seq<C, HoldsIn<T>>;

/// An equation
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct Eqn<L, R = L>(pub L, pub R);

/// An equation-in-context
pub type EqnIn<C, L, R = L> = Seq<C, Eqn<L, R>>;

impl<C, L, R> EqnIn<C, L, R> {
    /// Construct a new equation-in-context
    pub const fn new(ctx: C, lhs: L, rhs: R) -> Self {
        Seq {
            ctx,
            stmt: Eqn(lhs, rhs),
        }
    }
}

/// A term has the given type
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct HasTy<T> {
    pub tm: T,
    pub ty: T,
}

/// A term has the given type in a context
pub type HasTyIn<C, T> = Seq<C, HasTy<T>>;

impl<C: Copy, R> CheckFactIn<C, Pred0> for R
where
    R: ReadCtxFacts<C> + ?Sized,
{
    fn check_in(&self, ctx: C, pred: &Pred0) -> bool {
        self.ctx_satisfies(ctx, *pred)
    }
}

impl<R> CheckFactUnder<CtxId<R>, Forall<Ix<R>>, Pred0> for R
where
    R: ReadLocalStore + ?Sized,
{
    fn check_under(&self, ctx: CtxId<R>, binder: &Forall<Ix<R>>, pred: &Pred0) -> bool {
        self.ctx_satisfies(ctx, *pred)
            || *pred == Pred0::IS_CONTR && self.local_tm_satisfies(ctx, binder.0, Pred1::IS_EMPTY)
    }
}

impl<R> CheckFactIn<CtxId<R>, Holds<CtxId<R>, Ix<R>>> for R
where
    R: ReadLocalFacts + ?Sized,
{
    fn check_in(&self, ctx: CtxId<R>, fact: &Holds<CtxId<R>, Ix<R>>) -> bool {
        self.local_tm_satisfies(ctx, fact.tm, fact.pred)
    }
}

impl<R> CheckFactIn<CtxId<R>, Eqn<Ix<R>>> for R
where
    R: ReadLocalFacts + ?Sized,
{
    fn check_in(&self, ctx: CtxId<R>, fact: &Eqn<Ix<R>>) -> bool {
        self.local_eq(ctx, fact.0, fact.1)
    }
}

impl<R> CheckFactIn<CtxId<R>, HasTy<Ix<R>>> for R
where
    R: ReadLocalFacts + ?Sized,
{
    fn check_in(&self, ctx: CtxId<R>, fact: &HasTy<Ix<R>>) -> bool {
        self.local_has_ty(ctx, fact.tm, fact.ty)
    }
}

impl<R> CheckFactIn<CtxId<R>, Atom<Ix<R>>> for R
where
    R: ReadLocalStore + ?Sized,
{
    fn check_in(&self, ctx: CtxId<R>, fact: &Atom<Ix<R>>) -> bool {
        match fact {
            Atom::Pred0(p) => self.ctx_satisfies(ctx, *p),
            Atom::Pred1(p, tm) => self.local_tm_satisfies(ctx, *tm, *p),
            Atom::Eqn(lhs, rhs) => self.local_eq(ctx, *lhs, *rhs),
            Atom::HasTy(tm, ty) => self.local_has_ty(ctx, *tm, *ty),
        }
    }
}

/// A term is well-formed
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct IsWf<T>(T);

/// A term is well-formed in a context
pub type IsWfIn<C, T> = Seq<C, IsWf<T>>;

/// A term is a type
pub struct IsTy<T>(T);

/// A term is a type in a context
pub type IsTyIn<C, T> = Seq<C, IsTy<T>>;

/// A term is a proposition
pub struct IsProp<T>(T);

/// A term is a proposition in a context
pub type IsPropIn<C, T> = Seq<C, IsProp<T>>;

/// A term is an inhabited type
pub struct IsInhab<T>(T);

/// A term is inhabited in a context
pub type IsInhabIn<C, T> = Seq<C, IsInhab<T>>;

/// A term is an empty type
pub struct IsEmpty<T>(T);

/// A term is empty in a context
pub type IsEmptyIn<C, T> = Seq<C, IsEmpty<T>>;

/// A term is the true proposition
pub struct IsTrue<T>(T);

/// A term is the true proposition in a context
pub struct IsTrueIn<C, T>(C, T);

/// A term is the false proposition
pub struct IsFalse<T>(T);

/// A term is the false proposition in a context
pub struct IsFalseIn<C, T>(C, T);

/*
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
            Atom::Pred0(p) => ker.ctx_satisfies(ctx, p),
            Atom::Pred1(p, tm) => ker.tm_satisfies(ctx, tm, p),
            Atom::Eqn(lhs, rhs) => ker.eq_in(ctx, lhs, rhs),
            Atom::HasTy(tm, ty) => ker.has_ty(ctx, tm, ty),
        }
    }
}

impl<C, T, R> FactUnder<C, Forall<T>, R> for Atom<T>
where
    C: Copy,
    T: Copy,
    R: ReadQuantFacts<C, T> + ?Sized,
{
    /// Check whether this goal is true
    fn check_under(&self, &ctx: &C, &Forall(binder): &Forall<T>, ker: &R) -> bool {
        match *self {
            Atom::Pred0(p) => ker.tm_satisfies(ctx, binder, p.forall()),
            Atom::Pred1(p, tm) => ker.forall_satisfies(ctx, binder, tm, p),
            Atom::Eqn(lhs, rhs) => ker.forall_eq_in(ctx, binder, lhs, rhs),
            Atom::HasTy(tm, ty) => ker.forall_has_ty(ctx, binder, tm, ty),
        }
    }
}

impl<C, T, R> FactUnder<C, Option<Forall<T>>, R> for Atom<T>
where
    C: Copy,
    T: Copy,
    R: ReadQuantFacts<C, T> + ?Sized,
{
    /// Check whether this goal is true
    fn check_under(&self, &ctx: &C, binder: &Option<Forall<T>>, ker: &R) -> bool {
        match binder {
            None => self.check_in(&ctx, ker),
            Some(binder) => self.check_under(&ctx, binder, ker),
        }
    }
}
*/
