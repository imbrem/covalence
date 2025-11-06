/*!
Facts which can be checked in the datastore
*/
use std::ops::{Deref, DerefMut};

use covalence_data::{
    ctx::ReadCtxFacts,
    store::{CtxId, Ix, ReadLocalFacts, ReadLocalStore},
};

pub use crate::data::fact::*;

/// Atomic facts supported by the kernel
pub mod atom;

pub use atom::*;

/// A database which can check facts
pub trait CheckFact<F: ?Sized> {
    /// Check whether the given fact holds in this database
    fn check(&self, fact: &F) -> bool;
}

/// A database which can store unchecked facts
pub trait SetFactUnchecked<F: ?Sized> {
    /// Store the given fact without checking it
    ///
    /// Returns whether the fact was successfully set
    fn set_unchecked(&mut self, fact: F) -> bool;
}

/// A database which can check facts about ("within") a given context
pub trait CheckFactIn<C, F: ?Sized> {
    /// Check this fact in the given context
    fn check_in(&self, ctx: C, db: &F) -> bool;
}

/// A database which can set unchecked facts about ("within") a given context
pub trait SetFactUncheckedIn<C, F: ?Sized> {
    /// Store the given fact in the given context without checking it
    ///
    /// Returns whether the fact was successfully set
    fn set_unchecked_in(&mut self, ctx: C, fact: F) -> bool;
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

impl<C, S, R: ?Sized> SetFactUnchecked<Seq<C, S>> for R
where
    C: Copy,
    R: SetFactUncheckedIn<C, S>,
{
    fn set_unchecked(&mut self, fact: Seq<C, S>) -> bool {
        self.set_unchecked_in(fact.ctx, fact.stmt)
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
