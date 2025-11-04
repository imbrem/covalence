/*!
Facts which can be checked in the datastore
*/
use std::ops::{Deref, DerefMut};

use covalence_data::{
    ctx::ReadCtxFacts,
    store::{ReadLocalFacts, ReadLocalStore},
};

pub use crate::data::fact::*;

/// Logical composition for fact types
mod logic;

/// A fact which can be checked using a fact dataset
pub trait Fact<R: ?Sized> {
    /// Check whether this goal is true
    fn check(&self, db: &R) -> bool;
}

/// A fact which can be converted to an equivalent fact
pub trait EquivFact<F, R> {
    /// Convert this fact into an equivalent fact
    fn into_eqv(self, db: &R) -> F;
}

/// A fact about ("within") a given context
pub trait FactIn<C, R: ?Sized> {
    /// Check this fact in the given context
    fn check_in(&self, ctx: &C, db: &R) -> bool;
}

/// A fact which can be converted to an equivalent fact in a given context
pub trait EquivFactIn<F, C, R> {
    /// Convert this fact into an equivalent fact
    fn into_eqv_in(self, ctx: &C, db: &R) -> F;
}

/// A quantified fact within a given context
pub trait FactUnder<C, Q, R: ?Sized> {
    /// Check this fact under the given quantifier in the given context
    fn check_under(&self, ctx: &C, binder: &Q, db: &R) -> bool;
}

/// A quantified fact which can be converted to an equivalent quantified fact
pub trait EquivFactUnder<F, C, Q, R> {
    /// Convert this fact into an equivalent fact
    fn into_eqv_under(self, ctx: &C, binder: &Q, db: &R) -> F;
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

impl<C: Clone, S, F, R> EquivFact<Seq<C, F>, R> for Seq<C, S>
where
    S: EquivFactIn<F, C, R>,
{
    fn into_eqv(self, db: &R) -> Seq<C, F> {
        Seq {
            ctx: self.ctx.clone(),
            stmt: self.stmt.into_eqv_in(&self.ctx, db),
        }
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

impl<C, Q: Clone, S, F, R> EquivFactIn<Quantified<Q, F>, C, R> for Quantified<Q, S>
where
    S: EquivFactUnder<F, C, Q, R>,
{
    fn into_eqv_in(self, ctx: &C, db: &R) -> Quantified<Q, F> {
        Quantified {
            binder: self.binder.clone(),
            body: self.body.into_eqv_under(ctx, &self.binder, db),
        }
    }
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

/// A unary predicate holds on a term-in-context
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct HoldsIn<T> {
    pub pred: Pred1,
    pub tm: T,
}

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

impl<C: Copy, R> FactIn<C, R> for Pred0
where
    R: ReadCtxFacts<C> + ?Sized,
{
    fn check_in(&self, ctx: &C, db: &R) -> bool {
        db.ctx_satisfies(*ctx, *self)
    }
}

impl<R> FactUnder<R::CtxId, Forall<R::Ix>, R> for Pred0
where
    R: ReadLocalStore + ?Sized,
{
    fn check_under(&self, ctx: &R::CtxId, binder: &Forall<R::Ix>, db: &R) -> bool {
        db.ctx_satisfies(*ctx, *self)
            || *self == Pred0::IS_CONTR && db.local_tm_satisfies(*ctx, binder.0, Pred1::IS_EMPTY)
    }
}

impl<R> FactIn<R::CtxId, R> for Holds<R::CtxId, R::Ix>
where
    R: ReadLocalFacts + ?Sized,
{
    fn check_in(&self, ctx: &R::CtxId, db: &R) -> bool {
        db.local_tm_satisfies(*ctx, self.tm, self.pred)
    }
}

impl<R> FactIn<R::CtxId, R> for Eqn<R::Ix>
where
    R: ReadLocalFacts + ?Sized,
{
    fn check_in(&self, ctx: &R::CtxId, db: &R) -> bool {
        db.local_eq(*ctx, self.0, self.1)
    }
}

impl<R> FactIn<R::CtxId, R> for HasTy<R::Ix>
where
    R: ReadLocalFacts + ?Sized,
{
    fn check_in(&self, ctx: &R::CtxId, db: &R) -> bool {
        db.local_has_ty(*ctx, self.tm, self.ty)
    }
}

impl<C, T, R> FactIn<C, R> for Atom<T>
where
    Pred0: FactIn<C, R>,
    HoldsIn<T>: FactIn<C, R>,
    Eqn<T>: FactIn<C, R>,
    HasTy<T>: FactIn<C, R>,
    R: ?Sized,
    T: Copy,
{
    fn check_in(&self, ctx: &C, db: &R) -> bool {
        match *self {
            Atom::Pred0(p) => p.check_in(ctx, db),
            Atom::Pred1(p, tm) => HoldsIn { pred: p, tm }.check_in(ctx, db),
            Atom::Eqn(lhs, rhs) => Eqn(lhs, rhs).check_in(ctx, db),
            Atom::HasTy(tm, ty) => HasTy { tm, ty }.check_in(ctx, db),
        }
    }
}

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
