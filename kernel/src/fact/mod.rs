/*!
Facts which can be checked in the datastore
*/
use std::ops::{Deref, DerefMut};

/// Logical combinators for facts
pub mod logic;

/// Predicates on terms-in-context supported by the kernel
pub mod pred;

pub use pred::*;

/// Atomic facts supported by the kernel
pub mod atom;

pub use atom::*;

/// Quantified facts
pub mod quant;

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
    fn set_unchecked(&mut self, fact: &F) -> bool;
}

/// A database which can check facts about ("within") a given context
pub trait CheckFactIn<C, F: ?Sized> {
    /// Check this fact in the given context
    fn check_in(&self, ctx: C, fact: &F) -> bool;
}

/// A database which can set unchecked facts about ("within") a given context
pub trait SetFactUncheckedIn<C, F: ?Sized> {
    /// Store the given fact in the given context without checking it
    ///
    /// Returns whether the fact was successfully set
    fn set_unchecked_in(&mut self, ctx: C, fact: &F) -> bool;
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
    fn set_unchecked(&mut self, fact: &Seq<C, S>) -> bool {
        self.set_unchecked_in(fact.ctx, &fact.stmt)
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
