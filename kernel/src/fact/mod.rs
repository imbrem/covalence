/*!
Facts which can be checked in the datastore
*/
use std::{
    fmt::{self, Display},
    ops::{Deref, DerefMut},
};
use thiserror::Error;

/// Logical combinators for facts
pub mod logic;

/// Predicates on terms-in-context supported by the kernel
pub mod pred;

pub use pred::*;

/// Atomic facts supported by the kernel
pub mod atom;

pub use atom::*;

use crate::{
    data::term::Node,
    fact::implies::{FromIff, FromIffSealed},
};

/// Quantified facts
pub mod quant;

/// Stable facts
pub mod stable;

/// Implication for facts
pub mod implies;

/// A database which can check facts
pub trait CheckFact<F: ?Sized> {
    /// Check whether the given fact holds in this database
    fn check(&self, fact: &F) -> bool;
}

/// A database which can check facts about ("within") a given context
pub trait CheckFactIn<C, F: ?Sized> {
    /// Check this fact in the given context
    fn check_in(&self, ctx: C, fact: &F) -> bool;
}

/// An error indicating a failure to store a fact
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Error)]
pub struct StoreFailure;

impl Display for StoreFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "failed to store fact")
    }
}

/// A database which can store unchecked facts
pub trait SetFactUnchecked<F: ?Sized> {
    /// Store the given fact without checking it
    ///
    /// Returns whether the fact was successfully set
    fn set_unchecked(&mut self, fact: &F) -> Result<(), StoreFailure>;
}

/// A database which can set unchecked facts about ("within") a given context
pub trait SetFactUncheckedIn<C, F: ?Sized> {
    /// Store the given fact in the given context without checking it
    ///
    /// Returns whether the fact was successfully set
    fn set_unchecked_in(&mut self, ctx: C, fact: &F) -> Result<(), StoreFailure>;
}

/// A _sequent_: a pair `Γ ⊢ S` of a context and a statement
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct Seq<C, S> {
    /// The context for this sequent
    pub ctx: C,
    /// The statement asserted
    pub stmt: S,
}

impl<C, S, R> CheckFact<Seq<C, S>> for R
where
    C: Copy,
    R: CheckFactIn<C, S>,
{
    fn check(&self, fact: &Seq<C, S>) -> bool {
        self.check_in(fact.ctx, &fact.stmt)
    }
}

impl<C, S, R> SetFactUnchecked<Seq<C, S>> for R
where
    C: Copy,
    R: SetFactUncheckedIn<C, S> + ?Sized,
{
    fn set_unchecked(&mut self, fact: &Seq<C, S>) -> Result<(), StoreFailure> {
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

impl<C, F, G> FromIffSealed<Seq<C, F>> for Seq<C, G> where G: FromIff<F> {}

impl<C, F, G> FromIff<Seq<C, F>> for Seq<C, G>
where
    G: FromIff<F>,
{
    fn from_iff(fact: Seq<C, F>) -> Self {
        Seq {
            ctx: fact.ctx,
            stmt: G::from_iff(fact.stmt),
        }
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
pub struct HasTy<L, R = L> {
    pub tm: L,
    pub ty: R,
}

impl<C, T> FromIffSealed<HasTy<T>> for IsWf<Node<C, T>> {}

impl<C, T> FromIff<HasTy<T>> for IsWf<Node<C, T>> {
    fn from_iff(ht: HasTy<T>) -> Self {
        Is(Wf, Node::HasTy([ht.tm, ht.ty]))
    }
}

/// A term has the given type in a context
pub type HasTyIn<C, T, Ty = T> = Seq<C, HasTy<T, Ty>>;
