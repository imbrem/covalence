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
    data::term::HasTy,
    fact::logic::IffIn,
    store::{Ctx, LocalTerm},
};

/// Quantified facts
pub mod quant;

/// Stable facts
pub mod stable;

/// A database which can check facts
pub trait CheckFact<F: ?Sized> {
    /// Check whether the given fact holds in this database
    fn check(&self, fact: &F) -> bool;
}

/// A database which can check _formulas_: facts situated in a given context
pub trait CheckFormula<C, F: ?Sized> {
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

/// A _sequent_: a pair `Γ ⊢ φ` of a context and a formula in that context
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct Seq<C, S> {
    /// The context for this sequent
    pub ctx: C,
    /// The formula asserted in this context
    pub form: S,
}

impl<C, S, R> CheckFact<Seq<C, S>> for R
where
    C: Copy,
    R: CheckFormula<C, S>,
{
    fn check(&self, fact: &Seq<C, S>) -> bool {
        self.check_in(fact.ctx, &fact.form)
    }
}

impl<C, S, R> SetFactUnchecked<Seq<C, S>> for R
where
    C: Copy,
    R: SetFactUncheckedIn<C, S> + ?Sized,
{
    fn set_unchecked(&mut self, fact: &Seq<C, S>) -> Result<(), StoreFailure> {
        self.set_unchecked_in(fact.ctx, &fact.form)
    }
}

impl<C, S> Deref for Seq<C, S> {
    type Target = S;

    fn deref(&self) -> &Self::Target {
        &self.form
    }
}

impl<C, S> DerefMut for Seq<C, S> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.form
    }
}

/// An equation
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct Rw<L, R = L>(pub L, pub R);

/// An equation-in-context
pub type RwIn<C, L, R = L> = Seq<C, Rw<L, R>>;

impl<C, L, R> RwIn<C, L, R> {
    /// Construct a new equation-in-context
    pub const fn new(ctx: C, lhs: L, rhs: R) -> Self {
        Seq {
            ctx,
            form: Rw(lhs, rhs),
        }
    }
}

/// A term has the given type
pub type HasTyP<T, Ty = T> = IsWf<HasTy<T, Ty>>;

/// A term has the given type in a context
pub type HasTyIn<C, T, Ty = T> = Seq<C, HasTyP<T, Ty>>;

impl<C, T, Ty> HasTyIn<C, T, Ty> {
    /// Construct a new `HasTyIn` fact
    pub const fn new(ctx: C, tm: T, ty: Ty) -> Self {
        Seq {
            ctx,
            form: Is(Wf, HasTy::new(tm, ty)),
        }
    }
}
