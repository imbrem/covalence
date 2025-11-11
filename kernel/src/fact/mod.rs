/*!
Facts which can be checked in the datastore
*/
use std::ops::{Deref, DerefMut};

/// Logical combinators for facts
pub mod logic;

/// Atomic facts supported by the kernel
pub mod atom;

pub use atom::*;

use crate::{
    data::term::HasTy,
    formula::{
        CheckFormula, HasTyP, Is, IsEmpty, IsFalse, IsInhab, IsProp, IsTrue, IsTy, IsWf, Pred0,
        SetFactUncheckedIn, StoreFailure, Wf,
    },
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

/// A database which can store unchecked facts
pub trait SetFactUnchecked<F: ?Sized> {
    /// Store the given fact without checking it
    ///
    /// Returns whether the fact was successfully set
    fn set_unchecked(&mut self, fact: &F) -> Result<(), StoreFailure>;
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

/// A nullary predicate holds for a context
pub type HoldsFor<C> = Seq<C, Pred0>;

/// A unary predicate holds on a term-in-context
pub type IsIn<C, P, T> = Seq<C, Is<P, T>>;

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

/// A term is well-formed in a context
pub type IsWfIn<C, T> = Seq<C, IsWf<T>>;

/// A term is a type in a context
pub type IsTyIn<C, T> = Seq<C, IsTy<T>>;

/// A term is a proposition in a context
pub type IsPropIn<C, T> = Seq<C, IsProp<T>>;

/// A term is inhabited in a context
pub type IsInhabIn<C, T> = Seq<C, IsInhab<T>>;

/// A term is empty in a context
pub type IsEmptyIn<C, T> = Seq<C, IsEmpty<T>>;

/// A term is the true proposition in a context
pub type IsTrueIn<C, T> = Seq<C, IsTrue<T>>;

/// A term is the false proposition in a context
pub type IsFalseIn<C, T> = Seq<C, IsFalse<T>>;
