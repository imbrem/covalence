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
        IsWf(Node::HasTy([ht.tm, ht.ty]))
    }
}

/// A term has the given type in a context
pub type HasTyIn<C, T, Ty = T> = Seq<C, HasTy<T, Ty>>;

/// A term is well-formed
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct IsWf<T>(pub T);

/// A term is well-formed in a context
pub type IsWfIn<C, T> = Seq<C, IsWf<T>>;

/// A term is a type
pub struct IsTy<T>(pub T);

/// A term is a type in a context
pub type IsTyIn<C, T> = Seq<C, IsTy<T>>;

/// A term is a proposition
pub struct IsProp<T>(pub T);

/// A term is a proposition in a context
pub type IsPropIn<C, T> = Seq<C, IsProp<T>>;

/// A term is an inhabited type
pub struct IsInhab<T>(pub T);

/// A term is inhabited in a context
pub type IsInhabIn<C, T> = Seq<C, IsInhab<T>>;

/// A term is an empty type
pub struct IsEmpty<T>(pub T);

/// A term is empty in a context
pub type IsEmptyIn<C, T> = Seq<C, IsEmpty<T>>;

/// A term is the true proposition
pub struct IsTrue<T>(pub T);

/// A term is the true proposition in a context
pub struct IsTrueIn<C, T>(C, T);

/// A term is the false proposition
pub struct IsFalse<T>(pub T);

/// A term is the false proposition in a context
pub struct IsFalseIn<C, T>(C, T);

impl<T> FromIffSealed<IsWf<T>> for Holds<T> {}

impl<T> FromIff<IsWf<T>> for Holds<T> {
    fn from_iff(iwf: IsWf<T>) -> Self {
        Holds::is_wf(iwf.0)
    }
}

impl<T> FromIffSealed<IsTy<T>> for Holds<T> {}

impl<T> FromIff<IsTy<T>> for Holds<T> {
    fn from_iff(ity: IsTy<T>) -> Self {
        Holds::is_ty(ity.0)
    }
}

impl<T> FromIffSealed<IsProp<T>> for Holds<T> {}

impl<T> FromIff<IsProp<T>> for Holds<T> {
    fn from_iff(iprop: IsProp<T>) -> Self {
        Holds::is_prop(iprop.0)
    }
}

impl<T> FromIffSealed<IsInhab<T>> for Holds<T> {}

impl<T> FromIff<IsInhab<T>> for Holds<T> {
    fn from_iff(iinhab: IsInhab<T>) -> Self {
        Holds::is_inhab(iinhab.0)
    }
}

impl<T> FromIffSealed<IsEmpty<T>> for Holds<T> {}

impl<T> FromIff<IsEmpty<T>> for Holds<T> {
    fn from_iff(iempty: IsEmpty<T>) -> Self {
        Holds::is_empty(iempty.0)
    }
}

impl<T> FromIffSealed<IsTrue<T>> for Holds<T> {}

impl<T> FromIff<IsTrue<T>> for Holds<T> {
    fn from_iff(itt: IsTrue<T>) -> Self {
        Holds::is_true(itt.0)
    }
}

impl<T> FromIffSealed<IsFalse<T>> for Holds<T> {}

impl<T> FromIff<IsFalse<T>> for Holds<T> {
    fn from_iff(iff: IsFalse<T>) -> Self {
        Holds::is_false(iff.0)
    }
}
