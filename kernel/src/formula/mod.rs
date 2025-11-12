/*!
Facts which can be checked in the datastore
*/
use std::fmt::{self, Display};
use thiserror::Error;

/// Logical combinators for formulas
pub mod logic;

pub use logic::*;

/// Predicates on terms-in-context supported by the kernel
pub mod pred;

pub use pred::*;

use crate::data::term::HasTy;

/// Quantified formulas
pub mod quant;

/// Stable formulas
pub mod stable;

pub use stable::*;

/// Atomic formulas supported by the kernel
pub mod atom;

pub use atom::*;

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

/// A database which can set unchecked facts about ("within") a given context
pub trait SetFactUncheckedIn<C, F: ?Sized> {
    /// Store the given fact in the given context without checking it
    ///
    /// Returns whether the fact was successfully set
    fn set_unchecked_in(&mut self, ctx: C, fact: &F) -> Result<(), StoreFailure>;
}

/// An equation
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct Rw<L, R = L>(pub L, pub R);

/// A term has the given type
pub type HasTyP<T, Ty = T> = IsWf<HasTy<T, Ty>>;
