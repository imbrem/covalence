use std::fmt::{self, Display};
use std::ops::Deref;
use thiserror::Error;

use crate::Kernel;
use crate::error::KernelError;
use crate::fact::implies::FromIff;
use crate::fact::stable::StableFact;
use crate::fact::{CheckFact, SetFactUnchecked};

mod eqn;

/// A proven theorem
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Theorem<T> {
    /// The statement of this theorem
    pub(crate) stmt: T,
    /// The kernel ID this theorem belongs to
    pub(crate) id: u64,
}

impl<T> Theorem<T> {
    /// Get the kernel ID this theorem belongs to
    pub fn id(self) -> u64 {
        self.id
    }

    /// Convert this theorem into an equivalent one
    pub fn into_iff<U: FromIff<T>>(self) -> Theorem<U> {
        Theorem {
            stmt: U::from_iff(self.stmt),
            id: self.id,
        }
    }
}

impl<T> Deref for Theorem<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.stmt
    }
}

/// A theorem check failure
#[derive(Debug, Error)]
pub struct CheckFailed<F>(F);

impl<F: Display> Display for CheckFailed<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "covalence failed to check fact: {}", self.0)
    }
}

/// A kernel ID mismatch when attempting to use a theorem
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, PartialOrd, Ord, Error)]
pub struct IdMismatch;

impl Display for IdMismatch {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "covalence kernel ID mismatch",)
    }
}

impl<D> Kernel<D> {
    /// Construct a theorem in this kernel from a fact
    ///
    /// This is _unsound_ if the fact is not true!
    pub(crate) fn new_thm<F>(&self, fact: F) -> Theorem<F> {
        Theorem {
            stmt: fact,
            id: self.id(),
        }
    }

    /// Check whether a fact is true in the database
    ///
    /// If it is, return it as a theorem
    pub fn check_thm<F>(&self, fact: F) -> Result<Theorem<F>, CheckFailed<F>>
    where
        F: StableFact,
        D: CheckFact<F>,
    {
        if self.db.check(&fact) {
            Ok(self.new_thm(fact))
        } else {
            Err(CheckFailed(fact))
        }
    }

    /// Check whether a fact is true in the database
    ///
    /// If it is, return it as a theorem
    pub fn check_thm_ref<'a, F>(&self, fact: &'a F) -> Result<Theorem<&'a F>, CheckFailed<&'a F>>
    where
        F: StableFact,
        D: CheckFact<F>,
    {
        if self.db.check(fact) {
            Ok(self.new_thm(fact))
        } else {
            Err(CheckFailed(fact))
        }
    }

    /// Check whether a fact equivalent to this one is true in the database
    ///
    /// If it is, return it as a theorem
    pub fn check_thm_iff<G, F>(&self, fact: F) -> Result<Theorem<F>, CheckFailed<F>>
    where
        F: Copy,
        G: FromIff<F> + StableFact,
        D: CheckFact<G>,
    {
        if self.db.check(&G::from_iff(fact)) {
            Ok(self.new_thm(fact))
        } else {
            Err(CheckFailed(fact))
        }
    }

    /// Check this theorem belongs to this kernel
    ///
    /// Returns an error on kernel ID mismatch
    pub fn theorem_belongs<F>(&self, thm: &Theorem<F>) -> Result<(), IdMismatch> {
        if thm.id != self.id() {
            Err(IdMismatch)
        } else {
            Ok(())
        }
    }

    /// Store a theorem in the database
    ///
    /// Returns an error on kernel ID mismatch
    pub fn store_theorem<F>(&mut self, thm: &Theorem<F>) -> Result<(), KernelError>
    where
        F: StableFact,
        D: SetFactUnchecked<F>,
    {
        self.theorem_belongs(thm)?;
        self.db.set_unchecked(&thm.stmt)?;
        Ok(())
    }
}
