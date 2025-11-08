use std::fmt::{self, Display};
use thiserror::Error;

use crate::Kernel;
use crate::error::KernelError;
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
    /// Check whether a fact is true in the database
    ///
    /// If it is, return it as a theorem
    pub fn check_thm<F>(&self, fact: F) -> Result<Theorem<F>, CheckFailed<F>>
    where
        F: StableFact,
        D: CheckFact<F>,
    {
        if self.db.check(&fact) {
            Ok(Theorem {
                stmt: fact,
                id: self.id(),
            })
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
