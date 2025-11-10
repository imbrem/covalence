use std::fmt::{self, Debug, Display};
use std::hash::Hash;
use std::marker::PhantomData;
use std::ops::Deref;
use thiserror::Error;

use crate::Kernel;
use crate::error::KernelError;
use crate::fact::implies::{FromIff, TryFromIff};
use crate::fact::stable::StableFact;
use crate::fact::{CheckFact, SetFactUnchecked};

mod eqn;

mod quant;

/// A proven theorem
pub struct Theorem<F, D> {
    /// The statement of this theorem
    pub(crate) stmt: F,
    /// The kernel ID this theorem belongs to
    pub(crate) id: u64,
    /// The data store in use
    pub(crate) store: PhantomData<D>,
}

impl<F: Clone, D> Clone for Theorem<F, D> {
    fn clone(&self) -> Self {
        Theorem {
            stmt: self.stmt.clone(),
            id: self.id,
            store: PhantomData,
        }
    }
}

impl<F: Copy, D> Copy for Theorem<F, D> {}

impl<F: PartialEq, D> PartialEq for Theorem<F, D> {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id && self.stmt == other.stmt
    }
}

impl<F: Eq, D> Eq for Theorem<F, D> {}

impl<F: PartialOrd, D> PartialOrd for Theorem<F, D> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match self.id.cmp(&other.id) {
            std::cmp::Ordering::Equal => self.stmt.partial_cmp(&other.stmt),
            ord => Some(ord),
        }
    }
}

impl<F: Ord, D> Ord for Theorem<F, D> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match self.id.cmp(&other.id) {
            std::cmp::Ordering::Equal => self.stmt.cmp(&other.stmt),
            ord => ord,
        }
    }
}

impl<F: Hash, D> Hash for Theorem<F, D> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id.hash(state);
        self.stmt.hash(state);
    }
}

impl<F: Debug, D> Debug for Theorem<F, D> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Theorem")
            .field("id", &self.id)
            .field("stmt", &self.stmt)
            .finish()
    }
}

impl<F, D> Theorem<F, D> {
    /// Get the kernel ID this theorem belongs to
    pub fn id(self) -> u64 {
        self.id
    }

    /// Convert this theorem into an equivalent one
    pub fn into_iff<U: FromIff<F>>(self) -> Theorem<U, D> {
        Theorem {
            stmt: U::from_iff(self.stmt),
            id: self.id,
            store: PhantomData,
        }
    }

    /// Try to convert this theorem into an equivalent one
    pub fn try_into_iff<U: TryFromIff<F>>(self) -> Result<Theorem<U, D>, Theorem<F, D>> {
        match U::try_from_iff(self.stmt) {
            Ok(stmt) => Ok(Theorem {
                stmt,
                id: self.id,
                store: PhantomData,
            }),
            Err(stmt) => Err(Theorem {
                stmt,
                id: self.id,
                store: PhantomData,
            }),
        }
    }

    /// Get the statement of this theorem as a reference
    pub fn as_ref(&self) -> Theorem<&F, D> {
        Theorem {
            stmt: &self.stmt,
            id: self.id,
            store: PhantomData,
        }
    }

    /// Get the statement of this theorem as a mutable reference
    pub fn as_mut(&mut self) -> Theorem<&mut F, D> {
        Theorem {
            stmt: &mut self.stmt,
            id: self.id,
            store: PhantomData,
        }
    }

    /// Get the statement of this theorem by value
    pub fn into_inner(self) -> F {
        self.stmt
    }
}

impl<F: Clone, D> Theorem<&F, D> {
    /// Clone the statement of this theorem
    pub fn cloned(self) -> Theorem<F, D> {
        Theorem {
            stmt: self.stmt.clone(),
            id: self.id,
            store: PhantomData,
        }
    }
}

impl<F: Copy, D> Theorem<&F, D> {
    /// Copy the statement of this theorem
    pub fn copied(self) -> Theorem<F, D> {
        Theorem {
            stmt: *self.stmt,
            id: self.id,
            store: PhantomData,
        }
    }
}

impl<F, D> Deref for Theorem<F, D> {
    type Target = F;

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
    pub(crate) fn new_thm<F>(&self, fact: F) -> Theorem<F, D> {
        Theorem {
            stmt: fact,
            id: self.id(),
            store: PhantomData,
        }
    }

    /// Check whether a fact is true in the database
    ///
    /// If it is, return it as a theorem
    pub fn check_thm<F>(&self, fact: F) -> Result<Theorem<F, D>, CheckFailed<F>>
    where
        F: StableFact<D>,
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
    pub fn check_thm_ref<'a, F>(&self, fact: &'a F) -> Result<Theorem<&'a F, D>, CheckFailed<&'a F>>
    where
        F: StableFact<D>,
        D: CheckFact<F>,
    {
        if self.db.check(fact) {
            Ok(self.new_thm(fact))
        } else {
            Err(CheckFailed(fact))
        }
    }

    /// Check whether a fact is true in the database
    ///
    /// If it is, return it as a theorem
    pub fn check_thm_mut<'a, F>(
        &self,
        fact: &'a mut F,
    ) -> Result<Theorem<&'a mut F, D>, CheckFailed<&'a mut F>>
    where
        F: StableFact<D>,
        D: CheckFact<F>,
    {
        if self.db.check(fact) {
            Ok(self.new_thm(fact))
        } else {
            Err(CheckFailed(fact))
        }
    }

    /// Check this theorem belongs to this kernel
    ///
    /// Returns an error on kernel ID mismatch
    pub fn theorem_belongs<F>(&self, thm: &Theorem<F, D>) -> Result<(), IdMismatch> {
        if thm.id != self.id() {
            Err(IdMismatch)
        } else {
            Ok(())
        }
    }

    /// Store a theorem in the database
    ///
    /// Returns an error on kernel ID mismatch
    pub fn store_theorem<F>(&mut self, thm: &Theorem<F, D>) -> Result<(), KernelError>
    where
        F: StableFact<D>,
        D: SetFactUnchecked<F>,
    {
        self.theorem_belongs(thm)?;
        self.db.set_unchecked(&thm.stmt)?;
        Ok(())
    }
}
