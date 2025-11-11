use std::fmt::{self, Debug, Display};
use std::hash::Hash;
use std::marker::PhantomData;
use std::ops::Deref;
use thiserror::Error;

use crate::Kernel;
use crate::error::KernelError;
use crate::fact::logic::{Iff, Implies, TryIff};
use crate::fact::stable::StableFact;
use crate::fact::{CheckFact, RwIn, SetFactUnchecked};
use crate::id::KernelId;
use crate::store::{CtxId, Ix, NodeIx, ReadLocalTerm, TermIndex, TmId, WriteLocalTerm};

pub mod eqn;

pub mod quant;

/// A proven theorem
pub struct Theorem<F, D> {
    /// The statement of this theorem
    pub(crate) stmt: F,
    /// The kernel ID this theorem belongs to
    pub(crate) id: KernelId,
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
    pub fn id(self) -> KernelId {
        self.id
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

    /// Get whether this theorem is compatible with another theorem
    pub fn compat<G>(&self, other: &Theorem<G, D>) -> Result<(), IdMismatch> {
        if self.id != other.id {
            return Err(IdMismatch);
        }
        Ok(())
    }

    /// A pair of theorems is a theorem of pairs
    pub fn pair<G>(self, other: Theorem<G, D>) -> Result<Theorem<(F, G), D>, IdMismatch> {
        self.compat(&other)?;
        Ok(Theorem {
            stmt: (self.stmt, other.stmt),
            id: self.id,
            store: PhantomData,
        })
    }
}

impl<F, G, D> Implies<Theorem<G, D>, D> for Theorem<F, D>
where
    F: StableFact<D> + Implies<G, D>,
    G: StableFact<D>,
{
    fn implies(self) -> Theorem<G, D> {
        Theorem {
            stmt: self.stmt.implies(),
            id: self.id,
            store: PhantomData,
        }
    }
}

impl<F, G, D> Iff<Theorem<G, D>, D> for Theorem<F, D>
where
    F: StableFact<D> + Iff<G, D>,
    G: StableFact<D>,
{
    fn iff(self) -> Theorem<G, D> {
        Theorem {
            stmt: self.stmt.iff(),
            id: self.id,
            store: PhantomData,
        }
    }
}

impl<F, G, D> TryIff<Theorem<G, D>, D> for Theorem<F, D>
where
    F: StableFact<D> + TryIff<G, D>,
    G: StableFact<D>,
{
    fn try_iff(self) -> Result<Theorem<G, D>, Self> {
        match self.stmt.try_iff() {
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

    /// Cons a term into the context, returning it as an equation
    pub fn cons_eqn(
        &mut self,
        ctx: CtxId<D>,
        tm: NodeIx<D>,
    ) -> Theorem<RwIn<CtxId<D>, NodeIx<D>, Ix<D>>, D>
    where
        D: TermIndex + WriteLocalTerm<D>,
    {
        let ix = self.db.cons_node_ix(ctx, tm);
        let thm = RwIn::new(ctx, tm, ix);
        self.new_thm(thm)
    }

    /// Cons a term into the context, returning it as an equation
    pub fn cons_into_eqn<T>(
        &mut self,
        ctx: CtxId<D>,
        tm: T,
    ) -> Theorem<RwIn<CtxId<D>, T, Ix<D>>, D>
    where
        T: Clone + Into<NodeIx<D>>,
        D: TermIndex + WriteLocalTerm<D>,
    {
        let node = tm.clone().into();
        let ix = self.db.cons_node_ix(ctx, node);
        let thm = RwIn::new(ctx, tm, ix);
        self.new_thm(thm)
    }

    /// Cons a term into the context, returning it as an equation
    pub fn cons_try_into_eqn<T>(
        &mut self,
        ctx: CtxId<D>,
        tm: T,
    ) -> Result<Theorem<RwIn<CtxId<D>, T, Ix<D>>, D>, T::Error>
    where
        T: Clone + TryInto<NodeIx<D>>,
        D: TermIndex + WriteLocalTerm<D>,
    {
        let node = tm.clone().try_into()?;
        let ix = self.db.cons_node_ix(ctx, node);
        let thm = RwIn::new(ctx, tm, ix);
        Ok(self.new_thm(thm))
    }

    /// Get the node of a term in the context, returning the result as an equation
    pub fn node_eqn(
        &self,
        ctx: CtxId<D>,
        ix: Ix<D>,
    ) -> Theorem<RwIn<CtxId<D>, Ix<D>, NodeIx<D>>, D>
    where
        D: TermIndex + ReadLocalTerm<D>,
    {
        let tm = self.db.node(ctx, ix);
        let thm = RwIn::new(ctx, ix, tm);
        self.new_thm(thm)
    }

    /// Lookup a term in the context, returning the result as an equation
    pub fn lookup_eqn(
        &self,
        ctx: CtxId<D>,
        tm: NodeIx<D>,
    ) -> Option<Theorem<RwIn<CtxId<D>, NodeIx<D>, Ix<D>>, D>>
    where
        D: TermIndex + ReadLocalTerm<D>,
    {
        let ix = self.db.lookup(ctx, tm)?;
        let thm = RwIn::new(ctx, tm, ix);
        Some(self.new_thm(thm))
    }

    /// Lookup an import in the context, returning the result as an equation
    ///
    /// Does not traverse import chains
    pub fn lookup_import_eqn(
        &self,
        ctx: CtxId<D>,
        tm: TmId<D>,
    ) -> Option<Theorem<RwIn<CtxId<D>, TmId<D>, Ix<D>>, D>>
    where
        D: TermIndex + ReadLocalTerm<D>,
    {
        let ix = self.db.lookup_import(ctx, tm)?;
        let thm = RwIn::new(ctx, tm, ix);
        Some(self.new_thm(thm))
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
    pub fn thm_belongs<F>(&self, thm: &Theorem<F, D>) -> Result<(), IdMismatch> {
        if thm.id != self.id() {
            Err(IdMismatch)
        } else {
            Ok(())
        }
    }

    /// Store a theorem in the database
    ///
    /// Returns an error on kernel ID mismatch
    pub fn store_thm<F>(&mut self, thm: &Theorem<F, D>) -> Result<(), KernelError>
    where
        F: StableFact<D>,
        D: SetFactUnchecked<F>,
    {
        self.thm_belongs(thm)?;
        self.db.set_unchecked(&thm.stmt)?;
        Ok(())
    }
}
