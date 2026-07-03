//! `Ctx` — a theorem's hypothesis context.
//!
//! `Ctx` is an **opaque** newtype over [`crate::term::TermSet`]: it
//! adds the "this is a theorem's hypothesis context" identity on top
//! of the generic structurally-shared term-set mechanism, and is the
//! only shape the kernel exposes for theorem hypotheses. The backing
//! representation lives entirely in [`crate::term::set`]; this module
//! just re-presents the needed API by delegating to it.
//!
//! ## Iteration order
//!
//! Iteration follows the underlying set's order. Callers must treat
//! the order as stable for a given `Ctx` value but not semantically
//! meaningful — equality is set equality.

use crate::term::Term;
use crate::term::set::{self, TermSet};

/// A context for a theorem — an opaque set of hypotheses.
#[derive(Clone, Default, PartialEq, Eq)]
pub struct Ctx(TermSet);

impl Ctx {
    /// The empty context. Does not allocate.
    pub fn new() -> Self {
        Ctx(TermSet::new())
    }

    /// A context with a single hypothesis.
    pub fn singleton(t: Term) -> Self {
        Ctx(TermSet::singleton(t))
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn contains(&self, t: &Term) -> bool {
        self.0.contains(t)
    }

    /// Iterate over hypotheses in the underlying set's order.
    pub fn iter(&self) -> set::Iter<'_> {
        self.0.iter()
    }

    /// Return the `idx`-th hypothesis in iteration order, or `None`.
    pub fn at(&self, idx: usize) -> Option<&Term> {
        self.0.at(idx)
    }

    /// Return a new context with `t` added.
    pub fn insert(&self, t: Term) -> Self {
        Ctx(self.0.insert(t))
    }

    /// Return a new context without `t`.
    pub fn remove(&self, t: &Term) -> Self {
        Ctx(self.0.remove(t))
    }

    /// `true` iff every term in `self` is also in `other`.
    pub fn is_subset(&self, other: &Self) -> bool {
        self.0.is_subset(&other.0)
    }

    /// Set-theoretic union.
    pub fn union(&self, other: &Self) -> Self {
        Ctx(self.0.union(&other.0))
    }

    /// Apply `f` to every hypothesis, returning a new context.
    pub fn map<F: FnMut(&Term) -> Term>(&self, f: F) -> Self {
        Ctx(self.0.map(f))
    }
}

impl std::fmt::Debug for Ctx {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl<'a> IntoIterator for &'a Ctx {
    type Item = &'a Term;
    type IntoIter = set::Iter<'a>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl FromIterator<Term> for Ctx {
    fn from_iter<I: IntoIterator<Item = Term>>(iter: I) -> Self {
        Ctx(TermSet::from_iter(iter))
    }
}
