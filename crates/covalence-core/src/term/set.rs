//! Immutable, structurally-shared sets of terms.
//!
//! `TermSet` is the backing set mechanism that [`crate::Ctx`]
//! wraps. The
//! kernel never exposes its backing representation: this module is
//! the only place that knows whether hyps are stored as a
//! `BTreeSet`, a hash-trie, or anything else. Downstream code goes
//! through the methods here.
//!
//! ## Current representation
//!
//! `Option<Arc<BTreeSet<Term>>>` — `None` for the empty context (no
//! allocation), `Some(Arc<...>)` for non-empty. Most kernel rules
//! propagate their hypotheses unchanged, so the `Arc` is shared
//! across many `Thm` values, and `union` is O(1) when either side
//! is empty or both sides are pointer-equal.
//!
//! ## Iteration order
//!
//! Iteration follows the underlying `BTreeSet` order. Callers must
//! treat the order as stable for a given `TermSet` value but not
//! semantically meaningful — equality is set equality.

use std::collections::BTreeSet;
use std::sync::Arc;

use crate::term::Term;

/// A structurally-shared, immutable set of terms.
#[derive(Clone, Default)]
pub struct TermSet(Option<Arc<BTreeSet<Term>>>);

impl TermSet {
    /// The empty set. Does not allocate.
    pub fn new() -> Self {
        TermSet(None)
    }

    /// A set with a single element.
    pub fn singleton(t: Term) -> Self {
        let mut s = BTreeSet::new();
        s.insert(t);
        TermSet(Some(Arc::new(s)))
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_none()
    }

    pub fn len(&self) -> usize {
        self.0.as_deref().map_or(0, BTreeSet::len)
    }

    pub fn contains(&self, t: &Term) -> bool {
        self.0.as_deref().is_some_and(|s| s.contains(t))
    }

    /// Iterate over hypotheses in the underlying set's order.
    pub fn iter(&self) -> Iter<'_> {
        Iter(self.0.as_deref().map(|s| s.iter()))
    }

    /// Return the `idx`-th hypothesis in iteration order, or `None`
    /// if out of range. Linear in `idx` over the underlying
    /// `BTreeSet`; used by external bindings that need indexed
    /// access (e.g. the WIT `ctx.at` accessor).
    pub fn at(&self, idx: usize) -> Option<&Term> {
        self.0.as_deref().and_then(|s| s.iter().nth(idx))
    }

    /// Return a new context with `t` added. Shares the prefix with
    /// `self` via `Arc` only as long as `self` is the sole owner;
    /// otherwise clones.
    pub fn insert(&self, t: Term) -> Self {
        match &self.0 {
            None => Self::singleton(t),
            Some(arc) => {
                if arc.contains(&t) {
                    return self.clone();
                }
                let mut s = (**arc).clone();
                s.insert(t);
                TermSet(Some(Arc::new(s)))
            }
        }
    }

    /// Return a new context without `t`. If `t` was not present,
    /// returns a clone of `self` (cheap — just an `Arc::clone`).
    pub fn remove(&self, t: &Term) -> Self {
        match &self.0 {
            None => Self::new(),
            Some(arc) => {
                if !arc.contains(t) {
                    return self.clone();
                }
                let mut s = (**arc).clone();
                s.remove(t);
                if s.is_empty() {
                    TermSet(None)
                } else {
                    TermSet(Some(Arc::new(s)))
                }
            }
        }
    }

    /// `true` iff every term in `self` is also in `other`. The
    /// empty context is a subset of every context; pointer-equal
    /// contexts short-circuit to `true`.
    pub fn is_subset(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (None, _) => true,
            (Some(_), None) => false,
            (Some(a), Some(b)) => Arc::ptr_eq(a, b) || a.is_subset(b),
        }
    }

    /// Set-theoretic union. `a.union(&empty) == empty.union(&a) ==
    /// a` is O(1) (no clone of the underlying `BTreeSet`), and
    /// `a.union(&a)` short-circuits via `Arc::ptr_eq`.
    pub fn union(&self, other: &Self) -> Self {
        match (&self.0, &other.0) {
            (None, _) => other.clone(),
            (_, None) => self.clone(),
            (Some(a), Some(b)) => {
                if Arc::ptr_eq(a, b) {
                    return self.clone();
                }
                let mut out = (**a).clone();
                out.extend(b.iter().cloned());
                TermSet(Some(Arc::new(out)))
            }
        }
    }

    /// Apply `f` to every term, returning a new context with the
    /// images. Used by `inst_tfree` and similar whole-context
    /// transformations.
    pub fn map<F: FnMut(&Term) -> Term>(&self, mut f: F) -> Self {
        match &self.0 {
            None => Self::new(),
            Some(arc) => {
                let s: BTreeSet<Term> = arc.iter().map(&mut f).collect();
                if s.is_empty() {
                    TermSet(None)
                } else {
                    TermSet(Some(Arc::new(s)))
                }
            }
        }
    }
}

impl PartialEq for TermSet {
    fn eq(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (None, None) => true,
            (None, Some(s)) | (Some(s), None) => s.is_empty(),
            (Some(a), Some(b)) => Arc::ptr_eq(a, b) || **a == **b,
        }
    }
}

impl Eq for TermSet {}

impl std::fmt::Debug for TermSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

impl<'a> IntoIterator for &'a TermSet {
    type Item = &'a Term;
    type IntoIter = Iter<'a>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl FromIterator<Term> for TermSet {
    fn from_iter<I: IntoIterator<Item = Term>>(iter: I) -> Self {
        let s: BTreeSet<Term> = iter.into_iter().collect();
        if s.is_empty() {
            TermSet(None)
        } else {
            TermSet(Some(Arc::new(s)))
        }
    }
}

/// Iterator over a [`TermSet`].
pub struct Iter<'a>(Option<std::collections::btree_set::Iter<'a, Term>>);

impl<'a> Iterator for Iter<'a> {
    type Item = &'a Term;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.as_mut().and_then(|it| it.next())
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.as_ref().map_or((0, Some(0)), |it| it.size_hint())
    }
}

impl ExactSizeIterator for Iter<'_> {
    fn len(&self) -> usize {
        self.0.as_ref().map_or(0, ExactSizeIterator::len)
    }
}
