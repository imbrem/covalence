//! E-graph: an [`Arena`] paired with its [`TermUf`].
//!
//! In the kernel's data model an E-graph is the structural state
//! (terms, types, interned literals — held by `Arena`) together with
//! the equality state (canonical pointers — held by `TermUf`).
//!
//! `Egraph` is the unit of "proof environment" that Phase P moves
//! into the [`crate::Prop`] struct, so that a proposition can be a
//! single value rather than a tuple of references. For now it's a
//! thin wrapper with both fields `pub` — callers can keep using the
//! underlying `arena` / `uf` directly during the migration.

use crate::arena::{Arena, UnionError};
use crate::term::{TermDef, TermRef};
use crate::uf::TermUf;

/// An E-graph: arena (structural state) + union-find (equality state).
///
/// The arena's `alloc_term` does not dedupe, so callers that need a
/// stable canonical handle for repeated values (most commonly
/// `Bool(true)`) should go through [`Egraph::true_ref`] /
/// [`Egraph::false_ref`] — these find-or-allocate and cache.
#[derive(Debug, Clone, Default)]
pub struct Egraph {
    pub arena: Arena,
    pub uf: TermUf,
    /// Cached `TermRef` of the canonical `Bool(true)` leaf. Lazily
    /// initialised by [`Egraph::true_ref`].
    cached_true: Option<TermRef>,
    /// Cached `TermRef` of the canonical `Bool(false)` leaf. Lazily
    /// initialised by [`Egraph::false_ref`].
    cached_false: Option<TermRef>,
}

impl Egraph {
    /// Build an empty E-graph.
    pub fn new() -> Self {
        Self::default()
    }

    /// Same-canonical check (level 0).
    pub fn eq_at_level_0(&self, a: TermRef, b: TermRef) -> bool {
        self.uf.eq_at_level_0(a, b)
    }

    /// Union two terms in the UF.
    pub fn union(&mut self, a: TermRef, b: TermRef) -> Result<(), UnionError> {
        self.uf.union(a, b)
    }

    /// Canonical handle for `Bool(true)` — the union target every
    /// inference rule uses to mark a term as known-true. Lazily
    /// allocates on first call; subsequent calls return the same ref
    /// so UF unions against truth land in one equivalence class.
    pub fn true_ref(&mut self) -> TermRef {
        if let Some(r) = self.cached_true {
            return r;
        }
        let r = TermRef::local(self.arena.alloc_term(TermDef::Bool(true)));
        self.cached_true = Some(r);
        r
    }

    /// Canonical handle for `Bool(false)`. Lazy, like
    /// [`true_ref`](Self::true_ref).
    pub fn false_ref(&mut self) -> TermRef {
        if let Some(r) = self.cached_false {
            return r;
        }
        let r = TermRef::local(self.arena.alloc_term(TermDef::Bool(false)));
        self.cached_false = Some(r);
        r
    }
}
