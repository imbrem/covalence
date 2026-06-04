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
use crate::term::TermRef;
use crate::uf::TermUf;

/// An E-graph: arena (structural state) + union-find (equality state).
#[derive(Debug, Clone, Default)]
pub struct Egraph {
    pub arena: Arena,
    pub uf: TermUf,
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
}
