//! Union-find storage. Phase 1 lays down the data structures and the
//! canonical-walking logic; the equality predicates `eq_at_level(_, _, k)`
//! and the union primitives land in Phase 3.

use crate::term::TermRef;
use crate::ty::{TypeInfo, TypeRef};

/// One entry in `Arena.uf_terms`, parallel to one entry in `Arena.terms`.
///
/// Each newly allocated term starts canonical-to-itself (`canonical =
/// Local(self_id)`). Unions retarget `canonical` to point at another
/// term, possibly in a foreign arena.
///
/// `type_info` carries the term's computed type (or its unbound-depth /
/// ill-typed sentinel) — see [`TypeInfo`]. Combined with `has_free`,
/// it answers "is this term closed?" in O(1).
#[derive(Debug, Clone)]
pub struct TermUfEntry {
    /// The canonical representative of this term's UF class. Points
    /// somewhere reachable from the current arena (locally or via a
    /// foreign-import Arc).
    pub canonical: TermRef,
    /// Type info for this term — `Typed(t)` when the kernel could
    /// compute the type at insertion, `Unbound(n)` when the term has
    /// `n` dangling de Bruijn indices, `IllTyped` when the term is
    /// locally closed but no typing rule applies.
    pub type_info: TypeInfo,
    /// Whether any `Free(_, _)` is reachable from this term.
    pub has_free: bool,
}

impl TermUfEntry {
    /// True iff this term is closed — no free variables and no
    /// dangling de Bruijn indices.
    pub fn closed(&self) -> bool {
        self.type_info.is_locally_closed() && !self.has_free
    }

    /// For backward-compatibility tests: the dangling-bound count.
    pub fn bound_depth(&self) -> u32 {
        self.type_info.unbound_depth()
    }
}

/// One entry in `Arena.uf_types`, parallel to one entry in `Arena.types`.
#[derive(Debug, Clone)]
pub struct TypeUfEntry {
    /// The canonical representative of this type's UF class.
    pub canonical: TypeRef,
}
