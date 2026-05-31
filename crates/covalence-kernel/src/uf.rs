//! Union-find storage. Phase 1 lays down the data structures and the
//! canonical-walking logic; the equality predicates `eq_at_level(_, _, k)`
//! and the union primitives land in Phase 3.

use crate::term::TermRef;
use crate::ty::TypeRef;

/// One entry in `Arena.uf_terms`, parallel to one entry in `Arena.terms`.
///
/// Each newly allocated term starts canonical-to-itself (`canonical =
/// Local(self_id)`). Unions retarget `canonical` to point at another
/// term, possibly in a foreign arena.
///
/// `bound_depth` and `has_free` together let us answer "is this term
/// closed?" in O(1) at every allocation: the kernel reads the children's
/// stored entries to compute the parent's, rather than re-walking the
/// whole subtree.
#[derive(Debug, Clone)]
pub struct TermUfEntry {
    /// The canonical representative of this term's UF class. Points
    /// somewhere reachable from the current arena (locally or via a
    /// foreign-import Arc).
    pub canonical: TermRef,
    /// The smallest `n` such that this term, if wrapped in `n`
    /// additional lambdas, would have no dangling `Bound(_)`. `0`
    /// means no dangling indices.
    pub bound_depth: u32,
    /// Whether any `Free(_, _)` is reachable from this term.
    pub has_free: bool,
}

impl TermUfEntry {
    /// True iff this term is closed — no free variables and no
    /// dangling de Bruijn indices.
    pub fn closed(&self) -> bool {
        self.bound_depth == 0 && !self.has_free
    }
}

/// One entry in `Arena.uf_types`, parallel to one entry in `Arena.types`.
#[derive(Debug, Clone)]
pub struct TypeUfEntry {
    /// The canonical representative of this type's UF class.
    pub canonical: TypeRef,
}
