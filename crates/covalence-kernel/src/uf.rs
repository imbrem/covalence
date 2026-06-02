//! Union-find storage for term equality.

use crate::term::TermRef;
use crate::ty::TypeInfo;

/// One UF entry per allocated term.
///
/// Each newly allocated term starts canonical-to-itself (`canonical =
/// Local(self_id)`). Unions retarget `canonical` to point at another
/// term, possibly in a foreign arena.
#[derive(Debug, Clone)]
pub struct TermUfEntry {
    /// The canonical representative of this term's UF class.
    pub canonical: TermRef,
    /// Type info computed at insertion — `Typed(t)`, `Unbound(n)`,
    /// or `IllTyped`.
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
