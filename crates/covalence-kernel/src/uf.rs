//! Term-level union-find. Lives **outside** the arena — see
//! [`TermUf`].

use crate::arena::{Arena, UnionError};
use crate::id::TermId;
use crate::term::{Deps, TermRef};
use crate::ty::TypeInfo;

/// Cached structural properties of one allocated term in the arena.
///
/// These are derived from the term's [`TermDef`] at allocation time
/// (`alloc_term`) and don't change unless the def is rewritten — they
/// are **not** equality state and stay on the arena even when the UF
/// is external.
#[derive(Debug, Clone, Copy)]
pub struct TermProps {
    /// Computed type info — `Typed(t)`, `Unbound(n)`, or `IllTyped`.
    pub type_info: TypeInfo,
    /// Whether any `Free(_, _)` is reachable from this term.
    pub has_free: bool,
}

impl TermProps {
    /// True iff this term is closed — no free variables and no
    /// dangling de Bruijn indices.
    pub fn closed(&self) -> bool {
        self.type_info.is_locally_closed() && !self.has_free
    }

    /// Dangling-bound count. `0` for typed or ill-typed.
    pub fn bound_depth(&self) -> u32 {
        self.type_info.unbound_depth()
    }
}

/// Term-level union-find over an [`Arena`].
///
/// External to the arena. A `TermUf` holds a `Vec<TermRef>` of
/// canonical pointers indexed by [`TermId`]. Arenas can be queried,
/// frozen, and imported without touching equality state; many UFs
/// can coexist over the same arena.
///
/// Terms beyond `canonicals.len()` are **implicitly self-canonical**
/// — there's no need to allocate one entry per term up front. Unions
/// grow the vec lazily as needed.
#[derive(Debug, Clone, Default)]
pub struct TermUf {
    /// Canonicals indexed by `TermId`. Entries beyond `.len()` are
    /// implicitly self-canonical.
    canonicals: Vec<TermRef>,
}

impl TermUf {
    /// Build an empty UF — every term is its own canonical.
    pub fn new() -> Self {
        Self::default()
    }

    /// The canonical for `id` (or `id` itself if no union has touched
    /// it).
    fn stored(&self, id: TermId) -> TermRef {
        let i = id.0 as usize;
        if i < self.canonicals.len() {
            self.canonicals[i]
        } else {
            TermRef::local(id)
        }
    }

    fn ensure_len(&mut self, len: usize) {
        while self.canonicals.len() < len {
            let id = TermId(self.canonicals.len() as u32);
            self.canonicals.push(TermRef::local(id));
        }
    }

    /// Walk `r`'s canonical chain to its self-canonical landing. The
    /// returned ref is a [`TermRef`] inside the same arena.
    pub fn canonical_local(&self, r: TermRef) -> TermRef {
        let mut cur = r;
        loop {
            let id = match cur.as_local() {
                Some(id) => id,
                None => return cur,
            };
            let next = self.stored(id);
            if next == cur {
                return cur;
            }
            cur = next;
        }
    }

    /// Record an equality between two terms. Updates one side's
    /// canonical to point at the other.
    pub fn union(&mut self, a: TermRef, b: TermRef) -> Result<(), UnionError> {
        let a_canon = self.canonical_local(a);
        let b_canon = self.canonical_local(b);
        if a_canon == b_canon {
            return Ok(());
        }
        if let Some(a_local) = a_canon.as_local() {
            self.ensure_len((a_local.0 as usize) + 1);
            self.canonicals[a_local.0 as usize] = b_canon;
            return Ok(());
        }
        if let Some(b_local) = b_canon.as_local() {
            self.ensure_len((b_local.0 as usize) + 1);
            self.canonicals[b_local.0 as usize] = a_canon;
            return Ok(());
        }
        Err(UnionError::BothForeign)
    }

    /// Same-canonical check — level 0 of the equality family.
    pub fn eq_at_level_0(&self, a: TermRef, b: TermRef) -> bool {
        self.canonical_local(a) == self.canonical_local(b)
    }

    /// Are `a` and `b` known equal at congruence level `d`?
    ///
    /// - `d = 0`: same canonical.
    /// - `d = n > 0`: same `TermDef` shape (variant + non-dep payload)
    ///   with each pair of `TermRef` deps `eq_at_level(_, _, d - 1)`.
    pub fn eq_at_level(
        &self,
        arena: &Arena,
        a: TermRef,
        b: TermRef,
        depth: u32,
    ) -> bool {
        let a_canon = self.canonical_local(a);
        let b_canon = self.canonical_local(b);
        if a_canon == b_canon {
            return true;
        }
        if depth == 0 {
            return false;
        }
        let (Some(a_local), Some(b_local)) = (a_canon.as_local(), b_canon.as_local()) else {
            return false;
        };
        let a_def = *arena.term_def(a_local);
        let b_def = *arena.term_def(b_local);
        let sentinel = TermRef::from_raw(0);
        if a_def.with_zeroed_deps(sentinel) != b_def.with_zeroed_deps(sentinel) {
            return false;
        }
        let cdepth = depth - 1;
        match (a_def.deps(), b_def.deps()) {
            (Deps::None, Deps::None) => true,
            (Deps::One(x), Deps::One(y)) => self.eq_at_level(arena, x, y, cdepth),
            (Deps::Two(x1, x2), Deps::Two(y1, y2)) => {
                self.eq_at_level(arena, x1, y1, cdepth)
                    && self.eq_at_level(arena, x2, y2, cdepth)
            }
            _ => unreachable!("shape-equal defs must have matching dep arity"),
        }
    }

    /// If `a` and `b` are congruent at the requested depth, union
    /// them and return `true`. Otherwise return `false`.
    pub fn union_if_congruent(
        &mut self,
        arena: &Arena,
        a: TermRef,
        b: TermRef,
        depth: u32,
    ) -> Result<bool, UnionError> {
        if !self.eq_at_level(arena, a, b, depth) {
            return Ok(false);
        }
        self.union(a, b)?;
        Ok(true)
    }
}
