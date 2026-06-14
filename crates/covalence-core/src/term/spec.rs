//! `TermSpec` — the symbol-tagged definition of a kernel term constant.
//!
//! An opaque, process-shared handle (a single `Arc` internally)
//! pairing an `Arc<dyn Symbol>` with an optional `Type` and an optional
//! body/predicate `Term`. Same shape as [`crate::ty::TypeSpec`], but
//! for the term-level catalogue (`nat.add`, `list.map`, …). Reduction
//! (`Thm::reduce_prim` and successors) recognises a `TermKind::Spec(h,
//! args)` leaf by `h.ptr_eq(&catalogue_handle)` — pointer identity on
//! the underlying `Arc`.

use std::sync::Arc;

use crate::defs::symbol::{Symbol, symbol_cmp, symbol_eq, symbol_hash};
use crate::ty::Type;

use super::Term;

struct TermSpecInner {
    symbol: Arc<dyn Symbol>,
    ty: Option<Type>,
    tm: Option<Term>,
}

impl std::fmt::Debug for TermSpecInner {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TermSpec")
            .field("symbol", &self.symbol.label())
            .field("ty", &self.ty)
            .field("tm", &self.tm)
            .finish()
    }
}

/// An opaque, process-shared handle to a term-spec definition.
#[derive(Debug, Clone)]
pub struct TermSpec(Arc<TermSpecInner>);

impl TermSpec {
    /// Build a new term-spec with the given symbol, type, and
    /// body / selector predicate.
    pub fn new<S: Symbol>(symbol: S, ty: Option<Type>, tm: Option<Term>) -> Self {
        Self(Arc::new(TermSpecInner {
            symbol: Arc::new(symbol),
            ty,
            tm,
        }))
    }

    pub fn symbol(&self) -> &dyn Symbol {
        &*self.0.symbol
    }

    pub fn ty(&self) -> Option<&Type> {
        self.0.ty.as_ref()
    }

    pub fn tm(&self) -> Option<&Term> {
        self.0.tm.as_ref()
    }

    pub fn ptr_eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }

    pub fn ptr_id(&self) -> usize {
        Arc::as_ptr(&self.0) as *const () as usize
    }
}

impl PartialEq for TermSpec {
    fn eq(&self, other: &Self) -> bool {
        if Arc::ptr_eq(&self.0, &other.0) {
            return true;
        }
        let a = &*self.0;
        let b = &*other.0;
        if a.ty != b.ty || a.tm != b.tm {
            return false;
        }
        symbol_eq(&*a.symbol, &*b.symbol)
    }
}

impl Eq for TermSpec {}

impl PartialOrd for TermSpec {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for TermSpec {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if Arc::ptr_eq(&self.0, &other.0) {
            return std::cmp::Ordering::Equal;
        }
        let a = &*self.0;
        let b = &*other.0;
        symbol_cmp(&*a.symbol, &*b.symbol)
            .then_with(|| a.ty.cmp(&b.ty))
            .then_with(|| a.tm.cmp(&b.tm))
    }
}

impl std::hash::Hash for TermSpec {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        symbol_hash(&*self.0.symbol, state);
        self.0.ty.hash(state);
        self.0.tm.hash(state);
    }
}
