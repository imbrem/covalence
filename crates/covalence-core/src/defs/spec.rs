//! `TypeSpec` and `TermSpec` — symbol-tagged definitions of the
//! kernel's derived types and term constants.
//!
//! Both are opaque process-shared handles (a single `Arc` internally)
//! pairing an `Arc<dyn Symbol>` with an optional `Type` and an
//! optional `Term`. The *meaning* of the four representable shapes
//! is:
//!
//! | Shape                         | English notation                  |
//! |-------------------------------|-----------------------------------|
//! | `ty = Some, tm = Some(λ_. T)` | `def name args := ty`             |
//! | `ty = Some, tm = Some(pred)`  | `def name args := ty where pred`  |
//! | `ty = Some, tm = Some(rel)`   | `def name args := { car } close rel` |
//! | `ty = None,  tm = Some(t)`    | `let name args := t`              |
//!
//! See `docs/type-hierarchy.md` for the full intended catalogue.

use std::hash::Hash;
use std::sync::Arc;

use crate::term::{Term, Type};

use super::symbol::{Opacity, Symbol};

// ============================================================================
// Inner representation (private)
// ============================================================================

struct TypeSpecInner {
    symbol: Arc<dyn Symbol>,
    ty: Option<Type>,
    tm: Option<Term>,
}

impl std::fmt::Debug for TypeSpecInner {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TypeSpec")
            .field("symbol", &self.symbol.label())
            .field("ty", &self.ty)
            .field("tm", &self.tm)
            .finish()
    }
}

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

// ============================================================================
// TypeSpec
// ============================================================================

/// An opaque, process-shared handle to a type-spec definition.
///
/// Use [`Self::new`] to construct; the inner representation
/// (symbol/ty/tm) is private. Access via [`Self::symbol`],
/// [`Self::ty`], [`Self::tm`]. Cheap to clone (one `Arc` bump);
/// identity-comparable via [`Self::ptr_eq`].
#[derive(Debug, Clone)]
pub struct TypeSpec(Arc<TypeSpecInner>);

impl TypeSpec {
    /// Build a new type-spec with the given symbol, carrier, and
    /// predicate/body. The symbol can be any `Symbol` impl — typically
    /// [`super::Canonical`] for kernel-shipped definitions or
    /// `SmolStr` for user-supplied names.
    pub fn new<S: Symbol>(symbol: S, ty: Option<Type>, tm: Option<Term>) -> Self {
        Self(Arc::new(TypeSpecInner {
            symbol: Arc::new(symbol),
            ty,
            tm,
        }))
    }

    /// The spec's symbol, as a `&dyn Symbol`. Call `.label()` for
    /// display / serialisation, or `.opacity()` to inspect the
    /// equality contract.
    pub fn symbol(&self) -> &dyn Symbol {
        &*self.0.symbol
    }

    /// The carrier type, if present.
    pub fn ty(&self) -> Option<&Type> {
        self.0.ty.as_ref()
    }

    /// The predicate / body term, if present.
    pub fn tm(&self) -> Option<&Term> {
        self.0.tm.as_ref()
    }

    /// `true` iff `self` and `other` share the same underlying
    /// allocation. Two handles from the same catalogue lazy static
    /// always pointer-equal.
    pub fn ptr_eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }

    /// Stable integer identity for the underlying allocation. Used
    /// as a cache key outside the TCB (display, serialisation).
    pub fn ptr_id(&self) -> usize {
        Arc::as_ptr(&self.0) as *const () as usize
    }
}

impl PartialEq for TypeSpec {
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

impl Eq for TypeSpec {}

impl PartialOrd for TypeSpec {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for TypeSpec {
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

impl std::hash::Hash for TypeSpec {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        symbol_hash(&*self.0.symbol, state);
        self.0.ty.hash(state);
        self.0.tm.hash(state);
    }
}

// ============================================================================
// TermSpec
// ============================================================================

/// An opaque, process-shared handle to a term-spec definition.
///
/// Same shape as [`TypeSpec`], but for the term-level catalogue
/// (`natAdd`, `listMap`, …). Reduction (`Thm::reduce_prim` and
/// successors) recognises a `TermKind::Spec(h, args)` leaf by
/// `h.ptr_eq(&catalogue_handle)` — pointer identity on the
/// underlying `Arc`.
#[derive(Debug, Clone)]
pub struct TermSpec(Arc<TermSpecInner>);

impl TermSpec {
    /// Build a new term-spec with the given symbol, type, and
    /// selector predicate.
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

// ============================================================================
// Symbol comparison / hash helpers
// ============================================================================

/// Structural equality of two `dyn Symbol`s, respecting opacity.
fn symbol_eq(a: &dyn Symbol, b: &dyn Symbol) -> bool {
    match (a.opacity(), b.opacity()) {
        (Opacity::Transparent, Opacity::Transparent) => true,
        (Opacity::Opaque, Opacity::Opaque) => a.label() == b.label(),
        // Mixed opacity: never equal — a transparent and an opaque
        // symbol carry different equality contracts.
        _ => false,
    }
}

fn symbol_cmp(a: &dyn Symbol, b: &dyn Symbol) -> std::cmp::Ordering {
    // Order: transparent < opaque (so the catalogue sorts predictably
    // ahead of user-named entries). Within a class, by label.
    fn rank(o: Opacity) -> u8 {
        match o {
            Opacity::Transparent => 0,
            Opacity::Opaque => 1,
        }
    }
    rank(a.opacity())
        .cmp(&rank(b.opacity()))
        .then_with(|| a.label().cmp(b.label()))
}

fn symbol_hash<H: std::hash::Hasher>(s: &dyn Symbol, state: &mut H) {
    // Hash the opacity tag so transparent and opaque hash into
    // disjoint buckets; for opaque names, fold in the label.
    let tag: u8 = match s.opacity() {
        Opacity::Transparent => 0,
        Opacity::Opaque => 1,
    };
    state.write_u8(tag);
    if matches!(s.opacity(), Opacity::Opaque) {
        s.label().hash(state);
    }
}
