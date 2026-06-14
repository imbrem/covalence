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

use super::symbol::Symbol;

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
    /// A **subtype**: the carrier type `carrier` carved down by a
    /// selector predicate `pred : carrier → bool` (Hilbert-ε style —
    /// the type denotes `{ x : carrier | pred x }`). Most kernel types
    /// are built via this or [`Self::newtype`]; we expose those two
    /// intents rather than the raw `(Option, Option)` shape so the
    /// representation can change/extend later.
    pub fn subtype<S: Symbol>(symbol: S, carrier: Type, pred: Term) -> Self {
        Self::raw(symbol, Some(carrier), Some(pred))
    }

    /// A **newtype**: a fresh symbol over `base` with the trivial
    /// (always-true) predicate — `newtype S base` is isomorphic to
    /// `base` but a distinct type (e.g. `result a b := coprod a b`,
    /// `u8 := prod u4 u4`).
    pub fn newtype<S: Symbol>(symbol: S, base: Type) -> Self {
        let pred = super::helpers::any(&base);
        Self::raw(symbol, Some(base), Some(pred))
    }

    /// Raw constructor (escape hatch — prefer [`Self::subtype`] /
    /// [`Self::newtype`]). Used for the few specs that need an absent
    /// carrier or body.
    pub(super) fn raw<S: Symbol>(symbol: S, ty: Option<Type>, tm: Option<Term>) -> Self {
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
        symbol_eq(&*self.0.symbol, &*self.0.symbol)
            && self.0.ty == self.0.ty
            && self.0.tm == self.0.tm
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

/// Structural equality of two `dyn Symbol`s
fn symbol_eq(a: &dyn Symbol, b: &dyn Symbol) -> bool {
    // TODO: generalize
    std::ptr::addr_eq(a, b)
}

fn symbol_cmp(a: &dyn Symbol, b: &dyn Symbol) -> std::cmp::Ordering {
    // TODO: generalize
    (a as *const dyn Symbol)
        .cast::<()>()
        .cmp(&(b as *const dyn Symbol).cast::<()>())
}

fn symbol_hash<H: std::hash::Hasher>(s: &dyn Symbol, state: &mut H) {
    // TODO: generlaize
    s.label().hash(state)
}
