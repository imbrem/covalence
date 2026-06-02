//! Type-level data: `TypeDef`, `TypeRef`, `TypeInfo`, and the
//! `BuiltinTy` enum of pre-defined primitive types.
//!
//! ## Encoding sketch (i32, packed)
//!
//! Both [`TypeRef`] and [`TypeInfo`] are i32 newtypes. The
//! representation is **fully encapsulated** — callers go through
//! `decode()` for pattern matching and the smart constructors
//! (`local`, `foreign`, `builtin`, `typed`, `unbound`, `ILL_TYPED`)
//! for construction. The raw integer is an implementation detail.
//!
//! ```text
//! i32 range                          Meaning
//! ─────────────────────────────────────────────────────────────────
//! 0 ..= i32::MAX                     Allocated type. Bit 30 = foreign,
//!                                    bits 0..29 = id.
//! -1                                 IllTyped sentinel (also the
//!                                    "first builtin slot").
//! -2 ..= -BuiltinTy::COUNT - 1       Current builtin types (Bool=-2,
//!                                    Bytes=-3, Int=-4, Nat=-5).
//! -BuiltinTy::COUNT - 2 ..= -65536   Reserved builtin slots for future
//!                                    additions.
//! -65537 ..= i32::MIN                Unbound depth: Unbound(n) = -65537 - n.
//! ```
//!
//! So **every TypeRef is also a valid `TypeInfo::Typed(...)`** —
//! the same i32 value works for both.

use crate::id::{ForeignTypeId, StrId, TyArgsId, TypeId};

// ---------------------------------------------------------------------------
// Builtin primitive types
// ---------------------------------------------------------------------------

/// The kernel's primitive types — kernel-known, no arena allocation
/// required.
///
/// Each variant encodes as a small negative integer (-2 for `Bool`,
/// -3 for `Bytes`, -4 for `Int`, -5 for `Nat`). The slot at -1 is
/// reserved for [`TypeInfo::ILL_TYPED`]; future builtins (Bits and
/// fixed-width ints will return) can be added in slots up to
/// [`BUILTIN_SLOTS`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[repr(u8)]
pub enum BuiltinTy {
    Bool = 2,
    Bytes = 3,
    Int = 4,
    Nat = 5,
}

impl BuiltinTy {
    /// Number of builtin types currently defined.
    pub const COUNT: u8 = 4;

    /// Decode from the small-negative encoding (`-2..=-(COUNT + 1)`).
    pub fn from_encoded(neg: i32) -> Option<Self> {
        use BuiltinTy::*;
        Some(match neg {
            -2 => Bool,
            -3 => Bytes,
            -4 => Int,
            -5 => Nat,
            _ => return None,
        })
    }

    /// Encode as the small-negative TypeRef/TypeInfo value.
    pub const fn encoded(self) -> i32 {
        -(self as u8 as i32)
    }
}

// ---------------------------------------------------------------------------
// Encoding constants
// ---------------------------------------------------------------------------

/// Number of i32 slots reserved for builtin types, including the
/// [`TypeInfo::ILL_TYPED`] sentinel at slot -1. The kernel grants
/// itself room for a lot more builtins than it currently needs.
pub const BUILTIN_SLOTS: i32 = 65536;

/// IllTyped sentinel — slot -1, the first reserved builtin slot.
const ILL_TYPED_ENCODED: i32 = -1;

/// Most-negative i32 value still interpreted as a (current or future)
/// builtin / ill-typed sentinel.
const BUILTIN_FLOOR: i32 = -BUILTIN_SLOTS;

/// Bit 30 of the positive (allocated) range marks foreign refs.
const FOREIGN_FLAG_BIT: i32 = 1 << 30;
/// Mask for the id within the allocated range (bits 0..29).
const ALLOC_ID_MASK: i32 = FOREIGN_FLAG_BIT - 1;

// ---------------------------------------------------------------------------
// TypeRef
// ---------------------------------------------------------------------------

/// Reference to a type. Packed i32 — opaque to callers; construct via
/// [`TypeRef::local`] / [`TypeRef::foreign`] / [`TypeRef::builtin`],
/// inspect via [`TypeRef::decode`] or the `is_*`/`as_*` predicates.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TypeRef(i32);

/// Decoded view of a [`TypeRef`] — produced by [`TypeRef::decode`]
/// for pattern matching.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TypeRefKind {
    Local(TypeId),
    Foreign(ForeignTypeId),
    Builtin(BuiltinTy),
}

impl TypeRef {
    /// Build a local reference. Panics in debug builds if `id` exceeds 2^30 - 1.
    pub fn local(id: TypeId) -> Self {
        debug_assert!(
            id.0 <= ALLOC_ID_MASK as u32,
            "TypeId out of range for packed TypeRef"
        );
        Self(id.0 as i32)
    }

    /// Build a foreign reference. Panics in debug builds if `id` exceeds 2^30 - 1.
    pub fn foreign(id: ForeignTypeId) -> Self {
        debug_assert!(
            id.0 <= ALLOC_ID_MASK as u32,
            "ForeignTypeId out of range for packed TypeRef"
        );
        Self((id.0 as i32) | FOREIGN_FLAG_BIT)
    }

    /// Build a reference to a builtin primitive type.
    pub const fn builtin(ty: BuiltinTy) -> Self {
        Self(ty.encoded())
    }

    pub fn is_builtin(self) -> bool {
        self.0 < 0 && self.0 >= BUILTIN_FLOOR && self.0 != ILL_TYPED_ENCODED
    }

    pub fn is_allocated(self) -> bool {
        self.0 >= 0
    }

    pub fn is_local(self) -> bool {
        self.is_allocated() && (self.0 & FOREIGN_FLAG_BIT) == 0
    }

    pub fn is_foreign(self) -> bool {
        self.is_allocated() && (self.0 & FOREIGN_FLAG_BIT) != 0
    }

    pub fn as_local(self) -> Option<TypeId> {
        self.is_local().then(|| TypeId((self.0 & ALLOC_ID_MASK) as u32))
    }

    pub fn as_foreign(self) -> Option<ForeignTypeId> {
        self.is_foreign()
            .then(|| ForeignTypeId((self.0 & ALLOC_ID_MASK) as u32))
    }

    pub fn as_builtin(self) -> Option<BuiltinTy> {
        BuiltinTy::from_encoded(self.0)
    }

    /// Decoded view for pattern matching.
    pub fn decode(self) -> TypeRefKind {
        if let Some(local) = self.as_local() {
            TypeRefKind::Local(local)
        } else if let Some(foreign) = self.as_foreign() {
            TypeRefKind::Foreign(foreign)
        } else if let Some(builtin) = self.as_builtin() {
            TypeRefKind::Builtin(builtin)
        } else {
            // Hitting this means the i32 is in a reserved range we
            // haven't assigned (e.g., a future-builtin slot or the
            // IllTyped sentinel — but only the TypeInfo wrapper
            // should hold IllTyped). Treat as builtin for robustness.
            unreachable!("TypeRef i32 value {} doesn't decode", self.0);
        }
    }

    /// The raw i32 representation (for serialisation / debugging).
    pub fn to_raw(self) -> i32 {
        self.0
    }

    /// Wrap a raw i32. Caller asserts it's a valid TypeRef encoding.
    pub fn from_raw(raw: i32) -> Self {
        Self(raw)
    }
}

// ---------------------------------------------------------------------------
// TypeInfo
// ---------------------------------------------------------------------------

/// Type information attached to a term at allocation time. Opaque
/// i32 — see module-level encoding sketch. Pattern-match by calling
/// [`TypeInfo::decode`] to get a [`TypeInfoKind`].
///
/// **Soundness note.** A term with `TypeInfoKind::IllTyped` is
/// perfectly allowed to sit in the arena; `alloc_term` never rejects.
/// Only when a `Thm` is constructed does the kernel assert that all
/// terms in the relevant arena are well-typed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TypeInfo(i32);

impl TypeInfo {
    /// The IllTyped sentinel — slot -1 in the builtin range.
    pub const ILL_TYPED: TypeInfo = TypeInfo(ILL_TYPED_ENCODED);

    /// Build a `Typed` info from a TypeRef. Every TypeRef encoding is
    /// also a valid TypeInfo encoding.
    pub const fn typed(t: TypeRef) -> Self {
        Self(t.0)
    }

    /// Build an `Unbound(n)` info.
    pub fn unbound(n: u32) -> Self {
        let encoded = BUILTIN_FLOOR - 1 - (n as i32);
        debug_assert!(encoded >= i32::MIN, "unbound depth overflow");
        Self(encoded)
    }

    /// True iff the term has a known type (allocated or builtin).
    pub fn is_typed(self) -> bool {
        self.is_allocated() || self.as_builtin().is_some()
    }

    fn is_allocated(self) -> bool {
        self.0 >= 0
    }

    /// True iff this is the IllTyped sentinel.
    pub fn is_ill_typed(self) -> bool {
        self.0 == ILL_TYPED_ENCODED
    }

    /// True iff the term is locally closed — typed, ill-typed, or
    /// `Unbound(0)` qualifies. Only `Unbound(n > 0)` is open.
    pub fn is_locally_closed(self) -> bool {
        self.is_typed() || self.is_ill_typed() || self.unbound_depth() == 0
    }

    /// Returns the term's type if known.
    pub fn as_type(self) -> Option<TypeRef> {
        if self.is_typed() {
            Some(TypeRef::from_raw(self.0))
        } else {
            None
        }
    }

    fn as_builtin(self) -> Option<BuiltinTy> {
        BuiltinTy::from_encoded(self.0)
    }

    /// Dangling-bound count for an Unbound info; `0` for typed or
    /// ill-typed.
    pub fn unbound_depth(self) -> u32 {
        if self.0 < BUILTIN_FLOOR {
            (BUILTIN_FLOOR - 1 - self.0) as u32
        } else {
            0
        }
    }

    /// Decoded view for pattern matching.
    pub fn decode(self) -> TypeInfoKind {
        if self.is_ill_typed() {
            TypeInfoKind::IllTyped
        } else if self.is_typed() {
            TypeInfoKind::Typed(TypeRef::from_raw(self.0))
        } else {
            TypeInfoKind::Unbound(self.unbound_depth())
        }
    }
}

impl From<TypeRef> for TypeInfo {
    fn from(t: TypeRef) -> Self {
        TypeInfo::typed(t)
    }
}

/// Decoded view of a [`TypeInfo`] — produced by [`TypeInfo::decode`]
/// for pattern matching.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TypeInfoKind {
    Typed(TypeRef),
    Unbound(u32),
    IllTyped,
}

// ---------------------------------------------------------------------------
// TypeDef
// ---------------------------------------------------------------------------

/// The kernel's type language. Stored in `arena.types` for
/// **user-allocated** types only — primitive types live as
/// [`BuiltinTy`] inside [`TypeRef`] and never get an arena entry.
///
/// The primitive variants here (`Bool`, `Bytes`, `Int`, `Nat`) are accepted by
/// [`alloc_type`](crate::arena::Arena::alloc_type) for convenience;
/// the call returns the matching builtin TypeRef without writing to
/// `arena.types`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TypeDef {
    // -- primitive aliases (dedupe to BuiltinTy in alloc_type) --
    Bool,
    Bytes,
    Int,
    Nat,
    // -- type formers (user-allocated) --
    /// The function type `α → β`. Stored in `arena.types`.
    Fun(TypeRef, TypeRef),
    /// A polymorphic type variable, e.g. `'a` — name interned in
    /// `arena.strings`.
    TVar(StrId),
    /// A user-declared type constructor applied to its arguments.
    Tyapp(StrId, TyArgsId),
}

impl TypeDef {
    /// If this `TypeDef` is a nullary primitive, return the matching
    /// builtin. Otherwise `None`.
    pub fn as_builtin(self) -> Option<BuiltinTy> {
        Some(match self {
            TypeDef::Bool => BuiltinTy::Bool,
            TypeDef::Bytes => BuiltinTy::Bytes,
            TypeDef::Int => BuiltinTy::Int,
            TypeDef::Nat => BuiltinTy::Nat,
            _ => return None,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn builtin_typeref_roundtrip() {
        for ty in [
            BuiltinTy::Bool,
            BuiltinTy::Bytes,
            BuiltinTy::Int,
            BuiltinTy::Nat,
        ] {
            let r = TypeRef::builtin(ty);
            assert!(r.is_builtin());
            assert!(!r.is_allocated());
            assert_eq!(r.as_builtin(), Some(ty));
            assert_eq!(r.decode(), TypeRefKind::Builtin(ty));
        }
    }

    #[test]
    fn local_typeref_roundtrip() {
        let r = TypeRef::local(TypeId(42));
        assert!(r.is_local());
        assert!(!r.is_foreign());
        assert!(!r.is_builtin());
        assert_eq!(r.as_local(), Some(TypeId(42)));
        assert_eq!(r.decode(), TypeRefKind::Local(TypeId(42)));
    }

    #[test]
    fn foreign_typeref_roundtrip() {
        let r = TypeRef::foreign(ForeignTypeId(7));
        assert!(r.is_foreign());
        assert_eq!(r.as_foreign(), Some(ForeignTypeId(7)));
        assert_eq!(r.decode(), TypeRefKind::Foreign(ForeignTypeId(7)));
    }

    #[test]
    fn typeinfo_typed_via_typeref() {
        let info = TypeInfo::typed(TypeRef::builtin(BuiltinTy::Bool));
        assert!(info.is_typed());
        assert_eq!(info.as_type(), Some(TypeRef::builtin(BuiltinTy::Bool)));
        assert_eq!(
            info.decode(),
            TypeInfoKind::Typed(TypeRef::builtin(BuiltinTy::Bool))
        );
    }

    #[test]
    fn typeinfo_unbound_roundtrip() {
        for n in [0u32, 1, 3, 100, 65535] {
            let info = TypeInfo::unbound(n);
            assert!(!info.is_typed());
            assert!(!info.is_ill_typed());
            assert_eq!(info.unbound_depth(), n);
            assert_eq!(info.decode(), TypeInfoKind::Unbound(n));
        }
    }

    #[test]
    fn typeinfo_ill_typed() {
        let info = TypeInfo::ILL_TYPED;
        assert!(info.is_ill_typed());
        assert!(!info.is_typed());
        assert!(info.is_locally_closed());
        assert_eq!(info.decode(), TypeInfoKind::IllTyped);
    }

    #[test]
    fn typeinfo_one_i32() {
        assert_eq!(std::mem::size_of::<TypeInfo>(), 4);
        assert_eq!(std::mem::size_of::<TypeRef>(), 4);
    }
}
