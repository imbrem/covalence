//! Type-level data: [`TypeDef`], [`TypeRef`], [`TypeInfo`], and the
//! [`BuiltinTy`] enum of pre-defined primitive types.
//!
//! All three references ([`TypeRef`], [`TypeInfo`]) are opaque — the
//! kernel does not promise any particular byte representation.
//! Construct via the smart constructors ([`TypeRef::local`],
//! [`TypeRef::builtin`], [`TypeInfo::typed`], [`TypeInfo::ILL_TYPED`],
//! …) and pattern-match via `decode()`.

use crate::id::{StrId, TyArgsId, TypeId};

// ---------------------------------------------------------------------------
// Builtin primitive types
// ---------------------------------------------------------------------------

/// The kernel's primitive types — kernel-known, no arena allocation
/// required. Reach them via [`TypeRef::builtin`] or the convenience
/// accessors on [`Arena`](crate::Arena).
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

    pub(crate) fn from_encoded(neg: i32) -> Option<Self> {
        use BuiltinTy::*;
        Some(match neg {
            -2 => Bool,
            -3 => Bytes,
            -4 => Int,
            -5 => Nat,
            _ => return None,
        })
    }

    pub(crate) const fn encoded(self) -> i32 {
        -(self as u8 as i32)
    }
}

// ---------------------------------------------------------------------------
// Internal encoding constants (all crate-private)
// ---------------------------------------------------------------------------

/// Number of i32 slots reserved for builtin types, including the
/// IllTyped sentinel. The kernel grants itself room for a lot more
/// builtins than it currently needs.
pub(crate) const BUILTIN_SLOTS: i32 = 65536;

/// IllTyped sentinel.
const ILL_TYPED_ENCODED: i32 = -1;

/// Most-negative i32 value still interpreted as a (current or future)
/// builtin / ill-typed sentinel.
const BUILTIN_FLOOR: i32 = -BUILTIN_SLOTS;

// ---------------------------------------------------------------------------
// TypeRef
// ---------------------------------------------------------------------------

/// Reference to a type. Opaque — construct via
/// [`TypeRef::local`] / [`TypeRef::builtin`], inspect via
/// [`TypeRef::decode`] or the `is_*` / `as_*` predicates.
///
/// Foreign-arena types appear as [`TypeDef::Foreign`] structural
/// variants, not as a separate kind of `TypeRef`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TypeRef(i32);

/// Decoded view of a [`TypeRef`] — produced by [`TypeRef::decode`]
/// for pattern matching.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TypeRefKind {
    Local(TypeId),
    Builtin(BuiltinTy),
}

impl TypeRef {
    /// Build a reference to a type allocated in the current arena.
    pub fn local(id: TypeId) -> Self {
        debug_assert!(id.0 as i32 >= 0, "TypeId out of range for packed TypeRef");
        Self(id.0 as i32)
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
        self.is_allocated()
    }

    pub fn as_local(self) -> Option<TypeId> {
        self.is_local().then(|| TypeId(self.0 as u32))
    }

    pub fn as_builtin(self) -> Option<BuiltinTy> {
        BuiltinTy::from_encoded(self.0)
    }

    /// Decoded view for pattern matching.
    pub fn decode(self) -> TypeRefKind {
        if let Some(local) = self.as_local() {
            TypeRefKind::Local(local)
        } else if let Some(builtin) = self.as_builtin() {
            TypeRefKind::Builtin(builtin)
        } else {
            unreachable!("TypeRef internal encoding {} doesn't decode", self.0);
        }
    }

    pub(crate) fn from_raw(raw: i32) -> Self {
        Self(raw)
    }
}

// ---------------------------------------------------------------------------
// TypeInfo
// ---------------------------------------------------------------------------

/// Type information attached to a term at allocation time. Opaque —
/// pattern-match by calling [`TypeInfo::decode`] to get a
/// [`TypeInfoKind`], or use [`TypeInfo::is_typed`] / [`as_type`].
///
/// **Soundness note.** A term with `TypeInfoKind::IllTyped` is
/// perfectly allowed to sit in the arena; `alloc_term` never rejects.
/// Only when a `Thm` is constructed does the kernel assert that all
/// terms in the relevant arena are well-typed.
///
/// [`as_type`]: TypeInfo::as_type
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TypeInfo(i32);

impl TypeInfo {
    /// The IllTyped sentinel.
    pub const ILL_TYPED: TypeInfo = TypeInfo(ILL_TYPED_ENCODED);

    /// Build a `Typed` info from a TypeRef.
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

/// Internal storage shape of a kernel type.
///
/// `pub(crate)` so the kernel can change the representation without
/// breaking downstream callers. External consumers read types via
/// [`TypeKind`] (returned by [`Arena::type_kind`](crate::Arena::type_kind)
/// or via the opaque [`TypeRef`] handle).
///
/// The primitive variants (`Bool`, `Bytes`, `Int`, `Nat`) are
/// accepted by `alloc_type` as a convenience and dedupe to the
/// matching [`BuiltinTy`] [`TypeRef`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum TypeDef {
    // -- primitive aliases (dedupe to BuiltinTy in alloc_type) --
    Bool,
    Bytes,
    Int,
    Nat,
    // -- type formers (user-allocated) --
    /// The function type `α → β`.
    Fun(TypeRef, TypeRef),
    /// A polymorphic type variable, e.g. `'a`.
    TVar(StrId),
    /// A user-declared type constructor applied to its arguments.
    Tyapp(StrId, TyArgsId),
    /// Foreign reference: a type in an imported arena.
    Foreign(crate::id::ImportId, TypeId),
}

impl TypeDef {
    /// If this `TypeDef` is a nullary primitive, return the matching
    /// builtin. Otherwise `None`.
    pub(crate) fn as_builtin(self) -> Option<BuiltinTy> {
        Some(match self {
            TypeDef::Bool => BuiltinTy::Bool,
            TypeDef::Bytes => BuiltinTy::Bytes,
            TypeDef::Int => BuiltinTy::Int,
            TypeDef::Nat => BuiltinTy::Nat,
            _ => return None,
        })
    }
}

/// Public, stable view of a kernel type. Returned by
/// [`Arena::type_kind`](crate::Arena::type_kind).
///
/// Mirrors [`TermKind`](crate::term::TermKind) on the type side:
/// pattern-match on this rather than on the internal `TypeDef`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TypeKind {
    /// A builtin primitive type (`Bool` / `Bytes` / `Int` / `Nat`).
    Builtin(BuiltinTy),
    /// Function type `α → β`.
    Fun(TypeRef, TypeRef),
    /// Polymorphic type variable.
    TVar(StrId),
    /// User-declared type constructor applied to its arguments.
    Tyapp(StrId, TyArgsId),
    /// Foreign-arena reference.
    Foreign(crate::id::ImportId, TypeId),
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
        assert!(!r.is_builtin());
        assert_eq!(r.as_local(), Some(TypeId(42)));
        assert_eq!(r.decode(), TypeRefKind::Local(TypeId(42)));
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
