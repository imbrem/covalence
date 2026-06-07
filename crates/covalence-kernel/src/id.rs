//! Identity handles for things stored in an arena.
//!
//! [`TermId`] and [`TypeId`] are fully public — they're the natural
//! identity returned by [`alloc_term`](crate::Arena::alloc_term) /
//! [`alloc_type`](crate::Arena::alloc_type). The rest — `BytesId`,
//! `IntId`, `NatId`, `StrId`, `TyArgsId`, `ImportId` — are
//! **sealed**: the type is public so callers can hold and compare
//! them, but only the kernel can construct them. External code
//! receives these IDs from kernel methods (`intern_string`,
//! `add_import`, …) and matches on them inside `TermDef` /
//! `TypeDef` variants.

macro_rules! id_type_pub {
    ($(#[$attr:meta])* $name:ident) => {
        $(#[$attr])*
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
        pub struct $name(pub u32);
    };
}

macro_rules! id_type_sealed {
    ($(#[$attr:meta])* $name:ident) => {
        $(#[$attr])*
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
        pub struct $name(pub(crate) u32);
    };
}

id_type_pub! {
    /// Identity of a type allocated in an arena.
    TypeId
}

id_type_pub! {
    /// Identity of a term allocated in an arena.
    TermId
}

id_type_sealed! {
    /// Identity of a foreign arena imported into the current arena.
    ImportId
}

id_type_sealed! {
    /// Identity of an interned string (variable, constant, or type-
    /// variable name).
    StrId
}

id_type_sealed! {
    /// Identity of an interned byte-string literal.
    BytesId
}

id_type_sealed! {
    /// Identity of an interned arbitrary-precision integer literal.
    IntId
}

id_type_sealed! {
    /// Identity of an interned arbitrary-precision natural literal.
    NatId
}

id_type_sealed! {
    /// Identity of an interned argument list for [`TypeDef::Tyapp`](crate::TypeDef::Tyapp).
    TyArgsId
}

id_type_sealed! {
    /// Identity of a free term-variable in a [`crate::Arena`].
    ///
    /// Phase F1 (forward-compat hook): a per-arena monotonic
    /// integer that the kernel will eventually use in place of
    /// [`StrId`] inside `TermDef::Free`. The printer-facing
    /// [`StrId`] becomes a separate "display name" side-table; the
    /// `VarId` carries the identity. Not yet wired into
    /// `TermDef::Free` — see Phase F2.
    VarId
}

id_type_sealed! {
    /// Identity of a type-variable in a [`crate::Arena`].
    ///
    /// Phase F1 (forward-compat hook): a per-arena monotonic
    /// integer that will eventually replace [`StrId`] inside
    /// `TypeDef::TVar`. Not yet wired in — see Phase F2.
    TyVarId
}

id_type_sealed! {
    /// Identity of an interned term substitution (used by import edges).
    TermSubstId
}

impl TermSubstId {
    /// The reserved id for the always-empty substitution. Every
    /// [`crate::Arena`] is initialised with this slot pre-allocated.
    pub const EMPTY: Self = Self(0);
}

id_type_sealed! {
    /// Identity of an interned type substitution (used by import edges).
    TypeSubstId
}

impl TypeSubstId {
    /// The reserved id for the always-empty substitution. Every
    /// [`crate::Arena`] is initialised with this slot pre-allocated.
    pub const EMPTY: Self = Self(0);
}
