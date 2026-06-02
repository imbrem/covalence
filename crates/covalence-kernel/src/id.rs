//! Identity handles for things stored in an arena.
//!
//! [`TermId`] and [`TypeId`] are fully public — they're the natural
//! identity returned by [`alloc_term`](crate::Arena::alloc_term) /
//! [`alloc_type`](crate::Arena::alloc_type). The rest — `BytesId`,
//! `IntId`, `NatId`, `StrId`, `TyArgsId`, `ImportId`, `ForeignTermId`,
//! `ForeignTypeId` — are **sealed**: the type is public so callers
//! can hold and compare them, but only the kernel can construct
//! them. External code receives these IDs from kernel methods
//! (`intern_string`, `add_import`, …) and matches on them inside
//! `TermDef` / `TypeDef` variants.

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
    /// Foreign-term handle — paired with an [`ImportId`] inside the
    /// arena to resolve to a term in the imported arena.
    ForeignTermId
}

id_type_sealed! {
    /// Foreign-type handle — paired with an [`ImportId`] inside the
    /// arena to resolve to a type in the imported arena.
    ForeignTypeId
}
