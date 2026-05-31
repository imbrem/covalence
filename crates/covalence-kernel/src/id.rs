//! Index handles into the Arena's internal tables.
//!
//! Every variant is `Copy` and `u32`-sized — that's what lets `TermRef` and
//! `TypeRef` (and through them `TermDef` / `TypeDef`) stay `Copy`. The
//! variable-sized payloads (names, byte strings, big-ints, type-arg lists,
//! foreign arenas) live in per-arena interning tables and are referenced
//! by these handles.
//!
//! Sealing policy: `TermId` and `TypeId` are fully public (the natural
//! identity of a term / type the user receives from `alloc_term` /
//! `alloc_type`). The rest — `BitsId`, `BytesId`, `IntId`, `NatId`,
//! `StrId`, `TyArgsId`, `ImportId`, `ForeignTermId`, `ForeignTypeId` —
//! are **sealed**: the type is public so callers can hold and compare
//! them, but the inner u32 is `pub(crate)`, so only the kernel can
//! construct them. External code receives these IDs from kernel methods
//! (`intern_string`, `add_import`, …) and matches on them inside
//! `TermDef` / `TypeDef` variants without rebuilding them.

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
    /// Index into `Arena.types`.
    TypeId
}

id_type_pub! {
    /// Index into `Arena.terms`.
    TermId
}

id_type_sealed! {
    /// Index into `Arena.imports`. A `TermRef::Foreign(import, id)` or
    /// `TypeRef::Foreign(import, id)` resolves through this table.
    ImportId
}

id_type_sealed! {
    /// Index into `Arena.strings`. Interned `SmolStr` names (variable,
    /// constant, type, and type-variable names).
    StrId
}

id_type_sealed! {
    /// Index into `Arena.bytes`. Byte-string literals.
    BytesId
}

id_type_sealed! {
    /// Index into `Arena.bits`. Bit-string literals.
    BitsId
}

id_type_sealed! {
    /// Index into `Arena.ints`. Big-int literals (|value| > i64::MAX).
    IntId
}

id_type_sealed! {
    /// Index into `Arena.nats`. Big-nat literals (value > u64::MAX).
    NatId
}

id_type_sealed! {
    /// Index into `Arena.tyargs`. Argument lists for `TypeDef::Tyapp`.
    TyArgsId
}

id_type_sealed! {
    /// Index into `Arena.foreign_terms`. Bottom 31 bits of a foreign
    /// [`TermRef`](crate::term::TermRef).
    ForeignTermId
}

id_type_sealed! {
    /// Index into `Arena.foreign_types`. Bottom 31 bits of a foreign
    /// [`TypeRef`](crate::ty::TypeRef).
    ForeignTypeId
}
