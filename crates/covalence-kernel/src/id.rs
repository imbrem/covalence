//! Index handles into the Arena's internal tables.
//!
//! Every variant is `Copy` and `u32`-sized — that's what lets `TermRef` and
//! `TypeRef` (and through them `TermDef` / `TypeDef`) stay `Copy`. The
//! variable-sized payloads (names, byte strings, big-ints, type-arg lists,
//! foreign arenas) live in per-arena interning tables and are referenced
//! by these handles.

macro_rules! id_type {
    ($(#[$attr:meta])* $name:ident) => {
        $(#[$attr])*
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
        pub struct $name(pub u32);
    };
}

id_type! {
    /// Index into `Arena.types`.
    TypeId
}

id_type! {
    /// Index into `Arena.terms`.
    TermId
}

id_type! {
    /// Index into `Arena.imports`. A `TermRef::Foreign(import, id)` or
    /// `TypeRef::Foreign(import, id)` resolves through this table.
    ImportId
}

id_type! {
    /// Index into `Arena.strings`. Interned `SmolStr` names (variable,
    /// constant, type, and type-variable names).
    StrId
}

id_type! {
    /// Index into `Arena.bytes`. Byte-string literals and bit strings
    /// too large to inline in `TermDef`.
    BytesId
}

id_type! {
    /// Index into `Arena.bits`. Bit-string literals (length > 64 bits).
    BitsId
}

id_type! {
    /// Index into `Arena.ints`. Big-int literals (|value| > i64::MAX).
    IntId
}

id_type! {
    /// Index into `Arena.nats`. Big-nat literals (value > u64::MAX).
    NatId
}

id_type! {
    /// Index into `Arena.tyargs`. Argument lists for `TypeDef::Tyapp`.
    TyArgsId
}
