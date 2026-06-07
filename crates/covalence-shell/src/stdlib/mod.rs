//! HOL standard library.
//!
//! Process-global `LazyLock`-initialised types and constants built
//! on top of `covalence-pure` (TCB) and `covalence-hol`
//! (`HolLightCtx`). Internal definitions — predicates, witnesses,
//! Pure-level encodings — are PRIVATE so they can be refined later
//! (e.g., switching `Nat` from `bytes`-bijection to canonical
//! little-endian encoding) without breaking downstream callers.
//!
//! What's stable across re-definitions:
//! - The opaque types returned by each module's `ty()` (within a
//!   process; identity is tied to the typedef marker's `Arc` and
//!   doesn't survive process restarts).
//! - The signature of constructor / accessor / operation functions.
//!
//! What may change:
//! - The carrier set used by `new_type_definition`.
//! - The Pure-level predicate body.
//! - Internal axiomatisation of operations.

pub mod bool;
pub mod nat;
