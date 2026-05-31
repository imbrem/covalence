//! Covalence HOL kernel.
//!
//! See `docs/prover-architecture.md` for the conceptual model and
//! `docs/prover-mvp-plan.md` for the staged build-out. This crate is
//! mid-rewrite; Phase 1 stands up the arena, term/type enums, and
//! union-find storage. Equality predicates, inference rules, Prop/Thm,
//! and concepts land in later phases.

pub mod arena;
pub mod id;
pub mod primop;
pub mod term;
pub mod ty;
pub mod uf;

pub use arena::Arena;
pub use id::{
    BitsId, BytesId, ForeignTermId, ForeignTypeId, ImportId, IntId, NatId, StrId, TermId,
    TyArgsId, TypeId,
};
pub use primop::{PrimOp1, PrimOp2};
pub use term::{Packed64, TermDef, TermKind, TermRef};
pub use ty::{TypeDef, TypeInfo, TypeRef};
pub use uf::{TermUfEntry, TypeUfEntry};
