//! Covalence HOL kernel.
//!
//! See `docs/prover-architecture.md` for the conceptual model and
//! `docs/prover-mvp-plan.md` for the staged build-out.
//!
//! Surface layers:
//! - [`Kernel`] — ergonomic facade with term builders + proof methods.
//! - [`Arena`] + [`Thm`] — the lower-level primitives.

pub mod arena;
pub mod id;
pub mod kernel;
pub mod primop;
pub mod prop;
pub mod reduce;
pub mod term;
pub mod ty;
pub mod uf;

pub use arena::{Arena, UnionError};
pub use kernel::Kernel;
pub use prop::{Context, ProofError, Prop, Thm};
pub use id::{
    BytesId, ForeignTermId, ForeignTypeId, ImportId, IntId, NatId, StrId, TermId,
    TyArgsId, TypeId,
};
pub use primop::{PrimOp1, PrimOp2};
pub use term::{Packed64, TermDef, TermKind, TermRef};
pub use ty::{TypeDef, TypeInfo, TypeRef};
pub use uf::TermUfEntry;
