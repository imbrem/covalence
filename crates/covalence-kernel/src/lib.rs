//! Covalence HOL kernel.
//!
//! See `docs/prover-architecture.md` for the conceptual model and
//! `docs/prover-mvp-plan.md` for the staged build-out.
//!
//! Surface layers:
//! - [`Kernel`] — ergonomic facade with term builders + proof methods.
//! - [`Arena`] + [`Thm`] — the lower-level primitives.

pub mod arena;
pub mod egraph;
pub mod id;
pub mod kernel;
pub mod primop;
pub mod prop;
mod reduce;
pub mod subst;
pub mod term;
pub mod ty;
pub mod uf;

pub use arena::{Arena, SubsetError, UnionError};
pub use egraph::Egraph;
pub use kernel::Kernel;
pub use prop::{Context, ProofError, Prop, Thm};
pub use id::{
    BytesId, ImportId, IntId, NatId, StrId, TermId, TermSubstId, TyArgsId, TypeId, TypeSubstId,
};
pub use primop::{PrimOp1, PrimOp2};
pub use subst::{TermSubst, TypeSubst};
pub use term::{Packed64, TermDef, TermKind, TermRef};
pub use ty::{TypeInfo, TypeKind, TypeRef};
pub use uf::{TermProps, TermUf};
