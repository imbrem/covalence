//! covalence-hol — the thin HOL surface.
//!
//! The builder/trait surface HOL proof *consumers* work against:
//!
//! 1. **HOL builder API** ([`HolLightCtx`]) — convenience constructors over
//!    `covalence-core`'s folded-in HOL atoms (`bool`, `=`, the connectives, the
//!    binders).
//! 2. **Kernel traits** ([`HolLightKernel`] / [`HolLightTerms`] / [`HolLightTypes`])
//!    — the abstract surface a HOL backend implements; what the OpenTheory
//!    importer is generic over.
//! 3. **Shared types** ([`types`]) — the `NameId` namespace and `HolError`.
//!
//! Nothing here is consumed by `covalence-core`'s inference rules — a bug here
//! cannot produce a false `Thm`. The semi-trusted catalogue, proof machinery,
//! and `.cov` surface live in `covalence-init`. See `notes/vibes/init-hol-split.md`.
//!
//! Long-term this crate becomes a core-free HOL syntax/proof substrate (a peer
//! of `covalence-metamath`) and absorbs OpenTheory import behind an `opentheory`
//! feature; today it still depends on `covalence-core`.

pub mod hol_light_obs;
pub mod traits;
pub mod types;

pub use hol_light_obs::HolLightCtx;
pub use traits::{HolLightKernel, HolLightTerms, HolLightTypes};
pub use types::{BOOL_TYCON_ID, EQ_CONST_ID, FUN_TYCON_ID, HolError, NameId};

// Re-export the TCB term/type/theorem types the builder API works with, so
// downstream layers reach the kernel through `covalence-hol` rather than the
// `covalence-core` TCB crate directly.
pub use covalence_core::{Term, Thm, Type, TypeDef, TypeKind};
