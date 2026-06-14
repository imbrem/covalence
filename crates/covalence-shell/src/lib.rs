//! Covalence shell: high-level generic APIs around the HOL kernel.
//!
//! This crate hosts:
//!
//!   - The `SyncBackend` / `AsyncBackend` runtime traits + a concrete
//!     in-memory `Kernel` wrapping the content-addressed store.
//!   - The [`Prover`] trait — a high-level, kernel-agnostic theorem-prover
//!     API that downstream frontends (Alethe, OpenTheory, …) target. The
//!     impl lowers it to [`covalence_kernel::Kernel`].
//!
//! A future PureHol-backed `hol` module will host the untrusted
//! shell-side adapter (sexp serialisation, content hashing,
//! pretty-printing) over `covalence_hol::PureHol`. The legacy
//! HolPrim adapter (wrapping the arena kernel) was removed once
//! consumers moved to PureHol directly.
//!
//! When the kernel is rewritten, the [`Prover`] trait is the surface that
//! stays stable; impls underneath migrate, with individual operations
//! stubbed via [`ProverError::NotImplemented`] during the transition so
//! frontends keep compiling.

mod traits;
pub use traits::{AsyncBackend, BackendInfo, KernelError, SyncBackend};

mod kernel;
pub use kernel::Kernel;

pub mod prover;
mod prover_kernel;

// `init` (formerly `stdlib`) and `PureHol` were re-exports of
// `covalence_hol`'s proof-heavy modules. Re-introduce once the
// WASM-proof rewrite lands the `init` library over HOL-Light rules.
// pub use covalence_hol::init;

pub use prover::{Prover, ProverError};

/// Re-exports from `covalence-kernel` that downstream prover frontends need
/// in their signatures. Centralising them here lets frontends depend only on
/// `covalence-shell`.
pub use covalence_kernel::primop::{PrimOp1, PrimOp2};

/// HOL term-builder re-exports that downstream consumers need.
/// `PureHol` (the HolLightKernel impl) is gated until the WASM-proof
/// rewrite reinstates it on HOL-Light rules.
pub use covalence_hol::{HolLightCtx, HolLightKernel};
pub use covalence_core::{Term, Thm, Type, TypeDef, TypeKind};
