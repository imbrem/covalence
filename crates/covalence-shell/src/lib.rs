//! Covalence shell: high-level generic APIs around the HOL kernel.
//!
//! This crate hosts:
//!
//!   - The `SyncBackend` / `AsyncBackend` runtime traits + a concrete
//!     in-memory `Kernel` wrapping the content-addressed store.
//!   - The [`Prover`] trait — a high-level, kernel-agnostic theorem-prover
//!     API that downstream frontends (Alethe, OpenTheory, …) target. The
//!     impl lowers it to [`covalence_kernel::Kernel`].
//!   - The [`HolPrim`] HOL Light driver — implements the HOL Light
//!     `HolLightKernel` trait family on top of a kernel, bridging
//!     named ↔ locally-nameless representation. Used by the OpenTheory
//!     article interpreter.
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

pub use prover::{Prover, ProverError};

pub mod hol;
pub use hol::{HolPrim, HolPrimError, ThmHandle};

/// Re-exports from `covalence-kernel` that downstream prover frontends need
/// in their signatures. Centralising them here lets frontends depend only on
/// `covalence-shell`.
pub use covalence_kernel::primop::{PrimOp1, PrimOp2};
