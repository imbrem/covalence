//! Covalence kernel — the "OS-kernel" layer over the logical TCB.
//!
//! Sits between [`covalence_hol`] (the untrusted high-level proof API built on
//! the `covalence-core` TCB) and `covalence-shell` (userspace helpers).
//! Its job is to wire the HOL proof world to durable infrastructure:
//!
//!   - **facts** — proven theorems tracked via [`covalence_hol`]
//!     ([`facts`] — skeleton; the observer layer lands here).
//!   - **blobs** — a content-addressed [`Kernel`] over the blob store.
//!   - **trees** — directory / table objects via `covalence-object`.
//!
//! These will become *observers* in the longer-term design (see
//! `docs/roadmap.md`).
//!
//! # ⚠️ Status: skeleton
//!
//! The legacy arena + egraph + union-find prover kernel that used to live
//! here was removed in the kernel rewrite. Recover it from the
//! `backup/pre-hol-cleanup` branch if needed. What remains is the
//! content-addressed store wiring (lifted from `covalence-shell`) plus an
//! empty [`facts`] module to be filled in as the HOL-on-store stack comes
//! online.

// Re-export the high-level HOL API so the layers above (covalence-shell and
// downstream frontends) reach the proof world through the kernel. Access to
// the `covalence-core` TCB goes through `covalence-hol`, never directly.
pub use covalence_hol;

mod backend;
pub use backend::{AsyncBackend, BackendInfo, KernelError, SyncBackend};

mod store;
pub use store::Kernel;

mod service;
pub use service::{
    ArticleSource, CheckReport, Diagnostic, KernelService, Severity, Span, TheoremInfo, TrustLevel,
    TrustPolicy,
};

pub mod facts;
