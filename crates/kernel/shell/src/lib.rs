//! Covalence shell — userspace helpers over the kernel.
//!
//! A thin, *untrusted* convenience layer on top of [`covalence_kernel`]
//! (the "OS-kernel": facts + blob store + trees) and [`covalence_hol`]
//! (the high-level proof API over the `covalence-core` TCB). Downstream
//! frontends, the REPL, the server, and the CLI depend on the shell rather
//! than reaching into the kernel directly.
//!
//! # ⚠️ Status: skeleton
//!
//! What remains are re-exports of the kernel's backend surface plus the HOL
//! builder API; new userspace helpers land here as the HOL-on-store stack
//! comes online.

// Backend / blob-store surface, re-exported from the kernel so existing
// consumers keep depending only on `covalence-shell`.
pub use covalence_kernel::{AsyncBackend, BackendInfo, Kernel, KernelError, SyncBackend};

// HOL builder API + term/type/theorem types (the latter re-exported from
// `covalence-hol`, so the shell never depends on the TCB crate directly).
pub use covalence_hol::{HolLightCtx, HolLightKernel, Term, Thm, Type, TypeDef, TypeKind};
