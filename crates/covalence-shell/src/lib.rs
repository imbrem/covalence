//! Covalence shell: concrete wiring around the HOL kernel.
//!
//! This crate hosts the runtime concretes that the kernel keeps abstract:
//! the `SyncBackend` / `AsyncBackend` trait surface for local vs remote
//! kernels, a concrete in-memory `Kernel` wrapping the content-addressed
//! store, and (in later phases) the WASM `cov:hol/observe` executor plus
//! untrusted utilities (Goal, tactic combinators, closure strategies).

mod traits;
pub use traits::{AsyncBackend, BackendInfo, KernelError, SyncBackend};

mod kernel;
pub use kernel::Kernel;
