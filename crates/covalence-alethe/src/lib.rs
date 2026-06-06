//! Bridge from Alethe (SMT-LIB2 proof format) into any
//! `covalence_shell::Prover`.
//!
//! Surface:
//!   - [`AletheBridge`] — the *stable*, Alethe-shaped trait that any backend
//!     implements. One method per top-level Alethe command.
//!   - [`ingest_alethe`] / [`ingest_problem`] / [`ingest_proof`] — the
//!     prover-agnostic driver. Owns the step-id → `Thm` map; the bridge
//!     never sees raw step names.
//!   - [`KernelAletheBridge`] — the concrete impl against any
//!     `P: covalence_shell::Prover`. Expected to churn alongside kernel
//!     redesigns; the trait above stays put.
//!   - [`BridgeError`] — error type, including the `NotImplemented` escape
//!     hatch used by rules that haven't been wired through yet.

pub mod bridge;
pub mod error;
pub mod ingest;
pub mod kernel_bridge;

pub use bridge::AletheBridge;
pub use error::BridgeError;
pub use ingest::{ingest_alethe, ingest_problem, ingest_proof};
pub use kernel_bridge::KernelAletheBridge;
