//! Bridge from Alethe (SMT-LIB2 proof format) into a pluggable backend.
//!
//! Surface:
//!   - [`AletheBridge`] — the *stable*, Alethe-shaped trait that any backend
//!     implements. One method per top-level Alethe command.
//!   - [`ingest_alethe`] / [`ingest_problem`] / [`ingest_proof`] — the
//!     backend-agnostic driver. Owns the step-id → `Thm` map; the bridge
//!     never sees raw step names.
//!   - [`BridgeError`] — error type, including the `NotImplemented` escape
//!     hatch used by rules that haven't been wired through yet.
//!
//! # ⚠️ Status: skeleton
//!
//! The concrete `KernelAletheBridge` impl (against the legacy `Prover`
//! trait) was removed in the kernel rewrite. Recover it from
//! `backup/pre-hol-cleanup` if needed; a new impl over the HOL-on-store
//! stack lands here later. What remains is the backend-agnostic trait +
//! driver + SMT/Alethe parsing.

pub mod bridge;
pub mod error;
pub mod ingest;

pub use bridge::AletheBridge;
pub use error::BridgeError;
pub use ingest::{ingest_alethe, ingest_problem, ingest_proof};
