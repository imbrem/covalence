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
//! # Backends
//!
//! [`HolAletheBridge`] is the concrete backend over the
//! `covalence-core` HOL kernel: it replays an Alethe refutation as a
//! kernel derivation and reports `Unsat` when it reaches the empty
//! clause. It covers the QF_UF fragment today; the remaining rule
//! families (rewrite `hole`s, subproofs) are tracked in `SKELETONS.md`.
//! The legacy `Prover`-based `KernelAletheBridge` removed in the kernel
//! rewrite can still be recovered from `backup/pre-hol-cleanup`.

pub mod bridge;
pub mod error;
pub mod hol;
pub mod ingest;
pub mod la;

pub use bridge::AletheBridge;
pub use error::BridgeError;
pub use hol::HolAletheBridge;
pub use ingest::{ingest_alethe, ingest_problem, ingest_proof};
