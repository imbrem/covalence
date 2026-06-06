//! Bridge from Alethe (SMT-LIB2 proof format) into a `HolLightKernel`.
//!
//! Surface:
//!   - [`AletheBridge`] — the *stable*, Alethe-shaped trait that any backend
//!     implements. One method per top-level Alethe command.
//!   - [`ingest_alethe`] / [`ingest_problem`] / [`ingest_proof`] — the
//!     kernel-agnostic driver. Owns the step-id → `Thm` map; the bridge
//!     never sees raw step names.
//!   - [`HolAletheBridge`] — the concrete impl against any `K: HolLightKernel`.
//!     Expected to churn alongside kernel redesigns; the trait above stays put.
//!   - [`BridgeError`] — error type, including the `NotImplemented` escape
//!     hatch used by rules that haven't been wired through yet.
//!
//! See the crate's `README` / module docs for the layering rationale.

pub mod bridge;
pub mod error;
pub mod hol_bridge;
pub mod ingest;
pub mod names;

pub use bridge::AletheBridge;
pub use error::BridgeError;
pub use hol_bridge::HolAletheBridge;
pub use ingest::{ingest_alethe, ingest_problem, ingest_proof};
pub use names::NameTable;
