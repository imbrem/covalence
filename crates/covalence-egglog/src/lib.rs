//! Bridge from egglog (2.0 proof DAGs) into a pluggable backend.
//!
//! Surface mirrors [`covalence_alethe`](../../covalence-alethe/index.html):
//!
//!   - [`EgglogBridge`] — the *stable*, egglog-shaped trait that any backend
//!     implements. One method per egglog 2.0 [`Justification`] variant plus
//!     a small set of program-declaration verbs (`declare_sort`,
//!     `declare_constructor`).
//!   - [`ingest_proof_store`] — the backend-agnostic driver. Walks a
//!     [`ProofStore`] in dependency order, owns the `ProofId → Thm` map, and
//!     calls the bridge once per node.
//!   - [`BridgeError`] — error type, including the `NotImplemented` escape
//!     hatch for justifications that haven't been wired through yet.
//!
//! The crate is deliberately egglog-agnostic at the proof-source level: it
//! defines its own [`proof::Proof`] / [`proof::Justification`] / [`proof::TermDag`]
//! mirroring egglog 2.0's `src/proofs/proof_format.rs`. A future
//! `from_egglog_proofstore` shim converts the external library's `ProofStore`
//! into ours without the rest of the crate caring.
//!
//! # ⚠️ Status: skeleton
//!
//! The concrete `KernelEgglogBridge` impl over the HOL-on-store stack lands
//! here later. What remains is the backend-agnostic trait + driver + proof-DAG
//! parsing / lowering.

pub mod ast;
pub mod bridge;
pub mod error;
// egglog support DISABLED for now (see SKELETONS.md / Cargo.toml). The bridge in
// `external.rs` needs egglog's `proof` module, absent from released egglog.
// #[cfg(feature = "external-egglog")]
// pub mod external;
pub mod ingest;
pub mod lower;
pub mod parse;
pub mod proof;

pub use ast::{Command, Expr};
pub use bridge::EgglogBridge;
pub use error::BridgeError;
pub use ingest::ingest_proof_store;
pub use lower::{LoweredProgram, lower_program};
pub use parse::parse_program;
pub use proof::{Justification, Proof, ProofId, ProofStore, Proposition, Term, TermDag, TermId};

/// Parse an egglog source string, lower it against `bridge` (registering
/// every sort / constructor / union as it goes), and ingest the
/// `(prove …)` target into the backend — returning the resulting
/// [`Thm`](EgglogBridge::Thm).
///
/// One-shot helper that composes [`parse_program`], [`lower_program`], and
/// [`ingest_proof_store`]. Inherits the lowering's restriction: the
/// `(prove …)` target must syntactically match an earlier `(union …)`.
pub fn ingest_source<B: EgglogBridge>(bridge: &mut B, input: &str) -> Result<B::Thm, BridgeError> {
    let commands = parse_program(input)?;
    let LoweredProgram { dag, store, root } = lower_program(bridge, &commands)?;
    ingest_proof_store(bridge, &store, &dag, root)
}
