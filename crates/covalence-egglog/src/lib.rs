//! Bridge from egglog (2.0 proof DAGs) into any `covalence_shell::Prover`.
//!
//! Surface mirrors [`covalence_alethe`](../../covalence-alethe/index.html):
//!
//!   - [`EgglogBridge`] — the *stable*, egglog-shaped trait that any backend
//!     implements. One method per egglog 2.0 [`Justification`] variant plus
//!     a small set of program-declaration verbs (`declare_sort`,
//!     `declare_constructor`).
//!   - [`ingest_proof_store`] — the prover-agnostic driver. Walks a
//!     [`ProofStore`] in dependency order, owns the `ProofId → Thm` map, and
//!     calls the bridge once per node.
//!   - [`KernelEgglogBridge`] — the concrete impl against any
//!     `P: covalence_shell::Prover`. Stage 0 wires only [`Justification::Fiat`];
//!     every other justification returns
//!     [`BridgeError::NotImplemented`].
//!   - [`BridgeError`] — error type, including the `NotImplemented` escape
//!     hatch for justifications that haven't been wired through yet.
//!
//! The crate is deliberately egglog-agnostic at the proof-source level: it
//! defines its own [`proof::Proof`] / [`proof::Justification`] / [`proof::TermDag`]
//! mirroring egglog 2.0's `src/proofs/proof_format.rs`. A future
//! `from_egglog_proofstore` shim converts the external library's `ProofStore`
//! into ours without the rest of the crate caring.

pub mod bridge;
pub mod error;
pub mod ingest;
pub mod kernel_bridge;
pub mod proof;

pub use bridge::EgglogBridge;
pub use error::BridgeError;
pub use ingest::ingest_proof_store;
pub use kernel_bridge::KernelEgglogBridge;
pub use proof::{
    Justification, Proof, ProofId, ProofStore, Proposition, Term, TermDag, TermId,
};
