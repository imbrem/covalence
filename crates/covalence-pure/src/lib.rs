//! # `covalence-pure` — facade over the kernel + ergonomic extensions
//!
//! Re-exports [`covalence_pure_trusted`] (the kernel TCB — the audit target) and
//! adds **non-minting** sugar on top: the [`testing`] utilities and the
//! same-context extension traits ([`MThmExt`] / [`MThmVecExt`]). None of it can
//! reach the private `MThm::new`
//! constructor, so the trusted surface stays exactly `covalence-pure-trusted`.
//!
//! Downstream crates depend on `covalence-pure`; later siblings —
//! `covalence-pure-derive` (proc macros) and feature crates (a theory of
//! equality, first-order logic, content-addressing, …) — slot in the same way,
//! each contributing `Rule`s a context opts into.

pub use covalence_pure_trusted::*;

mod ext;
pub mod testing;

pub use ext::*;
