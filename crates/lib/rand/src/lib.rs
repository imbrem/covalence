//! Wrapper crate for randomness.
//!
//! All usage of `rand` should go through this crate.
//!
//! **Exception:** `covalence-crypto-sig` depends on `rand_core` 0.6 directly
//! (pinned to match `ed25519-dalek`'s internal dependency) and re-exports
//! it as `dalek_rand_core`. This is the one crate that bypasses
//! `covalence-rand` for randomness.

pub use rand;
pub use rand::*;
