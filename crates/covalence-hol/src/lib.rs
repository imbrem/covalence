//! covalence-hol — untrusted shell over `covalence-core`.
//!
//! This crate now wears two hats:
//!
//! 1. **HOL Light builder API** (`HolLightCtx`, `PureHol`, the
//!    `HolLightKernel`/`HolLightTerms`/`HolLightTypes` traits,
//!    `nat_axioms`, `int_axioms`) — convenience constructors over
//!    `covalence-core`'s folded-in HOL primitives, plus the
//!    bridge axioms and stdlib lazy statics.
//!
//! 2. **Term/type serialisation** (`hash`, `sexp`) — content
//!    hashing and the canonical S-expression syntax used by every
//!    shell crate. Formerly lived in the now-deleted
//!    `covalence-pure-shell`.
//!
//! Nothing in this crate is consumed by `covalence-core`'s
//! inference rules; a bug here cannot produce a false `Thm`.

// `bridge` and `peano` host Rust-encoded HOL proofs that depended on
// the now-removed Pure-meta layer (`Trueprop`, `⋀`, Pure `≡`). They
// are slated for rewrite in the upcoming WASM-based proof format;
// gated out for now so the kernel rebuild can land cleanly.
// pub mod bridge;
pub mod hash;
pub mod hol_light_obs;
pub mod int_axioms;
pub mod nat_axioms;
// pub mod peano;
pub mod pure_hol;
pub mod sexp;
pub mod stdlib;
pub mod traits;
pub mod types;

pub use hol_light_obs::HolLightCtx;
pub use pure_hol::PureHol;
pub use traits::{HolLightKernel, HolLightTerms, HolLightTypes};
pub use types::{BOOL_TYCON_ID, EQ_CONST_ID, FUN_TYCON_ID, HolError, NameId};
