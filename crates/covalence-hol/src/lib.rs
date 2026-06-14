//! covalence-hol — untrusted higher-level shell over `covalence-core`.
//!
//! Everything in this crate is plumbing on top of the kernel; a bug
//! here cannot produce a false `Thm`. It wears three hats:
//!
//! 1. **HOL term/type builder API** (`HolLightCtx`, the
//!    `HolLightKernel`/`HolLightTerms`/`HolLightTypes` traits) —
//!    convenience constructors over `covalence-core`'s folded-in HOL
//!    atoms (`bool`, `=`, the connectives, the binders).
//!
//! 2. **Postulated facts and proof tactics** (`nat_axioms`,
//!    `int_axioms`, `stdlib`, `proofs`) — facts not yet derived from
//!    the kernel's single non-computational axiom (`nat_induction`),
//!    threaded through `Thm::assume` with a self-hyp audit trail,
//!    plus pure tactic combinators that drive the kernel rules. These
//!    postulates are *temporary*: the long-term goal is for the only
//!    genuine axioms to be the kernel's content-addressing / observer
//!    ones, with arithmetic and the propositional connectives either
//!    derived or built into the kernel directly.
//!
//! 3. **Term/type serialisation** (`hash`, `sexp`) — content hashing
//!    and the canonical S-expression syntax used by every shell crate.
//!
//! Nothing in this crate is consumed by `covalence-core`'s inference
//! rules.

// `bridge`, `peano`, `pure_hol` host Rust-encoded proofs that
// depended on the now-removed Pure→HOL bridge layer (`Trueprop`,
// `eq_reflection`). They're slated for rewrite in the upcoming
// WASM-based proof format.
// pub mod bridge;
pub mod hash;
pub mod hol_light_obs;
pub mod int_axioms;
pub mod nat_axioms;
// pub mod peano;
pub mod proofs;
// pub mod pure_hol;
pub mod sexp;
pub mod stdlib;
pub mod traits;
pub mod types;

pub use hol_light_obs::HolLightCtx;
pub use traits::{HolLightKernel, HolLightTerms, HolLightTypes};
pub use types::{BOOL_TYCON_ID, EQ_CONST_ID, FUN_TYCON_ID, HolError, NameId};
