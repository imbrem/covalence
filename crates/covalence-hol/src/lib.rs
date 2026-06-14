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
//!    `int_axioms`, `init`, `proofs`) — facts not yet derived from
//!    the kernel's primitive rules (induction `Thm::nat_induct`, ex
//!    falso `Thm::false_elim`, the connective rules, …), threaded
//!    through `Thm::assume` with a self-hyp audit trail, plus pure
//!    tactic combinators that drive the kernel rules. The remaining
//!    postulates are the arithmetic tier (recursion theorem); the
//!    propositional logic (`init::bool`, `proofs::bool`) is fully
//!    derived.
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
pub mod init;
pub mod int_axioms;
pub mod nat_axioms;
// pub mod peano;
pub mod proofs;
// pub mod pure_hol;
pub mod sexp;
pub mod traits;
pub mod types;

pub use hol_light_obs::HolLightCtx;
pub use traits::{HolLightKernel, HolLightTerms, HolLightTypes};
pub use types::{BOOL_TYCON_ID, EQ_CONST_ID, FUN_TYCON_ID, HolError, NameId};
