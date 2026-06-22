//! covalence-hol — untrusted higher-level shell over `covalence-core`.
//!
//! Everything here is plumbing on top of the kernel; a bug here
//! cannot produce a false `Thm`. It provides:
//!
//! 1. **HOL term/type builder API** ([`HolLightCtx`], the
//!    `HolLightKernel` / `HolLightTerms` / `HolLightTypes` traits) —
//!    convenience constructors over `covalence-core`'s folded-in HOL
//!    atoms (`bool`, `=`, the connectives, the binders).
//!
//! 2. **Proof tactics & soundness witnesses** ([`proofs`]) — pure
//!    combinators over the kernel rules (`beta_nf`, `unfold_at_*`,
//!    rewriting) plus the executable derivations that witness the
//!    soundness of the kernel's fast connective methods. No postulates.
//!
//! 3. **Term/type serialisation** ([`hash`], [`sexp`]) — content
//!    hashing and the canonical S-expression syntax.
//!
//! The high-level "generalized Haskell" authoring layer now lives in
//! `script` (the `#sig`/`#thy`/`#model`/`#models` forms — the surface↔script
//! fusion of `docs/surface-compiler.md §3.0`); the old `surface/` design
//! sketch was removed (recover from git history). It will be rebuilt as the
//! elaborator from a Haskell-like surface *down to* `.thy` (`§3.0.4`).
//!
//! Nothing in this crate is consumed by `covalence-core`'s inference
//! rules.

pub mod ac;
pub mod category;
pub mod hash;
pub mod hol_light_obs;
pub mod init;
pub mod metalogic;
// The Metamath engine + `.mm` reader live in the lower, HOL-free
// `covalence-metamath` crate; re-export it so `crate::metamath::…` (the peano
// bridge, the metalogic replay) keeps resolving.
pub use covalence_metamath as metamath;
pub mod models;
pub mod monoidal;
pub mod peano;
pub mod project;
pub mod proofs;
pub mod regex;
pub mod ring;
pub mod script;
pub mod semiring;
pub mod sexp;
pub mod spectec;
pub mod traits;
pub mod types;

pub use hol_light_obs::HolLightCtx;
pub use traits::{HolLightKernel, HolLightTerms, HolLightTypes};
pub use types::{BOOL_TYCON_ID, EQ_CONST_ID, FUN_TYCON_ID, HolError, NameId};

// Re-export the TCB term/type/theorem types that the builder API works
// with, so downstream layers reach the kernel through `covalence-hol`
// rather than depending on the `covalence-core` TCB crate directly.
pub use covalence_core::{Term, Thm, Type, TypeDef, TypeKind};
