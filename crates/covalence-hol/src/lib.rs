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
//! 4. **Surface syntax** ([`surface`]) — a *design sketch* of the
//!    high-level "generalized Haskell" authoring language (pure
//!    S-expressions, `#`-headed builtins) that will elaborate down to the
//!    kernel objects. See `docs/surface-syntax.md`.
//!
//! Nothing in this crate is consumed by `covalence-core`'s inference
//! rules.

pub mod ac;
pub mod category;
pub mod hash;
pub mod hol_light_obs;
pub mod init;
pub mod monoidal;
pub mod peano;
pub mod proofs;
pub mod ring;
pub mod script;
pub mod semiring;
pub mod sexp;
pub mod surface;
pub mod traits;
pub mod types;

pub use hol_light_obs::HolLightCtx;
pub use traits::{HolLightKernel, HolLightTerms, HolLightTypes};
pub use types::{BOOL_TYCON_ID, EQ_CONST_ID, FUN_TYCON_ID, HolError, NameId};

// Re-export the TCB term/type/theorem types that the builder API works
// with, so downstream layers reach the kernel through `covalence-hol`
// rather than depending on the `covalence-core` TCB crate directly.
pub use covalence_core::{Term, Thm, Type, TypeDef, TypeKind};
