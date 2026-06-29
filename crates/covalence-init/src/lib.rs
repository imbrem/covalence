//! covalence-init — the semi-trusted covalence API over `covalence-core`.
//!
//! Everything here is plumbing on top of the kernel; a bug here cannot produce a
//! false `Thm`. It provides:
//!
//! 1. **The theory catalogue** ([`init`]) — nat/int/rat/real/bytes/list/prod/…,
//!    the algebra theories, the inductive engine.
//! 2. **Proof tactics & soundness witnesses** ([`proofs`]) — pure combinators
//!    over the kernel rules (`beta_nf`, `unfold_at_*`, rewriting) plus the
//!    executable derivations witnessing the kernel's fast connective methods.
//! 3. **The `.cov` surface** ([`script`], [`project`]) and the Metamath/Peano
//!    metalogic ([`metalogic`], [`peano`]).
//! 4. **Serialisation** ([`hash`], [`sexp`]) — content hashing + canonical
//!    S-expression syntax.
//!
//! The thin HOL builder/trait surface (`HolLightCtx`, the `HolLight*` traits,
//! `NameId`/`HolError`) lives in `covalence-hol` and is re-exported here so
//! `crate::…` paths resolve. See `notes/init-hol-split.md`.

pub mod algebra;
pub mod debug;
pub mod grammar;
pub mod hash;
pub mod init;
pub mod metalogic;
// The Metamath engine + `.mm` reader live in the lower, HOL-free
// `covalence-metamath` crate; re-export it so `crate::metamath::…` (the peano
// bridge, the metalogic replay) keeps resolving.
pub use covalence_metamath as metamath;
pub mod models;
pub mod peano;
pub mod project;
pub mod proofs;
pub mod script;
pub mod sexp;

// The thin HOL surface lives in `covalence-hol`. Re-export its modules and items
// so `crate::types` / `crate::traits` / `crate::hol_light_obs` / `crate::HolLightCtx`
// / `crate::Term` paths in this crate resolve unchanged.
pub use covalence_hol::{BOOL_TYCON_ID, EQ_CONST_ID, FUN_TYCON_ID, HolError, NameId};
pub use covalence_hol::{HolLightCtx, HolLightKernel, HolLightTerms, HolLightTypes};
pub use covalence_hol::{Term, Thm, Type, TypeDef, TypeKind};
pub use covalence_hol::{hol_light_obs, traits, types};
