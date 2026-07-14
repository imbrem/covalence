//! covalence-init — the semi-trusted covalence API over `covalence-core`.
//!
//! Everything here is plumbing on top of the kernel; a bug here cannot produce a
//! false `Thm`. It provides:
//!
//! 1. **The theory catalogue** ([`init`]) — nat/int/rat/real/bytes/list/prod/…,
//!    the algebra theories, the inductive engine.
//! 2. **Proof tactics & soundness witnesses** ([`proofs`]) — pure combinators
//!    over the kernel rules (`beta_nf`, `unfold_at_*`, rewriting) plus the
//!    rewriting combinators (the connective/quantifier rules themselves are
//!    `covalence-hol-eval::derived` derivations since stage L2).
//! 3. **The `.cov` surface** ([`script`], [`project`]) and the Metamath/Peano
//!    metalogic ([`metalogic`], [`peano`]).
//! 4. **Serialisation** ([`hash`], [`sexp`]) — content hashing + canonical
//!    S-expression syntax.
//!
//! The thin HOL builder/trait surface (`HolLightCtx`, the `HolLight*` traits,
//! `NameId`/`HolError`) lives in `covalence-hol` and is re-exported here so
//! `crate::…` paths resolve. See `notes/vibes/init-hol-split.md`.

pub mod algebra;
pub mod debug;
pub mod grammar;
pub mod hash;
pub mod init;
// The K-framework frontend lowering: KORE rewrite rules (via the untrusted
// `covalence-k` driver) → `Derivable_KStep` relations over the reified free
// term algebra. The K analogue of `wasm/`. See `notes/design/k-frontend.md`.
pub mod k;
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
pub mod wasm;

// The thin HOL surface lives in `covalence-hol`. Re-export its modules and items
// so `crate::types` / `crate::traits` / `crate::hol_light_ctx` / `crate::HolLightCtx`
// / `crate::Term` paths in this crate resolve unchanged.
pub use covalence_hol::{BOOL_TYCON_ID, EQ_CONST_ID, FUN_TYCON_ID, HolError, NameId};
pub use covalence_hol::{HolLightCtx, HolLightKernel, HolLightTerms, HolLightTypes};
pub use covalence_hol::{Term, Type, TypeDef, TypeKind};
pub use covalence_hol::{hol_light_ctx, traits, types};
pub use covalence_hol_eval::EvalThm as Thm;
// The literal build/recognize facade (`lit::mk_nat` / `mk_blob` / …): the
// sanctioned chokepoint for concrete literal terms, re-exported so surface
// crates that depend only on `covalence-init` (e.g. `covalence-haskell`'s HOL
// backend) never call the kernel literal constructors directly (the purge
// ratchet pins those call sites).
pub use covalence_hol_eval::lit;

/// Type-builder handler shapes used by the per-theory `HANDLERS` signature
/// tables (`init::prop`, `init::sexpr`, `peano::fol`, `peano::sem`, …).
pub type NullaryTypeHandler = fn() -> Type;
/// One-argument type-builder handler (see [`NullaryTypeHandler`]).
pub type UnaryTypeHandler = fn(&Type) -> Type;
/// Two-argument type-builder handler (see [`NullaryTypeHandler`]).
pub type BinaryTypeHandler = fn(&Type, &Type) -> Type;
