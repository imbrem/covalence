//! # `covalence-kernel-smt` — generic SMT-proof replay into the kernel
//!
//! Turns a parsed Alethe (cvc5 / veriT) proof into kernel theorems by
//! *re-deriving every step* — the proof is untrusted data; only the kernel's
//! own inference rules mint theorems, so this crate adds **zero TCB**. It is the
//! kernel-facing companion to `covalence-smt` (`crates/lib/smt`), which owns the
//! Alethe *format* (parsing, `SmtProblem`, the cvc5 solver shell).
//!
//! ## Two axes of genericity
//!
//! 1. **Target logic / integer representation.** The linear-arithmetic replay is
//!    written against the [`covalence_hol_api::Int`] trait, not a concrete
//!    kernel. The native HOL `int`, a `succ`/numeral integer encoding, and a
//!    future *object-level* `int` inside internal Peano arithmetic or
//!    second-order arithmetic are all just different `Int` impls; the same
//!    Farkas engine drives each. (See `notes/vibes/logics/smt-import-architecture.md`.)
//! 2. **Rule subset.** A [`RulePolicy`] lets a caller admit only a chosen subset
//!    of Alethe rules (e.g. "QF_UF only", "no subproofs", "propositional core")
//!    and get a clean, structured refusal for anything outside it — the hook for
//!    growing coverage one rule family at a time and for backends that can only
//!    model part of the logic.
//!
//! ## What is built here today
//!
//! - The **pure Farkas certificate checker** ([`farkas`], over [`rational`] +
//!   [`lincomb`]): backend-independent rational linear algebra implementing the
//!   Alethe spec's `la_generic` checking procedure (integer strengthening +
//!   scaling + sum-to-contradiction). It answers "is the certificate valid?" as
//!   data, decoupled from re-deriving it in any logic.
//! - The [`RulePolicy`] subset knob.
//!
//! The `Int`-generic term→[`farkas::NormLit`] parser and the kernel *replay*
//! (valid certificate → `⊢ ⊥`), plus the Alethe step dispatcher, are the next
//! modules — see `SKELETONS.md`. Until then the working HOL Alethe bridge lives
//! in `crates/proof/alethe`; this crate is its generic successor.

pub mod farkas;
pub mod lincomb;
pub mod policy;
pub mod rational;
pub mod replay;

pub use covalence_hol_api::{Discharger, EvalDischarger, LinOrder, Strict};
pub use farkas::{FarkasCert, FarkasError, NormLit, Rel};
pub use lincomb::LinComb;
pub use policy::{RuleClass, RulePolicy};
pub use rational::Rational;
pub use replay::{Edge, ReplayError, refute_chain, refute_cycle};
