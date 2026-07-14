//! # `covalence-hol-api` — the high-level, TRAIT-backed HOL consumer surface
//!
//! A consumer layer **above** the kernel. The point: application code and
//! theory-building code should construct terms and theorems through a small
//! set of traits — [`Hol`] (the value-typed HOL Light surface: term builders +
//! the primitive/derived inference rules) and [`Nat`] (natural-number ops +
//! the commonly-needed Peano lemmas by name) — rather than reaching into
//! `covalence_core::TermKind` / `Term` directly. Then the *only* code that
//! mentions the concrete backend is the trait **impl** ([`NativeHol`]), and
//! swapping the backend (an arena kernel, an internal/object-level HOL, a
//! different literal representation) is a matter of writing one new impl, not
//! porting every consumer.
//!
//! ## What lives here
//!
//! - [`Hol`] / [`NativeHol`] — re-exported from `covalence-init`'s inductive
//!   engine, where the value-typed HOL trait was first grown to make that
//!   engine backend-generic. This crate *promotes* it to a first-class,
//!   supported consumer API (the engine's use is one client among many).
//! - The generic HOL helpers ([`cong_arg`], [`conjuncts`], [`rewrite`],
//!   [`beta_expand`], …) — free functions over any [`Hol`].
//! - [`LogicOps`] / [`Logic`] and the inductive API ([`InductiveSpec`], …) —
//!   re-exported from `covalence-inductive` so a consumer names one crate.
//! - [`nat`] — the new [`Nat`] trait: `zero`/`succ`/`lit` term builders,
//!   `add`/`mul`, and accessors for the workhorse Peano theorems, implemented
//!   for [`NativeHol`] by delegating to `covalence_init`.
//!
//! ## Trust
//!
//! Zero TCB delta. Every method delegates to an already-audited
//! `covalence-core` / `covalence-init` operation; this crate declares no
//! [`Language`](covalence_core) rule and cannot reach `Thm`'s private mint.
//! The golden manifests are byte-identical.
//!
//! Design: `notes/vibes/backend-decoupling.md`.

pub mod int;
pub mod nat;
pub mod omega;
pub mod order;

// ---- The HOL trait surface + native backend (promoted from the inductive
//      engine, where it was first grown) ----
pub use covalence_init::init::inductive::hol::{
    Hol, NativeHol, and_all, beta_expand, beta_nf_concl, beta_nf_expand, beta_reduce, cong_arg,
    cong_fn, conj, conjuncts, discharge_conj, project, rewrite,
};

// ---- The logic-agnostic inductive-types API (a consumer names one crate) ----
pub use covalence_inductive::{
    ArgSort, BackendCaps, CtorSpec, InductiveBackend, InductiveFacts, InductiveSpec,
    InductiveTheory, Logic, LogicOps,
};

// ---- The certificate + core vocabulary the traits are stated over ----
pub use covalence_core::{Error, Result, Term, Type};
pub use covalence_hol_eval::EvalThm as Thm;

pub use int::Int;
pub use nat::Nat;
pub use order::{Discharger, EvalDischarger, LinOrder, Strict};

// ---- The reflected HOL-omega TYPE layer (type-operator variables + kinds) ----
pub use omega::{HolOmega, InstError, NativeHolOmega, OmegaLang};
