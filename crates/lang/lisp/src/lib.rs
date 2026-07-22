//! Reusable Lisp frontends and proof-producing HOL realizations.
//!
//! The stable waist is [`kernel_api`]: backend-neutral syntax, definitions,
//! environments, partial CEK execution, finite `MayEval` witnesses, and
//! admission capabilities. This crate supplies concrete readers and dialects:
//!
//! - [`frontend`] lowers Scheme, Sector, and ACL2 surface forms to the common
//!   core;
//! - [`carrier`] realizes Lisp data through the shared abstract S-expression
//!   API;
//! - [`relation`] proves `Reduces input value`; its exact `int ⊕ bytes`
//!   backend is the default [`session::Lang::Lisp`];
//! - [`semantics`] retains the older equational Scheme backend for recursive
//!   definitions while partial higher-order proof semantics are developed;
//! - [`acl2`] layers checked worlds, admission, derivations, and theorem
//!   transport over the common Lisp core.
//!
//! Parsing, lowering, search, and execution may propose witnesses. Only the
//! HOL kernel can produce theorem authority, and rendered proof-mode values
//! are read from checked theorem conclusions.

#![forbid(unsafe_code)]

pub mod forsp;
pub mod frontend;
pub mod reader;
pub mod scheme_effect;

#[cfg(feature = "hol")]
pub mod hol;

#[cfg(feature = "hol")]
pub mod carrier;

#[cfg(feature = "hol")]
pub mod defs;

#[cfg(feature = "hol")]
pub mod semantics;

#[cfg(feature = "hol")]
pub mod int_backend;

#[cfg(feature = "hol")]
pub mod relation;

#[cfg(feature = "hol")]
pub mod session;

#[cfg(feature = "hol")]
pub mod acl2;

#[cfg(feature = "hol")]
pub mod acl2_api;

#[cfg(feature = "hol")]
pub mod book;

#[cfg(feature = "hol")]
pub mod progress;
pub mod quasiquote;

#[cfg(feature = "hol")]
pub mod world;

/// Stable backend-neutral Lisp capabilities used by the concrete dialects in
/// this crate.
pub use covalence_kernel_lisp as kernel_api;
