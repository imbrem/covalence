//! Proof helpers built on top of the `covalence-core` kernel.
//!
//! Nothing here is part of the TCB. Each submodule is one of:
//!
//! * a set of *pure tactics* — combinators over the kernel's
//!   inference rules — see [`rewrite`] and [`nat`];
//! * a set of *temporary postulates* (`Thm::assume`-style with a
//!   self-hyp audit trail) for rules the kernel doesn't yet supply —
//!   see [`mod@bool`] for the HOL connective intro / elim
//!   rules. These
//!   are slated to disappear once the connectives are built into the
//!   kernel (the target axiom set is content-addressing only).
//!
//! Core tactics can't produce a false `Thm` independently; they're
//! plumbing that turns multi-step kernel sequences into one-line
//! call sites. Postulated rules sit behind a `LazyLock<Thm>` so
//! every consumer shares a single instance.

pub mod bool;
pub mod nat;
pub mod rewrite;
