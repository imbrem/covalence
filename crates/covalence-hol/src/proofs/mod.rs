//! Proof helpers built on top of the `covalence-core` kernel.
//!
//! Nothing here is part of the TCB. Each submodule is one of:
//!
//! * a set of *postulates* (`Thm::assume`-style with a self-hyp
//!   audit trail) for rules whose `Thm::define`-based derivation
//!   hasn't landed yet — see [`bool`] for HOL connective intro /
//!   elim rules;
//! * a set of *pure tactics* — combinators over the kernel's
//!   inference rules — see [`rewrite`] and [`nat`].
//!
//! Pure tactics can't produce a false `Thm` independently; they're
//! plumbing that turns multi-step kernel sequences into one-line
//! call sites. Postulated rules sit behind a `LazyLock<Thm>` so
//! every consumer shares a single instance.

pub mod bool;
pub mod nat;
pub mod rewrite;
