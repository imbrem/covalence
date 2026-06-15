//! Proof helpers built on top of the `covalence-core` kernel.
//!
//! Nothing here is part of the TCB. [`rewrite`] is a set of *pure
//! tactics* — combinators over the kernel's inference rules
//! (`beta_nf`, `unfold_at_*`, congruence/rewriting) that turn
//! multi-step kernel sequences into one-line call sites. They can't
//! produce a false `Thm` independently; they're plumbing.
//!
//! The old `bool` (HOL connective intro/elim *postulates*) and `nat`
//! helper modules were removed: the connectives are now kernel
//! primitives (`and_intro`, `or_elim`, … on [`covalence_core::Thm`])
//! and the `nat` facts live in [`crate::init::nat`]. Recover them from
//! the `backup/pre-hol-cleanup` branch if ever needed.

pub mod rewrite;
