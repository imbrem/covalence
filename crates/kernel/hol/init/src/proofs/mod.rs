//! Proof helpers built on top of the `covalence-core` kernel.
//!
//! Nothing here is part of the TCB. [`rewrite`] is a set of *pure
//! tactics* — combinators over the kernel's inference rules
//! (`beta_nf`, `unfold_at_*`, congruence/rewriting) that turn
//! multi-step kernel sequences into one-line call sites. They can't
//! produce a false `Thm` independently; they're plumbing.
//!
//! The connective / quantifier rules are zero-TCB derivations
//! (`covalence_hol_eval::derived::DerivedRules`, re-exported through
//! [`crate::init::ext`]) and the `nat` facts live in
//! [`crate::init::nat`].

pub mod rewrite;
