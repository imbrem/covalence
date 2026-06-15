//! Infrastructure for **basic inductive types** — the generic recursion
//! engine that `nat`, `list`, and future first-order inductives share.
//!
//! In this kernel no inductive type is primitive: each is a conservative
//! subtype of some carrier (`nat` is the kernel's, `list α` is
//! `stream (option α) where finite`), with constructors, and *derived*
//! recursion / induction. The per-type work splits into two independent
//! feeders and one generic engine:
//!
//! ```text
//!   FEEDER 1  carrier + predicate ─► constructors + FREENESS (Cᵢ inj,
//!             Cᵢ ≠ Cⱼ) + INDUCTION ((⋀ caseᵢ) ⟹ ∀t. P t)
//!                                          │
//!   ENGINE    [induction + freeness] ─► ⊢ ∃rec. P_rec rec   (this module)
//!                                          │
//!   FEEDER 2  spec_ax transfer ─► the recursor's ε-equations hold
//! ```
//!
//! [`sig`] is the engine's vocabulary — an [`InductiveSig`] describing a
//! type's constructors. [`graph`] is the first engine layer: the pure
//! term builders for the impredicative recursion graph, generic over a
//! signature.
//!
//! ## Status
//!
//! The term layer ([`graph`]) is in place and consumed by `nat`'s
//! construction in [`crate::init::recursion`]. The *proof* layer — the
//! per-constructor inversion lemmas, totality / determinacy by the
//! supplied induction principle, and the ε-assembly — is still specialised
//! to `nat` in that module; generalising it over an arbitrary
//! [`InductiveSig`] (and deriving `list`'s induction principle to feed it)
//! is tracked in `SKELETONS.md`.

pub mod graph;
pub mod sig;

pub use sig::{Arg, Constructor, InductiveSig};
