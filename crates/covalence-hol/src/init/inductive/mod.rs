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
//! type's constructors. [`data`] is the lifting seam — the [`Inductive`]
//! trait through which the engine consumes induction **and constructor
//! freeness**, so the *same* machinery serves both today's kernel-primitive
//! `nat` and a future HOL-internal one. [`graph`] is the term layer (the
//! impredicative recursion graph); [`existence`] and [`uniqueness`] are the
//! proof layers.
//!
//! ## Status
//!
//! - **Term layer** ([`graph`]) — done; consumed by `nat`'s construction in
//!   [`crate::init::recursion`].
//! - **Existence** ([`existence`]) — done and generic: `graph_intro` /
//!   `graph_total` over any [`Inductive`]. `nat` consumes them.
//! - **Uniqueness — inversion** ([`uniqueness`]) — done and generic:
//!   `graph_inv` over any [`Inductive`], its `Good`-relation closedness
//!   discharged by the trait's `injective` / `distinct`. `nat` consumes it.
//! - **Uniqueness — determinacy** ([`determinacy`]) — done and generic:
//!   `graph_det` folds the supplied induction over `graph_inv`. `nat`
//!   consumes it. (Multi-recursive-argument constructors not yet handled.)
//! - **ε-assembly** — the only remaining `nat`-specific piece (in
//!   [`crate::init::recursion`]); it couples to the recursor's `defs`
//!   selector predicate. Generalising it, and deriving `list`'s induction
//!   principle + freeness to feed the engine, are tracked in `SKELETONS.md`.

pub mod data;
pub mod determinacy;
pub mod existence;
pub mod graph;
pub mod sig;
pub mod uniqueness;
mod util;

pub use data::Inductive;
pub use sig::{Arg, Constructor, InductiveSig};
