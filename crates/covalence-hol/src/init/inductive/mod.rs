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
//! trait through which the engine consumes induction (and later freeness),
//! so the *same* machinery serves both today's kernel-primitive `nat` and a
//! future HOL-internal one. [`graph`] is the term layer (the impredicative
//! recursion graph); [`existence`] is the first proof layer (per-constructor
//! graph introduction + totality).
//!
//! ## Status
//!
//! - **Term layer** ([`graph`]) — done; consumed by `nat`'s construction in
//!   [`crate::init::recursion`].
//! - **Existence** ([`existence`]) — done and generic: `graph_intro` /
//!   `graph_total` over any [`Inductive`]. `nat` consumes them.
//! - **Uniqueness** (per-constructor inversion + determinacy) and the
//!   **ε-assembly** — still specialised to `nat` in [`crate::init::recursion`];
//!   generalising them (they additionally need constructor freeness on the
//!   [`Inductive`] trait) and deriving `list`'s induction principle to feed
//!   the engine are tracked in `SKELETONS.md`.

pub mod data;
pub mod existence;
pub mod graph;
pub mod sig;

pub use data::Inductive;
pub use sig::{Arg, Constructor, InductiveSig};
