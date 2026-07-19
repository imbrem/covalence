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
//! - **ε-assembly** ([`recursor`]) — done and generic: `recursion_theorem`
//!   builds the recursor (Hilbert choice over the graph), proves its
//!   per-constructor equations, and `∃`-introduces over the caller's `defs`
//!   recursor predicate. `nat` consumes it.
//!
//! The construction is **complete**: `nat`'s recursion theorem is the engine
//! at the `nat` signature end to end. What remains is *lifting* — supplying
//! a non-kernel [`Inductive`] impl (`nat`-from-`ind`, or `list`'s derived
//! induction + freeness) to drive the same engine — and the
//! multi-recursive-argument cases. Both are tracked in the generated open-work index.
//!
//! ## The inductive-types API (`covalence-inductive`)
//!
//! This module also hosts the **HOL backends** for the logic-agnostic
//! [`covalence_inductive`] API: [`api`] (the `Logic`/`LogicOps` glue for
//! [`hol::NativeHol`] + shared derivations), [`church`] (the
//! impredicative/Church backend — realizes *any* v1 spec, junk-guarded by a
//! `Wf` membership predicate), and [`engine`] (the exact-type adapter over
//! this very recursion engine — `nat` today). Consumers hold an
//! [`InductiveTheory`](covalence_inductive::InductiveTheory) bundle and
//! never see the representation; swapping backends is passing the other
//! value (`engine::tests::backend_swap_same_consumer`).

pub mod api;
mod bytes_api;
pub mod carved;
pub mod church;
pub mod data;
pub mod determinacy;
pub mod engine;
pub mod existence;
pub mod graph;
pub mod hol;
mod nat_api;
mod nat_backend_common;
#[cfg(test)]
mod nat_backend_tests;
mod nat_binary_api;
mod nat_unary_api;
pub mod recursor;
pub mod sig;
pub mod uniqueness;
mod util;
pub mod variant;

pub use carved::{CarvedSExpr, CarvedSExprBackend, carved, carved_backend};
pub use church::ImpredicativeBackend;
pub use data::Inductive;
pub use engine::{NatEngineBackend, nat_backend, nat_spec};
pub use nat_binary_api::DoubleSuccNat;
pub use nat_unary_api::UnaryNat;
pub use sig::{Arg, Constructor, GenArg, GenConstructor, GenSig, InductiveSig};
pub use variant::{
    ChurchBackend, CoprodBackend, CoprodVariantTheory, VCtor, Variant, VariantBackend,
    VariantTheory, VariantTheoryBackend, self_ty_var,
};
