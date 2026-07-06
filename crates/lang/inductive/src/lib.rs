//! **The inductive-types API** — a logic-agnostic vocabulary for *simple*
//! inductive datatypes, abstracting over their **representation**.
//!
//! ## The shape
//!
//! - [`InductiveSpec`] — a **plain-data** description of a datatype
//!   (constructors + argument sorts), generic over an external-sort token
//!   `X` and free of any logic's term/type values. Serializable,
//!   content-addressable, comparable.
//! - [`Logic`] / [`LogicOps`] — the two-tier logic abstraction. Tier 1 is
//!   just the carrier types (`Type`/`Term`/`Thm`/`Error`) — all a backend
//!   needs to *deliver* a bundle. Tier 2 adds construction + a minimal HOL
//!   rule surface, for generic machinery built *on top of* bundles.
//! - [`InductiveTheory`] / [`InductiveFacts`] — what a backend realizes from
//!   a spec: the carrier type, a **membership predicate**, the constructor
//!   terms, and the characteristic theorems (computation, freeness, cases,
//!   induction, membership plumbing) behind rule-form methods.
//! - [`InductiveBackend`] — the realization seam. Two backends *within the
//!   same logic* (e.g. HOL's impredicative Church encoding vs. the
//!   typedef + recursion-theorem engine) implement the same trait, so
//!   consumers swap representations without changing a line.
//!
//! ## The membership-relativized contract
//!
//! Every theorem in the bundle is stated **relative to the membership
//! predicate** [`InductiveTheory::mem`]: induction concludes
//! `∀t. mem t ⟹ P t`, cases guards with `mem t`, and so on. This is the
//! honest common denominator across representations: an exact-type backend
//! (a carved subtype) has `mem = λt. ⊤` and supplies
//! [`InductiveFacts::mem_trivial`] so consumers discharge the guard for
//! free; a junk-carrying encoding (an impredicative/Church carrier) has a
//! genuine well-formedness `mem`; an untyped set-theoretic backend is
//! membership-relativized natively. See [`theory`] for the full contract
//! (term conventions, observation instances, capability flags).
//!
//! ## Scope (v1)
//!
//! A **single, non-indexed, strictly-positive, first-order, directly
//! recursive** datatype: every recursive constructor argument is the
//! inductive type itself (never `T → …` nor `F⟨T⟩`). Mutual blocks, nested
//! recursion, spec-level parameters, and indexed families are explicitly
//! *later* scope; the data model is shaped so they land additively (new
//! [`ArgSort`] variants + backend capability flags).
//!
//! Design rationale: `notes/vibes/inductive-api-design.md`.

pub mod backend;
pub mod conformance;
pub mod error;
pub mod logic;
pub mod spec;
pub mod theory;

pub use backend::InductiveBackend;
pub use error::{IndResult, InductiveError, SpecError};
pub use logic::{Logic, LogicOps, beta_expand, beta_reduce};
pub use spec::{ArgSort, CtorSpec, InductiveSpec};
pub use theory::{BackendCaps, InductiveFacts, InductiveTheory};
