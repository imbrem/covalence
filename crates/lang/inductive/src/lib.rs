//! **Polynomial datatype APIs** — logic-agnostic vocabularies for aggregate
//! types and least/greatest fixpoints, abstracting over their
//! **representation**.
//!
//! ## The shape
//!
//! - [`RecordSpec`], [`VariantSpec`], and [`EnumSpec`] — non-recursive
//!   aggregates, all represented by the same named sum-of-products model.
//! - [`PolynomialSpec`] / [`FixpointSpec`] — the shared functor vocabulary
//!   and separate least/greatest realization seams
//!   ([`InductiveFixpointBackend`] / [`CoinductiveFixpointBackend`]).
//! - [`InductiveSpec`] — the compatibility **plain-data** description
//!   of a simple datatype
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
//! - [`RecordTheory`], [`VariantTheory`], [`EnumTheory`],
//!   [`LeastFixpoint`], and [`GreatestFixpoint`] — shared proof-bearing
//!   contracts. Backends may implement only the capabilities they can
//!   actually prove; the older opaque seams remain as compatibility APIs.
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

pub mod aggregate;
pub mod backend;
pub mod conformance;
pub mod error;
pub mod fixpoint;
pub mod functor;
pub mod logic;
pub mod logic_api;
pub mod polynomial;
pub mod spec;
pub mod stream;
pub mod theory;
pub mod validated;

pub use aggregate::{
    AggregateRealizeError, EnumBackend, EnumFacts, EnumTheory, ProofBearingEnumBackend,
    ProofBearingRecordBackend, ProofBearingVariantBackend, RecordBackend, RecordFacts,
    RecordTheory, VariantBackend, VariantFacts, VariantTheory, realize_enum, realize_record,
    realize_variant,
};
pub use backend::InductiveBackend;
pub use error::{IndResult, InductiveError, SpecError};
pub use fixpoint::{
    CoinductiveFixpointBackend, FixpointCore, FixpointIsoFacts, FixpointNoConfusionFacts,
    FixpointSpec, GreatestFixpoint, GreatestFixpointFacts, InductiveFixpointBackend, LeastFixpoint,
    LeastFixpointFacts, NoConfusionLeastFixpoint, ProofBearingGreatestFixpointBackend,
    ProofBearingLeastFixpointBackend, RealizeError, realize_coinductive, realize_inductive,
};
pub use functor::{
    StructuralFunctorAction, StructuralFunctorLaws, StructuralPolynomial, StructuralPolynomialError,
};
pub use logic::{Logic, LogicOps, beta_expand, beta_reduce};
pub use logic_api::LogicApiAdapter;
pub use polynomial::{
    EnumSpec, FieldSpec, FunctorExpr, PolynomialBuilder, PolynomialSpec, Position, RecordBuilder,
    RecordSpec, VariantCase, VariantSpec,
};
pub use spec::{ArgSort, CtorSpec, InductiveSpec};
pub use stream::{
    ReferenceStream, ReferenceStreamBackend, StreamBisimulation, StreamBisimulationStep,
    StreamLayer, StreamObservation, check_bisimulation_prefix, stream_fixpoint, stream_functor,
};
pub use theory::{BackendCaps, InductiveFacts, InductiveTheory};
pub use validated::Validated;
