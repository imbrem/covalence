//! # `covalence-hol-api` — the high-level, TRAIT-backed HOL consumer surface
//!
//! A consumer layer **above** the kernel. The point: application code and
//! theory-building code should construct terms and theorems through a small
//! set of traits — [`Hol`] (the value-typed HOL Light surface: term builders +
//! the primitive/derived inference rules) and [`Nat`] (natural-number ops +
//! the commonly-needed Peano lemmas by name) — rather than reaching into
//! `covalence_core::TermKind` / `Term` directly. Then the *only* code that
//! mentions the concrete backend is the trait **impl** ([`NativeHol`]), and
//! swapping the backend (an arena kernel, an internal/object-level HOL, a
//! different literal representation) is a matter of writing one new impl, not
//! porting every consumer.
//!
//! ## What lives here
//!
//! - [`Hol`] / [`NativeHol`] — re-exported from `covalence-init`'s inductive
//!   engine, where the value-typed HOL trait was first grown to make that
//!   engine backend-generic. This crate *promotes* it to a first-class,
//!   supported consumer API (the engine's use is one client among many).
//! - The generic HOL helpers ([`cong_arg`], [`conjuncts`], [`rewrite`],
//!   [`beta_expand`], …) — free functions over any [`Hol`].
//! - [`LogicOps`] / [`Logic`] and the inductive API ([`InductiveSpec`], …) —
//!   re-exported from `covalence-inductive` so a consumer names one crate.
//! - [`nat`] — the new [`Nat`] trait: `zero`/`succ`/`lit` term builders,
//!   `add`/`mul`, and accessors for the workhorse Peano theorems, implemented
//!   for [`NativeHol`] by delegating to `covalence_init`.
//!
//! ## Trust
//!
//! Zero TCB delta. Every method delegates to an already-audited
//! `covalence-core` / `covalence-init` operation; this crate declares no
//! [`Language`](covalence_core) rule and cannot reach `Thm`'s private mint.
//! The golden manifests are byte-identical.
//!
//! Design: `notes/vibes/backend-decoupling.md`.

pub mod int;
pub mod nat;
pub mod omega;
pub mod order;
pub mod succ;
pub mod wasm;

/// Dependency-free logic carriers, capabilities, and relational algebra.
///
/// Theory APIs should prefer these traits to concrete native HOL values.
pub use covalence_logic_api as logic;
pub use covalence_logic_api::{
    Arrow, BinderRules, Category, Decision, EqualityRules, EqualitySyntax, Logic as LogicApi,
    QuantifierSyntax, RelationAlgebra, RelationEvidence, RelationJudgmentSyntax,
    RelationOrderDecision, RelationOrderLaws, RelationProperty, RelationPropertyEvidence,
    RelationPropertySyntax, TermLanguage, TheoremView, TypeSystem,
};

// ---- The HOL trait surface + native backend (promoted from the inductive
//      engine, where it was first grown) ----
pub use covalence_init::init::inductive::hol::{
    Hol, NativeHol, and_all, beta_expand, beta_nf_concl, beta_nf_expand, beta_reduce, cong_arg,
    cong_fn, conj, conjuncts, discharge_conj, project, rewrite,
};

// ---- The logic-agnostic inductive-types API (a consumer names one crate) ----
pub use covalence_inductive::{
    ArgSort, BackendCaps, CtorSpec, InductiveBackend, InductiveFacts, InductiveSpec,
    InductiveTheory, Logic, LogicOps,
};
pub use covalence_init::init::inductive::{
    CoprodVariantTheory, VariantTheory, VariantTheoryBackend,
};

// ---- The certificate + core vocabulary the traits are stated over ----
pub use covalence_core::{Error, Result, Term, Type};
pub use covalence_hol_eval::EvalThm as Thm;

pub use int::Int;
pub use nat::{
    Nat, NatAdditiveLaws, NatArithmetic, NatEqDecision, NatFreeness, NatLaws,
    NatMultiplicativeLaws, NatNormalization, NatOrder, NatRecursionLaws, NatSyntax,
};
pub use order::{Discharger, EvalDischarger, LinOrder, Strict};
pub use succ::{SuccDischarger, SuccHol};

// ---- The reflected HOL-omega TYPE layer (type-operator variables + kinds) ----
pub use omega::{HolOmega, InstError, NativeHolOmega, OmegaLang};

// ---- The high-level SpecTec-fragment API (grammars + relations over the core) ----
// Reusable, trait-based surface for the universally useful pieces of a SpecTec
// spec: `GrammarEnv` (grammars → `Derives_E`) and `RelationEnv` (relations →
// `Derivable_R`) both implement the `Fragment` trait. Defined in `covalence-init`
// next to the engines; re-exported here so consumers name one crate.
pub use covalence_init::grammar::cfg::GrammarEnv;
pub use covalence_init::grammar::spectec::{
    GrammarInstance, GrammarInstanceKey, GrammarRoot, GrammarRootError, IndexedGrammarEnv,
    IndexedGrammarError, IndexedLoweringRefusal, IndexedLoweringReport, IndexedLoweringResidual,
    IndexedProduction, IndexedProductionLowerer, ParameterizedGrammarIr, PremiseFreeRegexLowerer,
    RootedGrammarEnv, spec_grammar_env_recognition_roots, wasm3_indexed_grammar_env,
};
pub use covalence_init::spectec::{
    DefinitionKind, DefinitionRef, FragPremise, Fragment, HolSpec, RelationEnv, SpecTecSpec,
};

// ---- The whole-spec total load + spec slices (the WASM-semantics surface) ----
// The bundled WASM 3.0 spec loads as ONE kernel-checked rule set
// (`total_spec_clauses` / `total_rule_set`, censused by `TotalReport`; drive
// whole-spec ops through `with_total_stack`). `SpecSlice`/`SliceEnv` carve
// named premise-closed sub-specs out of it (presets: `lime_slice` — the
// maximally-fireable core; `wasm1_slice`/`wasm2_slice` — approximate 1.0/2.0
// feature subsets), and `transport` lifts a slice theorem into the full set,
// kernel-derived — the `1.0 ⊆ 2.0 ⊆ 3.0` seed. `SliceEnv` implements
// `Fragment` too. See `covalence_init::wasm::lower::slice`'s module docs for
// a build → carve → derive → transport example.
pub use covalence_init::wasm::lower::slice::{
    SliceEnv, SliceReport, SliceSeed, SpecSlice, exec_slice, lime_slice, transport, wasm1_slice,
    wasm2_slice,
};
// Positive, adequacy-gated decision seam for SpecTec `otherwise` guards that
// depend on non-derivability of an earlier relation judgement. Implementors
// supply certified graph relations; the default remains honestly opaque.
pub use covalence_init::wasm::lower::decision::{
    CertifiedDecisionCase, CertifiedDecisionFamily, DecisionAnswer, DecisionLowerer,
    DecisionRequest, OpaqueDecisions,
};
pub use covalence_init::wasm::lower::total::{
    ClauseMeta, OpaquePremiseSite, TotalReport, total_rule_set, total_spec_clauses,
    with_total_stack,
};
// Lossless source-type layer: refinement-preserving shapes plus deterministic
// dependency/SCC analysis, ready for semantic HOL-sort backends.
pub use covalence_init::wasm::sort::{
    CarrierTypeResolver, HolSort, RefinementAwareTypeResolver, ResolvedType, SemanticTypeResolver,
    SortInvariant, TypeProvenance,
};
pub use covalence_init::wasm::type_family::{
    CaseShape, FamilyInstance, FieldShape, TypeFamilies, TypeFamily, TypeFamilySource, TypeShape,
    coprod_variant_theory,
};
// Execution traces (Wave G): chain single-`Step` theorems through the spec's
// own `Steps/refl`+`Steps/trans` into multi-step runs; `TraceEnv` also
// packages the `Step/pure`/`Step/read` lifts, the `Step/ctxt-instrs` framing
// (`frame`) and the ground `ev.*` evaluation helpers. `exec_slice` is the
// smallest preset on which the const-fold+drop demo executes.
pub use covalence_init::wasm::lower::trace::{Config, TraceEnv, TraceStep, const_fold_drop_trace};
pub use covalence_init::wasm::spec::wasm_spec;
