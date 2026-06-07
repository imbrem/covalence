//! Covalence HOL kernel.
//!
//! See `docs/prover-architecture.md` for the conceptual model and
//! `docs/prover-mvp-plan.md` for the staged build-out.
//!
//! Surface layers:
//! - [`Kernel`] — ergonomic facade with term builders + proof methods.
//! - [`Arena`] + [`Thm`] — the lower-level primitives.
//!
//! # ⚠️ Status: experimental, planned for full rewrite
//!
//! This kernel is **not** the soundness-critical, audited
//! production kernel. It's an experimental staging implementation
//! that exists so the surrounding crates (frontend bridges,
//! OpenTheory import, Alethe import, the `Prover` trait) can be
//! built and tested end-to-end against *something* — and so any
//! missing primitives can be added incrementally rather than
//! up-front.
//!
//! Known soundness-affecting holes and rough edges (incomplete
//! list — assume there are more):
//!
//! - **Trust escape hatches.** [`Thm::abs_unchecked`] skips the
//!   `VariableEscapesAssumption` check. Frontends call it when they
//!   know the var is safe; if they're wrong, the resulting `Thm` is
//!   unsound. The eventual kernel will replace this with a proper
//!   "axiom set" representation that lets the safe `Thm::abs` rule
//!   succeed without the escape hatch.
//!
//! - **Auto-`infer` in `alloc_term` papers over stale-cache bugs.**
//!   The cache on a `TermId` can drift after substitution or after
//!   a child's cache changes for reasons outside this term's own
//!   structure. We re-walk on every allocation; that's a
//!   performance cliff and the eventual rewrite should keep caches
//!   coherent without it.
//!
//! - **`subst_tyvar_in_term` / `subst_tyvar_in_type` treat
//!   `Subset` types opaquely.** Subset types whose parent or
//!   predicate carries the substituted tyvar won't be updated. Use
//!   only for HOL Light-style monomorphic instantiation of leaf
//!   constants until this is fixed.
//!
//! - **`Thm::deduct_antisym_rule` drop logic depends on
//!   `uf.eq_at_level_0`.** If a hypothesis's concl is α-equivalent
//!   to the exclude term but not UF-canonical-equal (e.g. raw
//!   `Comb(Const "!", λ)` vs folded `Forall(λ)`), the drop misses
//!   it. The shell bridges pre-union shape pairs before calling the
//!   rule; the eventual kernel should consider shape-equivalent
//!   forms natively.
//!
//! - **`Thm::beta` and other rules used to leak `ILL_TYPED` caches
//!   into their `Eq` results.** The current workaround is the
//!   auto-`infer` in `alloc_term`; the eventual fix should be at
//!   the rule level so we can drop the auto-`infer`.
//!
//! Recently fixed:
//!
//! - **Linear-scan dedup → HashMap hash-cons.** `alloc_term`,
//!   `alloc_type`, `intern_tyargs`, and `intern_string` now use
//!   `HashMap<Content, Id>` instead of `Vec::iter().position(..)`,
//!   bringing dedup back to amortized O(1).
//!
//! - **`intern_tyargs` dedup.** A long-standing bug let every
//!   `intern_tyargs(vec![])` allocate a fresh `TyArgsId`, which
//!   inflated nullary `Tyapp`s to distinct `TypeRef`s and broke
//!   polymorphic-instance equality across rules.
//!
//! Soundness-critical work (auditing, hardening, proof of
//! soundness against an explicit logical semantics, hashing model,
//! …) is **explicitly out of scope** for this version. Don't
//! deploy this kernel where soundness matters.

pub mod arena;
pub mod egraph;
pub mod eprop;
pub mod hash;
pub mod id;
pub mod kernel;
pub mod primop;
pub mod prop;
mod reduce;
pub mod subst;
pub mod term;
pub mod ty;
pub mod uf;

pub use arena::{Arena, SubsetError, UnionError};
pub use egraph::Egraph;
pub use eprop::{EProp, EThm};
pub use id::{
    BytesId, ImportId, IntId, NatId, StrId, TermId, TermSubstId, TyArgsId, TyVarId, TypeId,
    TypeSubstId, VarId,
};
pub use kernel::Kernel;
pub use primop::{PrimOp1, PrimOp2};
pub use prop::{Context, ProofError, Prop, Thm};
pub use subst::{TermSubst, TypeSubst};
pub use term::{Packed64, TermDef, TermKind, TermRef};
pub use ty::{TypeInfo, TypeKind, TypeRef};
pub use uf::{TermProps, TermUf};
