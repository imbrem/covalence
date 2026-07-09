//! # `covalence_pure::api` — the SUPPORTED consumer surface of the base
//!
//! A curated re-export set: exactly the items downstream kernel crates
//! (`covalence-core`, `covalence-hol-eval`, `covalence-pure-eval`) consume
//! today, as inventoried in `notes/vibes/base-api-surface.md`. Pure re-exports
//! — importing through here is byte-for-byte the same as importing from the
//! crate root, so there is **zero behavior change** and zero TCB delta.
//!
//! ## CONTRACT (what is stable vs. implementation detail)
//!
//! The base is slated for a severe refactor (`notes/vibes/base-abstraction.md`,
//! `notes/vibes/base-relcalc-holomega-design.md` Fronts D/E): all computation
//! moves into **untrusted relation evaluation** (`rel::execute`-style positive
//! graph membership) and axioms become simple propositions of the shape
//! `Computation(i, o) ⟹ SomeRelation(i, o)`. This module is the line that
//! refactor must not move:
//!
//! **STABLE — the certificate algebra.** Everything re-exported here keeps its
//! meaning (though not necessarily its implementation):
//! - the unforgeable certificate [`Thm`] with its read accessors
//!   ([`Thm::prop`]/[`Thm::lang`]) and the ungated transport calculus
//!   (`refl`/`sym`/`trans`/`eq_mp`/`cong_app`/`cong_pair`/`lift`);
//! - the gated mints [`apply`]/[`apply0`]/[`canon`];
//! - the trust enumeration: [`Language`] (`admits`/`extends`/`union`),
//!   [`Manifest`]/[`RuleRecord`]/[`LangMeta`]/[`RuleMeta`], and the admitted-rule
//!   traits [`Rule`]/[`CanonRule`];
//! - the proposition vocabulary: [`Expr`]/[`Op`]/[`App`]/[`Val`]/[`Eqn`], the
//!   bit-exact float leaf sorts [`F32`]/[`F64`], and [`Error`].
//!
//! **STABLE but expected to become *derived*.** [`canon`]'s functional equation
//! `⊢ f(a) = b` will eventually be derivable from a relation run plus an
//! admitted functionality axiom instead of a primitive gate ([`CanonRule`]
//! likewise demotes from "trusted eval seam" to "an untrusted [`UntrustedFn`]
//! whose functionality is separately axiomatized"). The *signatures* stay; the
//! trust story behind them shrinks.
//!
//! **IMPLEMENTATION DETAIL — everything not re-exported here.** In particular:
//! the leaf-equality injectors (`of_eq`/`of_eq_with`/`of_ptr_eq`/`semidecide`,
//! `trans_ptr`), the extra expression shapes (`Ref`/`Dyn`/`True`/`False`,
//! `TrustedDeref`), the pure bool theory (`And`/`Or`/`Imp`/`Not` and the
//! `and_*`/`or_*`/`mp` methods), the `MatchApp`/`Rewrite`/`apply_rewrite` seam,
//! the Phase-0 relation calculus (`UntrustedFn`/`Rel`/`execute` and the
//! positive combinators), the concrete trusted-float op inventory
//! (`F32Add`…), and the HOL-ω reflection (`tyrep`/`kind`/`kindcheck`). These
//! remain reachable at the crate root (nothing is hidden — hiding re-exports
//! would be a breaking change for base-internal tests and would not shrink the
//! TCB), but they are **slated to be reshaped** by the relations refactor:
//! new code outside `crates/kernel/base/` must not grow dependencies on them
//! without updating the inventory note. Note the relation calculus is
//! implementation detail only in the sense that its *current shape* is
//! pre-Front-E; it is the direction the base is moving toward, not away from.
//!
//! Consumers are NOT yet migrated to `use covalence_pure::api::…` — this
//! module documents and pins the supported set first; the import rewrite is a
//! separate mechanical step after in-flight core work merges.

// ---- The certificate + its calculus (trust-bearing) ----
pub use covalence_pure_trusted::{Error, Thm, apply, apply0, canon};

// ---- The trust enumeration (languages, manifests, admitted rules) ----
pub use covalence_pure_trusted::{
    CanonRule, LangMeta, Language, Manifest, Rule, RuleMeta, RuleRecord,
};

// ---- The proposition vocabulary (freely constructible; proves nothing) ----
pub use covalence_pure_trusted::{App, Eqn, Expr, F32, F64, Op, Val};
