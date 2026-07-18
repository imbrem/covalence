//! Source-local open work for this module/crate.
//!
//! Migrated from the former Markdown registry. Move markers beside the relevant
//! implementation as the area is touched; `bun run todos` provides the index.

// TODO(cov:kernel.base.evaluate-seam-decision-evaluation, severe): Evaluate seam (decision + evaluation): the kernel has no disequality /
// TODO(cov:kernel.base.stage-1-adts-set-t-interpset, severe): Stage 1 ADTs + Set<T>/InterpSet: the abstract-sort + interpretation
// TODO(cov:kernel.base.stage-2-hol, severe): Stage 2 HOL: HolTy/HolTm<V> ops, Fv/Bv/subst/β as
// TODO(cov:kernel.base.stage-3-text-builtins-stage-4-cov, severe): Stage 3 Text builtins + Stage 4 Cov: the Nat/Int/Bytes/fixed-width
// TODO(cov:kernel.base.stage-5, severe): Stage 5: Wasm/X86 languages. The WASM f32/f64 numeric op inventory
// TODO(cov:kernel.base.positive-only-boundary-is-a-standing-soundness-invariant, major): Positive-only boundary is a STANDING soundness invariant: execute's
// TODO(cov:kernel.base.rest-of-the-positive-calculus, major): Rest of the positive calculus: only transpose shipped; compose/join/
// TODO(cov:kernel.base.op-val-collapse-not-attempted, major): Op/Val collapse not attempted: the design's unification of ops and
// TODO(cov:kernel.base.tyrep-uses-a-demo-rep, major): TyRep uses a demo rep: the constructors are generic; full core::Type
// TODO(cov:kernel.base.hol-middle-language, major): HOL-ω middle language: deferred entirely (design Appendix A); needs a real
// TODO(cov:kernel.base.kindcheck-recursion-has-no-depth-guard, major): kindcheck recursion has no depth guard: kindof/rankof are unbounded
// TODO(cov:kernel.base.tyc-kindc-are-the-demo-rep, major): TyC/KindC are the DEMO rep: the real oracle is over core::Type (the
// TODO(cov:kernel.base.middle-hol-rules-not-built, major): Middle HOL-ω rules not built: TyInst (rank side-condition consuming
// TODO(cov:kernel.base.facade-algebra-not-yet-consumed-by-core-eval, minor): Facade/algebra not yet consumed by core/eval: src/api.rs (curated
// TODO(cov:kernel.base.rewrite-conclusion-is-shape-erased, minor): Rewrite conclusion is shape-erased: applyrewrite mints
// TODO(cov:kernel.base.covalence-pure-derive-proc-macros, minor): covalence-pure-derive (proc macros): not built (and no proc-macro crate /
// TODO(cov:kernel.base.op-reference-forwarding-is-static-f-only, minor): Op reference forwarding is &'static F only: the Op: Any supertrait
// TODO(cov:kernel.base.unsized-sorts, minor): Unsized sorts: Ref requires P::Target: Sized, so str/[T] can't be
// TODO(cov:kernel.base.non-static-rules, minor): Non-'static rules: the Rule::Id tag seam was removed (it was
// TODO(cov:kernel.base.dyn-expr-is-opaque, minor): dyn Expr is opaque: Box<dyn Expr> is a genuine (sealed) expression but
// TODO(cov:kernel.base.canon-only-on-ground-args, minor): canon only on ground args: canon takes arg: F::In and forms
