# Skeletons — `covalence-hol/src/models`

Open placeholders in the minimal surface-compiler core (the `Logic`/`Model`
triad + cross-model `add_comm` replay). See `CLAUDE.md` § Skeletons. Design:
[`docs/theories-models-and-logics.md`](../../../../docs/theories-models-and-logics.md)
§1/§1.1, [`docs/surface-compiler.md`](../../../../docs/surface-compiler.md) §2/§3.

## Severe / blocking

- **No general `Signature`/`admits`.** `Logic::nat_model()` is specialized to the
  fixed `Nat` signature, not `interpret(&Signature)` over an arbitrary signature
  with an `admits` statability gate. Signatures are also single-sorted + first-order:
  multi-sort and the `(family m (-> ty ty))` kind-ty→ty families (HOL-ω,
  `surface-compiler.md` §3.0) are rejected.
- **No model synthesis (§3.0.4 north star).** Models are hand-declared via
  `(#model …)`; no tactic synthesizing a model from a theory (subsuming
  `#inductive`), no `#data`/`#codata` theory forms.

## Polish / increments

- **Partial `HandlerSet`.** Only the induction handler (`m.induct`) dispatches per
  model; rewriter/unifier/reducer still come from the model-agnostic `Env` seams.
  `lift_string`/`lift_bytes` return `Err(NoLiteral)` for both `Nat` models.
- **No typed `.sig`/`.thy`/`.mod` imports.** `(#import x.sig #sig)` (§3.0/§3.0.1)
  is unbuilt; bodies are inlined into `declared.cov` rather than imported by type.
- **`(from WITNESS)` is transitional.** `(#models nat/unary …)` pulls specs from the
  Rust `models::unary::prelude()` env (re-checked, so sound) until those proofs port
  to `.cov` (keeps `unary.rs` non-self-contained).
- **`#models` registers no `.thm` certificate.** Verified axioms accumulate as
  lemmas + bless the dispatch env, but there is no first-class `M ⊨ T` proof value
  carrying its logic (§3.0.2).
- **`#in MODEL` only accepts `#thm`.** Nested `#def`/`#have`/`#in`, `#transport`
  across models, and isomorphic-model dispatch (§4) are unimplemented.
- **Two models, one theory, no iso.** `Nat` has `nat/self` + `nat/unary` with no
  proved morphism/iso between them (the `nat ≅ list unit` length iso of
  theories-models §2.1/§2.2) and no iso registry.
