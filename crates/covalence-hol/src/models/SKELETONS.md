# Skeletons — `covalence-hol/src/models`

Intentional placeholders in the minimal surface-compiler core (the
`Logic`/`Model` triad + cross-model `add_comm` replay). See `CLAUDE.md`
§ Skeletons and the [crate index](../SKELETONS.md). Design:
[`docs/theories-models-and-logics.md`](../../../../docs/theories-models-and-logics.md)
§1/§1.1, [`docs/surface-compiler.md`](../../../../docs/surface-compiler.md) §2/§3.

This module is deliberately the *dumbest dispatch that works*: it pins the
abstractions in code (the objective function — one `add_comm` proof, two
models — passes) and leaves the generalizations below for later.

## The `Logic` trait is `Nat`-specialized

`Logic::nat_model()` is `interpret`+`handlers` specialized to the **fixed**
`Nat` signature, not the doc's `interpret(sig: &Signature)` over an arbitrary
signature (with `admits` as the statability gate). Deferred:

- **A first-class `Signature` type** (type constants + families + typed
  operation symbols) and `Logic::interpret(&Signature)` / `admits` over it, so
  `Monoid`/`Ring`/`CompleteOrderedField` reuse the same machinery (today
  `init::monoid` carries its own parallel `Monoid` value).
- **The full `HandlerSet`.** Only the induction handler (`m.induct`) is
  dispatched per model; the rewriter/unifier/reducer handlers still come from
  the model-agnostic `Env` seams (`beta`/`congr`/`funext`/`comp_default`).
- **`lift_string` / `lift_bytes`** return `Err(NoLiteral)` for both `Nat`
  models (no sensible lowering); a real model with string/bytes carriers
  supplies them.

## `#sig`/`#thy`/`#model`/`#models` directives (BUILT — increment 1)

The declared surface↔script fusion now exists (`script/theory.rs`,
`models/declared.cov`, `models/nat.sig`, `models/nat.thy`): `(#sig …)` declares
a single-sorted signature, `(#thy …)` a theory (axioms validated abstractly),
`(#model …)` a model (op interpretations typechecked at the carrier), and
`(#models M T …)` certifies `M ⊨ T` (each axiom INSTANTIATED at the carrier is
proved by the supplied `(#by …)`/`(#proof …)`, then M's `NatModel::env()`-shape
dispatch env is registered for `(#in M …)`). `declared.cov` declares `Nat` +
`NatTheory`, declares + certifies `nat/self` and `nat/unary`, and replays the
abstract `add.comm` at both — the Track 1 `NatModel::env()` is now *sourced from
declared data*. Remaining deferrals:

- **Generic, multi-sort / kinded (HOL-ω) signatures.** `Signature` is
  single-sorted (one `(sort α)`) and first-order (op templates are `α`/`->`
  types). The `(family m (-> ty ty))` kind-ty→ty families of `surface-compiler.md`
  §3.0, and multiple sorts, are rejected (`#sig: multi-sort … not supported`).
- **Typed `.sig`/`.thy`/`.mod` file imports.** `(#import x.sig #sig)` /
  `(#import x.thy #thy)` (§3.0/§3.0.1) — the *typed* single-object import that
  checks you got a signature where a signature was expected — is not built; the
  `.sig`/`.thy` bodies are inlined into `declared.cov` (the standalone
  `nat.sig`/`nat.thy` files exist as the deliverable shape but are not yet
  consumed via a typed import).
- **`(from WITNESS)` is transitional.** `(#models nat/unary NatTheory (from
  unary))` pulls the four axioms from a host-supplied env
  (`models::unary::prelude()` — the heavy `unit`-singleton Rust proofs) instead
  of inline `(#by …)`. This keeps `unary.rs` in Rust until its proofs are ported
  to `.cov`; the witnessed theorems ARE re-checked against the instantiated
  goals, so it is sound, just not yet self-contained.
- **`#models` does not register a `.thm` certificate object.** The verified
  axioms accumulate as `M.axname` lemmas + bless the dispatch env, but there is
  no first-class "`M ⊨ T` proof" value (`surface-compiler.md` §3.0.2) carrying
  the logic it was proved in. The next cut reifies the certificate.
- **No model *synthesis* (§3.0.4 north star).** Models are hand-declared via
  `(#model …)`; the tactic that *synthesizes* a model from a theory (subsuming
  `#inductive` as "synthesize the initial model"), and the `#data`/`#codata`
  theory-level declaration forms, are not built. `Model` is a plain value, so it
  stays producible by a future synthesis tactic.

## `#in` block only runs `#thm`

`(#in MODEL STMT…)` (the implemented dispatch form) only accepts nested `#thm`
statements (enough to replay `add_comm`). Nested `#def`/`#have`/`#in`,
`#transport` across models, and the isomorphic-model dispatch
(`surface-compiler.md` §4 — route a fact to the cheapest representative of an
iso class) are unimplemented.

## Only two models, one theory

`Nat` has exactly two models here (`nat/self`, `nat/unary`) and there is no
proved morphism / isomorphism between them (the `nat ≅ list unit` length
iso of `theories-models §2.1/§2.2` — and acceleration-as-iso). Adding more
models (bool-stream coding, a reified-PA model) and the iso registry is the
next increment.
