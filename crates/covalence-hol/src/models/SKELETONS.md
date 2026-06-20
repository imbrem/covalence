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

## `#model` directive (not built)

The surface `(#model NAME : THEORY #in LOGIC (#carrier …) (#map …))` form
(`surface-compiler.md` §3) that *declares* a model inside a `.cov` is not
implemented — models are built in Rust (`NatSelf`/`NatUnary`) and entered via a
resolver-backed `#import` + `#in`. A `#model` directive needs the surface
elaborator to turn a `(#map …)` into a `NatModel` (and to discharge the
axiom-satisfaction obligation), which depends on the not-yet-built theory
header (`#theory`/`#spec`).

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
