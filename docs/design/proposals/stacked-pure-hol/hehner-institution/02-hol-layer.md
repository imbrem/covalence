# HOL Layer

If Pure is the framework for making and transporting judgments, HOL is the
first major **object theory** packaged on top of that framework.

## HOL in institution-theory terms

HOL is the default **object institution** hosted over Pure.

The intended reading is:

- Pure provides the meta-level judgment machinery.
- HOL contributes the familiar object-language constants and rules:
  `bool`, `=`, `T`, `F`, implication, conjunction, disjunction, quantifiers,
  and `ε`.
- HOL theorems are represented by Pure theorems whose conclusions are Pure
  propositions built from HOL content.

The crucial bridge is `Trueprop`:

- a HOL formula is a term of type `bool`
- `Trueprop : bool -> prop` repackages that object-level claim as a
  meta-level proposition

Institutionally, `Trueprop` is the visible map from "HOL sentence" into "Pure
sentence that the framework can classify".

## HOL in Hehner / `aPToP` terms

The Hehner lens is useful here because HOL formulas are not yet theorem objects.
They are still expressions whose classification depends on context.

In that lens:

- a HOL boolean term is a **truth-valued specification/predicate expression**
- `Trueprop p` says "treat this packaged truth-valued expression as a claim to
  classify at the meta-level"
- a HOL theorem is therefore still a packaged derivation from an assumption
  bunch, just with a more specific object-language shape

This is the point where the two vocabularies meet cleanly:

- Hehner distinguishes expression from classification.
- Pure distinguishes `bool` terms from `prop` judgments.

## What HOL actually adds

Relative to Pure, HOL adds a first bundled theory of ordinary mathematical
reasoning:

- `bool` as the object-level truth type
- object equality
- logical connectives
- quantifiers
- Hilbert `ε`
- subset typing discipline

The existing code already shows the intended shape even though today's
`covalence-hol` crate is still a standalone HOL-Light-shaped kernel:

- [`crates/covalence-hol/src/hol_light_obs.rs`](../../../../../crates/covalence-hol/src/hol_light_obs.rs)
  shows the current HOL object vocabulary and the explicit `Trueprop` bridge.
- [`crates/covalence-hol/src/traits.rs`](../../../../../crates/covalence-hol/src/traits.rs)
  shows the current HOL-Light-style object-kernel API surface.
- [`../README.md`](../README.md) states the target direction: HOL as the
  default object logic over a Pure substrate.

So there are two readings to keep distinct:

- **today's code reality:** `covalence-hol` is a separate object-kernel
  implementation
- **proposed stack:** the same role is re-expressed as HOL-over-Pure

## The disjunct trick in both vocabularies

The subset-type disjunct trick is one of the clearest points where the
Hehner and institution readings both explain the same architectural choice.

The design goal is:

- type formation must remain syntactic
- inhabitation obligations must not leak into well-formedness

So instead of requiring provable nonemptiness to form a subtype, the design
moves the burden into the sentence layer:

- the type is formed unconditionally
- the representation law carries a disjunct that expresses the missing
  inhabitation case inside the logic

Why this matters:

- Hehner lens: do not let the classification status of one claim decide whether
  another expression may even be formed.
- Institution lens: do not let theoremhood mutate signature or sentence
  formation.

This is one of the load-bearing reasons the architecture insists on the
disjunct trick.

## HOL as the first packaged object theory

Pure is intentionally austere. HOL is the first place where Covalence gets the
object-language conveniences needed for normal mathematics and later semantics
work.

That makes HOL the first major **package** in the Hehner sense:

- not just a raw bunch of expressions
- but a coherent named theory with a familiar vocabulary

At the same time, institution theory prevents overclaiming:

- HOL is a theory family/object institution
- it is not the entire prover
- it is not every future logic
- it is not the same thing as OpenTheory, Lean export, or Alethe

## Why start with HOL

The repo's philosophy repeatedly says the base should be accommodating enough
to host stronger or stranger theories later, but still familiar enough for
daily use. HOL is the first serious realization of that balance.

In this crosswalk's terms:

- Hehner: HOL is the first rich packaged theory over the lower-level
  collection-and-classification machinery.
- Institution theory: HOL is the first default object institution over the
  meta-institution.

That is why "Pure first, HOL second" is not just a layering slogan. It is the
first clean decomposition of the logical core.
