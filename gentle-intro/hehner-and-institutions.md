# Hehner and Institution Theory

This note translates the **current code** into two outside vocabularies:

- Hehner `aPToP` language about collections and packaging
- institution theory language about logics, theories, proof artifacts, and
  translations

It is a reading aid, not a claim that the repo has been formally rebuilt in
either framework.

## 1. Hehner: collection versus packaging

The most useful part of the Hehner lens here is a simple distinction:

- a **collection** of assumptions, facts, or rows
- a **packaged artifact** that stores, transports, or names that collection

That distinction clarifies several current code choices immediately.

### 1.1 In `covalence-pure`

In current Pure code, a theorem is not "just the conclusion". It is a package
that records a dependence:

- `hyps` is the collected assumption set
- `concl` is the classified expression
- `Thm` is the package witnessing that derivability

This is especially visible because `hyps` is a `BTreeSet<Term>`, not an ordered
proof script. The current kernel is telling you that what matters first is the
assumption collection, not a narrative trace.

The observation machinery reinforces the same point:

- an observation leaf is a scoped fact source
- the theorem that uses it remains explicit about that dependency
- the observer object is not itself a global truth

### 1.2 In `covalence-hol`

The current HOL kernel adds another packaging layer:

- types, terms, and theorems are arena objects indexed by handles
- named constants and type constructors are registered in kernel state
- OpenTheory content is later imported into that state

That is all packaging in Hehner's sense: the repo is not only talking about
mathematical claims, it is building persistent packaged forms for them.

### 1.3 In `covalence-opentheory`

This crate is the clearest packaging example in the current logic-facing code.
It is not primarily a new logic. It is a package and transport discipline for
HOL-family content.

So the Hehner lesson for the current repo is:

> do not confuse the collection of assumptions/facts with the package that
> stores, imports, hashes, transports, or names them

That rule also matches the broader repository's storage and namespace themes.

## 2. Institution theory: current code map

Institution theory asks you to separate at least four roles:

- the **logic**
- the **theory/context** inside that logic
- the **proof artifact**
- the **translation or transport path**

That vocabulary maps well to the current code.

### 2.1 `covalence-pure`

Current best reading: a candidate **meta-institution / logical framework**.

Why:

- it defines the term and type language
- it defines which expressions count as `prop`
- it defines theorem construction rules
- it is intended to host upper-layer object vocabularies

Current-code caution:

- this does not mean it is already the single settled base institution for the
  whole repo
- it means the crate is written in a way that naturally invites that reading

### 2.2 `covalence-hol`

Current best reading: a concrete **object institution** with a separate kernel.

Why:

- it has its own type/term/theorem representation
- it has the HOL Light primitive inference rules
- it supports object-level axioms, definitions, and basic type definitions

The traits in `traits.rs` make the institution-like surface explicit: types,
terms, and theorem rules are separated, so different HOL backends can implement
the same object-logic API.

### 2.3 `covalence-opentheory`

Current best reading: a **theory/package transport layer** for HOL-family
content.

Why:

- it reads OpenTheory artifacts
- it resolves and interprets them
- it targets a HOL kernel interface

So institutionally it is not best understood as "another logic beside HOL".
It is a transport path into HOL.

## 3. The especially interesting current-code bridge: `hol_light_obs.rs`

If you want one file where the two vocabularies meet most clearly, it is:

- [`crates/covalence-hol/src/hol_light_obs.rs`](../crates/covalence-hol/src/hol_light_obs.rs)

That file shows how current code is already experimenting with a bridge between
Pure-style and HOL-style views:

- HOL primitives are represented as one observer family
- `HolLightCtx` provides stable identities for those primitives
- `Trueprop` turns a HOL `bool` claim into a Pure `prop`
- observer policies provide a bootstrap account of some HOL reasoning

Institution-theoretically, this looks like an attempted embedding path from
HOL-flavored object statements into a Pure-style framework language.

In Hehner terms, it is also a packaging move:

- the same mathematical object-language primitives are being repackaged as
  Pure-level terms with explicit observer identities

## 4. The honest current-code summary

The most honest summary is slightly untidy, because the repo is mid-transition.

Today:

- `covalence-pure` is best read as a framework-like candidate
  meta-institution
- `covalence-hol` is best read as the clearest current concrete object
  institution
- `covalence-opentheory` is best read as package/import transport into that HOL
  world
- `hol_light_obs.rs` is the clearest current experiment tying the Pure and HOL
  worlds together

That is more accurate than saying either:

- "Pure already is the whole trusted base and HOL already sits cleanly over it"
- or "HOL is the only logic that matters and Pure is merely a side experiment"

Neither extreme matches the current code.

## 5. The practical reading rule

When reading the repo right now, keep these two questions separate:

1. **What does the current code do?**
2. **What architecture do the proposal docs want eventually?**

This `gentle-intro/` folder answers the first question.

The proposal docs under `docs/design/proposals/` answer the second.
