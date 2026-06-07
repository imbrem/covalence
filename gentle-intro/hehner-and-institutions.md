# Hehner and Institution Theory

This note translates the **current code** into two outside vocabularies:

- Hehner `aPToP` language about collections and packaging
- institution theory language about logics, theories, proof artifacts, and
  translations

It is a translation guide. It is not a claim that the repo has been formally
rebuilt in either framework.

## 1. Hehner: collection versus packaging

The Hehner lens starts with a simple distinction:

- a **collection** of assumptions, facts, or rows
- a **packaged artifact** that stores, transports, or names that collection

That distinction clarifies several code choices at once.

### 1.1 In `covalence-pure`

In current Pure code, a theorem is not "just the conclusion". It is a package
that records a dependence:

- `hyps` is the collected assumption set
- `concl` is the classified expression
- `Thm` is the package witnessing that derivability

This is especially visible because `hyps` is a `BTreeSet<Term>`, not an ordered
proof script. The kernel treats the assumption collection as primary.

The observation machinery reinforces the same point:

- an observation leaf is a scoped fact source
- the theorem that uses it remains explicit about that dependency
- the observer object is not itself a global truth

### 1.2 In `covalence-hol`

The current HOL kernel adds another packaging layer:

- types, terms, and theorems are arena objects indexed by handles
- named constants and type constructors are registered in kernel state
- OpenTheory content is later imported into that state

That is packaging in Hehner's sense. The repo does not only state
mathematical claims; it also builds persistent packaged forms for them.

### 1.3 In `covalence-opentheory`

This crate is the clearest packaging example in the current logic-facing code.
It is not primarily a new logic. It is a package and transport discipline for
HOL-family content.

The Hehner lesson for this repo is:

> do not confuse the collection of assumptions/facts with the package that
> stores, imports, hashes, transports, or names them

That rule also matches the broader repository's storage and namespace themes.

## 2. Institution theory: current code map

Institution theory separates four roles:

- the **logic**
- the **theory/context** inside that logic
- the **proof artifact**
- the **translation or transport path**

That vocabulary maps well to the current code.

### 2.1 `covalence-pure`

`covalence-pure` is the framework logic in this part of the tree.

The code does four things:

- it defines the term and type language
- it defines which expressions count as `prop`
- it defines theorem construction rules
- it is intended to host upper-layer object vocabularies

In institution-theory terms, that makes it the meta-level framework here.

### 2.2 `covalence-hol`

`covalence-hol` is the concrete object logic here.

The code does three things:

- it has its own type/term/theorem representation
- it has the HOL Light primitive inference rules
- it supports object-level axioms, definitions, and basic type definitions

The traits in `traits.rs` make this explicit. Types, terms, and theorem rules
are separate, so different HOL backends can implement the same object-logic
API.

### 2.3 `covalence-opentheory`

`covalence-opentheory` is the theory and package transport layer for
HOL-family content.

The code does three things:

- it reads OpenTheory artifacts
- it resolves and interprets them
- it targets a HOL kernel interface

Institutionally it is not another logic beside HOL. It is a transport path
into HOL.

## 3. The key bridge: `hol_light_obs.rs`

If you want one file where the two vocabularies meet most clearly, it is:

- [`crates/covalence-hol/src/hol_light_obs.rs`](../crates/covalence-hol/src/hol_light_obs.rs)

That file shows the bridge between Pure-style and HOL-style views:

- HOL primitives are represented as one observer family
- `HolLightCtx` provides stable identities for those primitives
- `Trueprop` turns a HOL `bool` claim into a Pure `prop`
- observer policies provide a bootstrap account of some HOL reasoning

In institution-theory terms, this is an embedding path from HOL-flavored object
statements into a Pure-style framework language.

In Hehner terms, it is also a packaging move:

- the same mathematical object-language primitives are being repackaged as
  Pure-level terms with explicit observer identities

## 4. Current-code summary

- `covalence-pure` is the framework logic in this part of the tree
- `covalence-hol` is the concrete object logic
- `covalence-opentheory` is the package and import path into that HOL world
- `hol_light_obs.rs` is the bridge between the Pure and HOL representations

This is more accurate than saying either:

- "Pure already is the whole trusted base and HOL already sits cleanly over it"
- or "HOL is the only logic that matters and Pure is merely a side experiment"

Neither extreme matches the code.

## 5. The practical reading rule

Keep these two questions separate:

1. **What does the current code do?**
2. **What architecture do the proposal docs want eventually?**

This `gentle-intro/` folder answers the first question.

The proposal docs under `docs/design/proposals/` answer the second.
