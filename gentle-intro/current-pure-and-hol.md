# Current Pure and HOL

This note is the shortest accurate description of the current Pure and HOL code
without jumping ahead to the proposal docs.

## The short picture

Today the tree contains two different logic cores that matter for this topic:

1. [`covalence-pure`](../crates/covalence-pure/src/lib.rs) is a small
   Pure-style logical framework.
2. [`covalence-hol`](../crates/covalence-hol/src/lib.rs) is a separate
   HOL-Light-shaped kernel.

They are related, but they are not yet "one finished stacked system".

`covalence-opentheory` is also important because it is the current transport
layer that feeds HOL-family material into `covalence-hol`.

## What `covalence-pure` currently is

The current `covalence-pure` crate says its role plainly in
[`crates/covalence-pure/src/lib.rs`](../crates/covalence-pure/src/lib.rs):

- it is Isabelle/Pure-shaped
- it is small
- it owns term/type representation, substitution, and theorem rules
- it deliberately does **not** own the HOL vocabulary

At the current-code level, the most important parts are:

- [`term.rs`](../crates/covalence-pure/src/term.rs):
  locally nameless terms and types, with meta-level implication, universal
  quantification, equality, blobs, and observation leaves
- [`thm.rs`](../crates/covalence-pure/src/thm.rs):
  the opaque `Thm` type and the LCF-style rule API
- [`subst.rs`](../crates/covalence-pure/src/subst.rs):
  capture-avoiding substitution, opening/closing, and type substitution

### What Pure's theorem object means

The theorem object is:

```rust
pub struct Thm {
    hyps: Arc<BTreeSet<Term>>,
    concl: Term,
}
```

That matters for three reasons:

- hypotheses are stored as a **set**, not a script or list of steps
- every theorem is checked to ensure the conclusion and hypotheses are all
  `prop`-typed
- construction is restricted to the rule API, so this is LCF-style
  constructional soundness

### What Pure currently has

Pure currently exposes meta-level rules such as:

- `assume`
- `imp_intro` / `imp_elim`
- `all_intro` / `all_elim`
- `refl`, `trans`, `sym`
- `cong_app`, `cong_abs`
- `beta_conv`, `eta_conv`
- `inst_tfree`

It also has observation-facing machinery in the term language and theorem API,
including:

- typed erased observer leaves
- pointer-identity comparison for observer objects
- observer-specific policies like `ObsEq`, `ObsTrue`, and `ObsImp`

What it does **not** currently include is just as important:

- no built-in HOL `bool` vocabulary inside the crate interface
- no `define` rule in the current crate state
- no local-authority `observe` rule in the current crate state
- no content-addressing or store integration inside the kernel rules

So the current Pure code is best read as a small framework kernel with some
bootstrap observation machinery, not yet as the whole future trusted center
described by the proposals.

## What `covalence-hol` currently is

The current `covalence-hol` crate is not just "the HOL layer over Pure".
It has its own separate arena-based kernel.

The current public surface in
[`crates/covalence-hol/src/lib.rs`](../crates/covalence-hol/src/lib.rs)
exports:

- `HolKernel`
- `HolArena`
- `HolLightKernel`, `HolLightTerms`, `HolLightTypes`
- `HolLight`, `HolLightCtx`, and typed hint helpers

### The arena kernel side

[`crates/covalence-hol/src/light.rs`](../crates/covalence-hol/src/light.rs)
implements a classic arena/index-handle kernel:

- `HolKernel` stores arenas for types, terms, and theorems
- it registers the built-in type constructors `fun` and `bool`
- it registers polymorphic equality
- it implements the 10 HOL Light primitive inference rules
- it also supports axioms, basic definitions, and basic type definitions

The traits in
[`crates/covalence-hol/src/traits.rs`](../crates/covalence-hol/src/traits.rs)
make this shape explicit:

- one trait for types
- one for terms
- one for theorem proving

That means `covalence-hol` is already written as an object-kernel interface with
multiple possible backends, not just one hardcoded implementation.

### The Pure-facing bootstrap side

At the same time, `covalence-hol` also contains
[`hol_light_obs.rs`](../crates/covalence-hol/src/hol_light_obs.rs), which is
important because it shows how HOL vocabulary can be represented in current
`covalence-pure` terms:

- `HolLight` enumerates HOL primitives like `bool`, `=`, `T`, `F`, connectives,
  quantifiers, `ε`, and `Trueprop`
- `HolLightCtx` gives shared identities for those primitives
- `Trueprop : bool -> prop` is the bridge from HOL truth values into Pure
  propositions
- observer policies encode a bootstrap account of some HOL reasoning over Pure

This file is the clearest current code showing how the repo is trying to relate
Pure-style framework reasoning to HOL-style object reasoning.

## What `covalence-opentheory` currently is

`covalence-opentheory` is not another logic in the same sense as the two crates
above.

Its current role is:

- read OpenTheory material
- resolve dependencies
- interpret that material against a HOL-style kernel interface
- currently drive `covalence-hol`

So for a new reader, the right present-tense picture is:

- `covalence-pure` is a framework-like logic kernel
- `covalence-hol` is a separate HOL object-kernel
- `covalence-opentheory` is a transport/import client of the HOL side

## The most important "do not blur this" point

The current repo also contains proposal docs that describe a future cleaner
stack. Those are useful, but they are not the same thing as the current code.

If you want to stay honest about the current tree, the right statement is:

> The repo already contains a Pure-style framework crate and a separate HOL
> kernel crate, plus a HOL import layer, but the final architecture that unifies
> or reorganizes them is still under active design.
