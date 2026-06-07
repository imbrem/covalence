# Pure Layer

Pure is the bottom layer in the proposed stack, but the important point is not
"bottom" by itself. The important point is that Pure is the first place where
Covalence makes the collection/package and logic/theory separations precise.

## Pure in institution-theory terms

Pure is best read as a candidate **meta-institution**.

At a high level:

- **Signatures** are the available type constructors, term constructors, and
  observation heads with their Pure types.
- **Sentences** are the terms of kind `prop`.
- **Proof artifacts** are `Thm` values.
- **Theories/contexts** are the hypothesis sets carried by those `Thm` values.

This matches the current crate shape directly:

- [`crates/covalence-pure/src/term.rs`](../../../../../crates/covalence-pure/src/term.rs)
  defines the term and type language.
- [`crates/covalence-pure/src/thm.rs`](../../../../../crates/covalence-pure/src/thm.rs)
  defines the LCF rule API and theorem packaging.
- [`crates/covalence-pure/src/lib.rs`](../../../../../crates/covalence-pure/src/lib.rs)
  states the intended role: tiny LF substrate, upper-layer object logics above it.

## Pure in Hehner / `aPToP` terms

Pure is the layer where we refuse to confuse three things:

1. the **expression** being discussed
2. the **bunch of assumptions** available
3. the **packaged derivation artifact** that records the relation between them

That is exactly what `Thm { hyps, concl }` gives us:

- `concl` is the expression being classified
- `hyps` is the bunch it depends on
- the `Thm` object is the package witnessing that dependence

The current implementation uses a `BTreeSet<Term>` for hypotheses, so the bunch
is specifically:

- unordered
- idempotent
- duplicate-insensitive

That is much closer to Hehner's "reason from a collection" stance than to a
proof script as an ordered log.

## Why `SYNTACTIC-WF` matters here

The repo invariant
[`SYNTACTIC-WF`](../../../../../AGENTS.md)
is the key bridge between the two vocabularies.

Pure well-formedness must be purely syntactic because:

- in Hehner's terms, **expression formation must happen before truth
  classification**
- in institution terms, **sentence formation `Sen(Σ)` must not depend on what is
  already provable**

This is why the architecture text is so strict about never consulting
provability while deciding whether a type or term is well-formed.

## The Pure rules as bunch manipulation

The LF rules can be read as controlled transforms on assumption bunches:

- `assume` introduces a one-element bunch.
- `imp_intro` discharges one assumption from the bunch and packages it into the
  conclusion.
- `imp_elim` unions the two supporting bunches.
- `all_intro` and `all_elim` change the sentence while respecting the bunch's
  free-variable discipline.

Pure equality rules do the same thing for transport:

- `refl`, `sym`, `trans` classify equalities
- `cong_app`, `cong_abs`, `beta_conv`, `eta_conv` move classification through
  syntax

Institutionally this is ordinary derivability machinery. In the Hehner lens it
is also a disciplined account of how a bunch of available facts licenses a new
classification.

## Observations in Pure

Observations are where the scoping discipline becomes visible.

Pure's observation leaves and observer policies are not "truth from nowhere".
They are a way to say:

- this fact source is explicit
- this fact is scoped
- this fact enters through a controlled rule, not by ambient privilege

That aligns with both vocabularies:

- Hehner lens: an observation is an extra collected fact, not a magical global
  package
- institution lens: an observation is a theory extension in a designated
  fragment, not a rewrite of the logic itself

This is also why the Pure theorem object exposes whether it contains observation
leaves at all: a theorem with no observations is a universal derivation in the
bare framework, while a theorem with observations advertises its dependency.

## Why Pure is the right starting point

Pure comes first because it gives Covalence one place to host many later
object logics without baking any one of them into the kernel surface.

From the two viewpoints:

- Hehner: keep the general machinery for expressions, classification, and
  assumption bunches separate from any specific packaged theory.
- Institution theory: keep one stable meta-institution, then host object
  institutions over it.

That is the whole reason the proposed split is stronger than "a slightly better
single HOL kernel".
