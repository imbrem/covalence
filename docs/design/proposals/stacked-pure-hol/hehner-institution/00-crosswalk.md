# Crosswalk

This page fixes the vocabulary before the layer-by-layer docs.

## The short version

Hehner's `aPToP` lens is useful here because Covalence repeatedly needs to
separate:

- a **collection of things** we can reason from
- a **packaged artifact** with its own identity

Institution theory is useful because Covalence also repeatedly needs to
separate:

- a **logic**
- a **theory inside that logic**
- a **proof artifact**
- a **translation** between any of the above

The repo's proposed Pure/HOL split becomes clearer if you hold both separations
at once.

## Translation Table

| Covalence term | Hehner / `aPToP` reading | Institution-theory reading |
|---|---|---|
| `Term`, `Type` syntax | Expressions built before any proof status is assigned. | Signature and sentence formation data. |
| `SYNTACTIC-WF` | Formation is purely syntactic, never proof-dependent. | `Sen(Σ)` must not depend on theoremhood. |
| Hypothesis set on a theorem | An idempotent commutative **bunch of assumptions**. | The local theory/context relative to which a sentence is derivable. |
| `Thm { hyps, concl }` | A packaged derivation from one bunch to one conclusion. | A proof artifact for entailment in the institution. |
| `define` | Introduce a new packaged name by explicit equation, not by ambient magic. | Conservative signature/theory extension. |
| Observation / oracle fact | A scoped addition to the current bunch of available facts. | A designated theory extension, not a change in the logic itself. |
| HOL `bool` proposition | A truth-valued predicate/specification expression. | An object-level sentence candidate in the HOL institution. |
| `Trueprop` | Repackage a truth-valued object claim so the meta-level can classify it. | Embedding from HOL formulas into Pure propositions. |
| Content-addressed blob / frozen theory | A packaged artifact with identity. | A theory package / transport object, not a sentence by itself. |
| Namespace rows / mount facts | Bunches of rows/facts, later packaged into stores and trees. | Structured theory data and transports, not the core institution. |

## What the bunch lens clarifies

The bunch vocabulary is most useful for the following repo distinctions:

- **Hypotheses are collections, not files.** A theorem depends on a bunch of
  assumptions, not on a directory, package, or serialization format.
- **Rows in a namespace are collections before they are packaged.** The store
  may freeze them into blobs and Merkle roots later, but the logical content is
  still extensional row/fact data first.
- **An observation is not a global truth.** It is an additional scoped fact in
  some authority-owned fragment.

In other words, the bunch lens is primarily about **anti-confusion**:
do not mistake a package, name, blob, or mount point for the underlying fact
collection.

## What the institution lens clarifies

The institution vocabulary is most useful for the following repo distinctions:

- **Pure is not "just syntax".** It is a candidate logic/framework with its own
  signatures, sentences, and derivability relation.
- **HOL is not "the whole prover".** It is one object institution hosted over
  the framework.
- **OpenTheory, Alethe, LRAT, Lean exports, and future SpecTec imports are not
  all the same kind of thing.** Some are package layers, some are proof
  languages, some are translations.

## The main synthesis

The two lenses line up on one recurring rule:

> Keep the **collection of facts**, the **package that stores them**, the
> **logic that states them**, and the **translation that moves them** as four
> different things.

That is already the direction of:

- [`../../../../institution-map.md`](../../../../institution-map.md)
- [`../README.md`](../README.md)
- [`../../../../../ARCHITECTURE.md`](../../../../../ARCHITECTURE.md)

The rest of this subdirectory applies that synthesis first to Pure, then to
HOL.
