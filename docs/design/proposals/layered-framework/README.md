# Layered-Framework Proposal

> **STATUS: PROPOSED — working-draft architecture, not committed.**
>
> This is a working-draft design proposal generated during a planning
> conversation. It is **not** a committed architecture; the shape,
> vocabulary, and approach are subject to substantial revision before
> any implementation lands. For the canonical view of what is
> *actually built* vs. what is *proposed*, see
> [`where-we-are.md`](../../../where-we-are.md). For the design
> directory's overall index, see
> [`../../README.md`](../../README.md).

Working-draft design docs for the Covalence redesign. Source of truth for
**what we're trying to build**; the implementation hasn't started yet.

Read together with [`../../../institution-map.md`](../../../institution-map.md):
these docs are easiest to understand if you treat
**Framework / HOL / Morphism** as

- a candidate **meta-institution**,
- a default **object institution**,
- and explicit **institution-translation machinery**

respectively. That is also why this proposal sits naturally beside the
[`stacked-pure-hol`](../stacked-pure-hol/README.md) sketch and the
repo's broader Paulson/Isabelle-Pure homage.

Where these docs *redefine* or *supersede* concepts from
[`ARCHITECTURE.md`](../../../../ARCHITECTURE.md) or
[`AGENTS.md`](../../../../AGENTS.md), the redefinition is called out at the top
of the relevant doc.

## Read in this order

1. **[`../../../where-we-are.md`](../../../where-we-are.md)** — honest snapshot of the
   current codebase: what's shipping, what's in flight, what's stale.
2. **[`00-glossary.md`](./00-glossary.md)** — vocabulary. Definitions of
   LF, HOL, framework, authority, observation, store, meta-trust, etc.
   Cross-referenced throughout.
3. **[`01-conventions.md`](./01-conventions.md)** — naming (256-bit
   opaque names everywhere), the BLAKE3-mode trichotomy, fresh-as-RNG,
   wrapper-crate discipline. Reasons through each convention.
4. **[`02-framework.md`](./02-framework.md)** — the **Framework layer**
   (`covalence-framework`). The actual TCB / [meta-trust
   set](./00-glossary.md#meta-trust-set). LF rules, terms, sequents,
   authorities, observations, stores. ~800 LoC target.

5. **[`03-authority.md`](./03-authority.md)** — Authority + observation in
   depth. The single trust primitive. Safe-axiom class. Meaning-axioms
   in detail.
6. **[`04-store.md`](./04-store.md)** — Stores as scoping for crypto
   assumptions. The global-store framing of `ARCHITECTURE.md` §5.4
   promoted to a framework-primitive.
7. **[`05-trust.md`](./05-trust.md)** — Meta-trust vs trust-set
   distinction; ElidePolicy; exporting facts; what "honest" means for
   a kernel.

## Notes

Focused side-notes that clarify or refine specific points in the main
docs, written as conversations surface them. Not a separate proposal;
companion material.

- **[`notes/facts-not-proofs.md`](./notes/facts-not-proofs.md)** — LCF
  discipline restated: the bottom layer stores facts, not
  justifications. Proof recording is optional. Applies to EProp/EThm:
  the egraph is *storage*, not a decision procedure.

## Planned, not yet written

8. **`06-hol.md`** — Classical HOL as an object theory over the
   Framework. Subset typedef with the disjunct trick, the existentials,
   ε-choice, the primop axiomatization. Institutionally, this is the
   default object logic over the Framework's LF substrate. Builds on the existing
   [`prover-architecture.md`](../../../prover-architecture.md) but rebases it
   onto the framework.
9. **`07-morphism.md`** — Embeddings between theories, equiconsistency,
   base-shift, the commutative-diagram API. This is the place where the
   repo's institution-theoretic vocabulary should become explicit rather
   than merely implied.
10. **`08-oracles.md`** — Oracle conventions, spec format, the BLAKE3
    trichotomy as a recommended *naming* convention (not framework
    primitive). WASM oracle as the canonical example.
11. **`09-federation.md`** — PKI-as-universal-substrate; signed Thm
    exchange; browser ↔ server federation; one-way trust edges.

## Conventions for the docs themselves

- Cross-references use Markdown links: `[term](file.md#anchor)`.
  Anchors are GitHub-flavored auto-generated.
- Inline definitions of vocabulary terms are linked back to
  [`00-glossary.md`](./00-glossary.md) on first occurrence in each
  doc.
- Inference rules are written in display form (numerator / denominator)
  with a rule name in parens to the right of the bar.
- Code examples use Rust pseudocode at the trait/interface level;
  implementation is for the actual codebase.
- "Open questions" sections at the end of each doc list explicit
  decisions to make before implementation.

## Status

| Doc                            | Written | Reviewed | Stable |
|--------------------------------|---------|----------|--------|
| `../../../where-we-are.md`           | ✓       |          |        |
| `README.md` (this file)        | ✓       |          |        |
| `00-glossary.md`               | ✓       |          |        |
| `01-conventions.md`            | ✓       |          |        |
| `02-framework.md`              | ✓       |          |        |
| `03-authority.md`              | ✓       |          |        |
| `04-store.md`                  | ✓       |          |        |
| `05-trust.md`                  | ✓       |          |        |
| `notes/facts-not-proofs.md`    | ✓       |          |        |
| `06-hol.md`                    |         |          |        |
| `07-morphism.md`               |         |          |        |
| `08-oracles.md`                |         |          |        |
| `09-federation.md`             |         |          |        |
