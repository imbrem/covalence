# Documentation Map

This repository has three different kinds of documentation:

- **Canonical vision**: what Covalence is trying to become.
- **Current-state docs**: what is actually in the tree today.
- **Proposal docs**: candidate directions that are still under debate.

This page is the index for all three so contributors do not have to infer which
documents are normative.

## Start here

| If you need... | Read |
|---|---|
| A quick map of the system and repo | [`c4.md`](./c4.md) |
| A gentle, current-code intro to Pure/HOL | [`../gentle-intro/README.md`](../gentle-intro/README.md) |
| The multi-logic / multi-format zoo in one vocabulary | [`institution-map.md`](./institution-map.md) |
| The short conceptual overview | [`VISION.md`](./VISION.md) |
| The canonical philosophy and invariants | [`../ARCHITECTURE.md`](../ARCHITECTURE.md) |
| The operational rules for implementation work | [`../AGENTS.md`](../AGENTS.md) |
| The honest implementation snapshot | [`where-we-are.md`](./where-we-are.md) |
| The proposal tree and proposal statuses | [`design/README.md`](./design/README.md) |

## Reading order

For most contributors, the shortest useful path is:

1. [`../README.md`](../README.md) for build/run basics.
2. [`c4.md`](./c4.md) for the current architecture map.
3. [`../gentle-intro/README.md`](../gentle-intro/README.md) for a current-code-oriented conceptual intro to Pure/HOL.
4. [`institution-map.md`](./institution-map.md) for the current logic/translation landscape.
5. [`where-we-are.md`](./where-we-are.md) for what is shipping vs in flight.
6. [`VISION.md`](./VISION.md) and [`../ARCHITECTURE.md`](../ARCHITECTURE.md) for the target shape.

If you are changing trusted-core or storage semantics, read
[`../AGENTS.md`](../AGENTS.md) in full before touching code.

## Canonical vs provisional

Use this distinction consistently:

- **Canonical / normative**:
  [`../ARCHITECTURE.md`](../ARCHITECTURE.md),
  [`../AGENTS.md`](../AGENTS.md)
- **Current-state / descriptive**:
  [`c4.md`](./c4.md),
  [`institution-map.md`](./institution-map.md),
  [`where-we-are.md`](./where-we-are.md),
  [`prover-architecture.md`](./prover-architecture.md)
- **Proposal / not yet committed**:
  [`design/README.md`](./design/README.md) and everything under
  [`design/proposals/`](./design/proposals/)
- **Historical / partially superseded**:
  [`refactor-plan.md`](./refactor-plan.md),
  [`prover-mvp-plan.md`](./prover-mvp-plan.md),
  [`../MVP_DESIGN.md`](../MVP_DESIGN.md),
  [`../DESIGN.md`](../DESIGN.md)

## What `c4.md` is for

[`c4.md`](./c4.md) is the consolidation layer this tree was missing:

- It gives a **Level 1 system context** for who uses Covalence.
- It gives a **Level 2 container view** for the runnable surfaces.
- It gives a **Level 3 component view** for how the repo is grouped today.

It is intentionally about the **current repo and runtime surfaces**, not a claim
that every proposal in `docs/design/` has been adopted.
