# Documentation Map

This directory now has three clearly different jobs:

- describe the code that exists today,
- describe the target architecture and invariants,
- keep proposals and historical material without pretending they are current.

Use this page to avoid mixing those layers up.

## Start Here

| If you need... | Read |
|---|---|
| Build and run basics | [`../README.md`](../README.md) |
| The current implementation snapshot | [`where-we-are.md`](./where-we-are.md) |
| The current runtime / repo structure | [`c4.md`](./c4.md) |
| The logic / proof-format / translation landscape | [`institution-map.md`](./institution-map.md) |
| The target philosophy and invariants | [`../ARCHITECTURE.md`](../ARCHITECTURE.md) |
| Trusted-core implementation rules | [`../AGENTS.md`](../AGENTS.md) |
| Design proposals and historical planning docs | [`design/README.md`](./design/README.md) |

## Reading Order

For most contributors:

1. [`../README.md`](../README.md)
2. [`where-we-are.md`](./where-we-are.md)
3. [`c4.md`](./c4.md)
4. [`institution-map.md`](./institution-map.md) if your work touches proofs,
   importers, or logic translation
5. [`../ARCHITECTURE.md`](../ARCHITECTURE.md) and [`../AGENTS.md`](../AGENTS.md)
   if your work touches the trusted core or long-term architecture

## Status Labels

Use these labels consistently when updating docs:

- `Current implementation`: intended to match the checked-in code
- `Target architecture`: the direction the repo is trying to move toward
- `Proposal`: a candidate design, not an adopted fact
- `Historical`: useful context, but not a statement about the current tree

## Current Implementation Docs

- [`where-we-are.md`](./where-we-are.md) — code-first snapshot of the workspace
- [`c4.md`](./c4.md) — surfaces, runtime containers, and component groupings
- [`institution-map.md`](./institution-map.md) — logic/integration map
- [`prover-architecture.md`](./prover-architecture.md) — legacy
  `covalence-kernel` implementation notes
- [`prover-primops.md`](./prover-primops.md) and
  [`prover-sexpr.md`](./prover-sexpr.md) — legacy kernel internals and syntax

## Target Architecture Docs

- [`../ARCHITECTURE.md`](../ARCHITECTURE.md)
- [`../AGENTS.md`](../AGENTS.md)
- [`VISION.md`](./VISION.md)

These explain where the project is trying to go. They are not a literal map of
today's runtime surfaces.

## Proposals And History

- [`design/README.md`](./design/README.md) — proposal index
- [`refactor-plan.md`](./refactor-plan.md) — historical kernel refactor plan
- [`prover-mvp-plan.md`](./prover-mvp-plan.md) — historical restart sketch
- [`../MVP_DESIGN.md`](../MVP_DESIGN.md), [`../DESIGN.md`](../DESIGN.md) —
  older design snapshots

## One Important Rule

If a document claims to describe the current codebase, verify it against files
under `crates/`, `apps/`, `packages/`, and `extensions/`. If it claims to
describe the architecture we want, link it to `ARCHITECTURE.md` or the relevant
proposal and label it accordingly.
