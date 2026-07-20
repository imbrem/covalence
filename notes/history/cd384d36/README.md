+++
id = "N0058"
status = "draft"
review = "unreviewed"
[[contributions]]
role = "author"
actor = "agent:gpt-5.6-sol"
at = "2026-07-20T00:00:00+01:00"
source = "repository-snapshot-cd384d36"
agent = "gpt-5.6-sol"
harness = "codex"
+++

# Repository snapshot: `cd384d36`

| Field | Value |
|---|---|
| Commit | `cd384d36c1f0795d49440191e063086740bfc80a` |
| Time | 2026-07-20 22:56:01 +01:00 |
| Subject | `docs(map): index trusted database algebra` |
| Open work | 386 markers: 55 severe, 171 major, 160 minor |
| TCB audit | base 1,496 source lines; 24 mint sites; zero unsafe |

This is the consolidation point after the Lisp/ACL2, SpecTec, and parser waves
were merged and the SQLite relational substrate became the current rewrite
direction. It reports code and plans; it does not claim a freshly run full test
suite.

## Executive state

- Metamath is the most mature large-corpus proof-import path.
- SAT has checked RUP/LRAT replay; SMT has a useful Farkas core but lacks
  general Alethe replay.
- Lisp has substantial neutral machine/effect/trace APIs; proof-producing HOL
  Lisp remains incomplete.
- ACL2 has book/world analysis, progress accounting, selected green islands,
  and checked APPEND/fixer/ordinal work, but not general admissibility.
- K has KORE and small `.k` frontends, not a checked semantic backend.
- SpecTec/WASM has extensive grammar and HOL lowering, with serious exactness,
  totality, and end-to-end gaps.
- The high-level data, inductive, parsing, JSON, graph, computation, and
  automata APIs are experimental consumers for the substrate rewrite.

## Reports

- [Substrate](./substrate.md)
- [Metamath](./metamath.md)
- [Lisp](./lisp.md)
- [ACL2](./acl2.md)
- [K](./k.md)
- [WASM and SpecTec](./wasm.md)
- [SMT and SAT](./smt-sat.md)

## Current plan

1. Specify `Set`, `Relation`, witness, projection, `MThm`, grounding, and
   completeness.
2. Implement `App` and `HasTy` with in-memory and SQLite witnesses.
3. Define and cross-check the tiny trusted query/multi-database algebra.
4. Define atomic proton/neutron transitions.
5. Add canonical snapshots, replay, signer policies, and filtered subDBs.
6. Exercise WASM instance lifecycle relations.
7. Differentially migrate audited vertical slices.

Live plan: [`N0055`](../../vibes/plans/current-program.md). Rewrite detail:
[`N0054`](../../vibes/kernel/substrate-rewrite.md).

## Validation

At snapshot creation, `bun run todos:check` and `bun run deps:check` passed.
No full Rust/Python test suite was run for this documentation snapshot.

