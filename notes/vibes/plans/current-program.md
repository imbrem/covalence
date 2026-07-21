+++
id = "N0055"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:gpt-5.6-sol"
at = "2026-07-20T00:00:00+01:00"
source = "vision-consolidation"
agent = "gpt-5.6-sol"
harness = "codex"
+++

# Current program

This is the short portfolio entry point. Stable TODO markers describe concrete
open work; specialized notes explain local designs. Historical plans removed
from this directory remain available in Git.

## Priority order

1. **Specify the relational substrate.** Start from maintainer designs
   [`N0056`](../../plans/relational-design.md) and
   [`N005H`](../../plans/covalence_substrate_design.md). Settle the partial
   SQLite model, context-indexed expressions and decoding from
   [`N005I`](../kernel/substrate-expressions.md), table quantifiers,
   `Set`/`Relation`/`MThm`, and `DEF`/`USE` mutation semantics. Then build
   matching in-memory and SQLite witnesses. Specify the query/multi-DB algebra in
   [`N0057`](../kernel/trusted-database-algebra.md) before general replay.
2. **Stabilize consumer APIs.** Logic/relations, data/numerics, inductives,
   parsing, Lisp, graphs, and JSON must have capability-sized interfaces and
   backend-neutral conformance tests.
3. **Polish proof pipelines.** Metamath is the scale baseline; SMT/SAT stress
   propositions and bitvectors; ACL2/Lisp and SpecTec/WASM stress execution and
   semantics.
4. **Run old and new substrates together.** Migrate one vertical slice at a
   time and compare statements, assumptions, trust reports, and performance.
5. **Audit-copy into the clean architecture.** Once APIs and the substrate are
   stable, move only reviewed modules onto the fresh main line.

## Dependency graph

```text
                       ┌─ Metamath scale
high-level APIs ───────┼─ SMT/SAT + bitvectors
      │                ├─ Lisp/ACL2
      │                └─ SpecTec/K/WASM
      ↓                         │
compatibility suites            │
      │                         │
      ├──────────────┬──────────┘
      ↓              ↓
table logic       SQLite/schema/Expr model
      └──────┬───────┘
             ↓
      DEF/USE + dual witness prototype
             ↓
      trusted query + multi-DB algebra
             ↓
      nucleus transition API
       ├─ blobs/snapshots
       ├─ replay/provenance
       └─ signatures/trust
             ↓
       distributed subDB exchange
             ↓
       dual-backend vertical slice
             ↓
       audit and replacement
```

## Documentation hierarchy

- [`N0053`](../vision/neel-meeting-synthesis.md): current product and research
  vision.
- [`N0054`](../kernel/substrate-rewrite.md): substrate rewrite invariants and
  work packages.
- This note: current sequencing.
- Topic notes: reusable local designs and audited subsystem state.
- Handoffs: temporary branch state; delete after incorporation.
- Stable TODO database: acceptance-oriented implementation work.

Any plan that repeats this portfolio should be deleted or reduced to a link.
Project status belongs in queryable tasks/TODOs rather than narrative snapshots.
