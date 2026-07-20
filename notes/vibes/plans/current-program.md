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

1. **Specify the relational substrate.** Settle `Set`, `Relation`, witness,
   projection, `MThm`, schema-grounding, and completeness semantics from
   [`N0056`](../../plans/relational-design.md), then build matching in-memory
   and SQLite witnesses.
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
relational API    schema/grounding model
      └──────┬───────┘
             ↓
      dual witness prototype
             ↓
      nucleus transition API
       ├─ blobs/snapshots
       ├─ replay/provenance
       └─ signatures/trust
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
