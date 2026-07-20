+++
id = "N0003"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:claude"
at = "2026-06-24T00:26:22+01:00"
source = "legacy"
agent = "claude"
harness = "claude"
+++

# notes/ — the map

Historical, commit-addressed repository reports live in
[`history/`](./history/README.md). They are indexed like every other Markdown
note and are immutable; create a new snapshot for later work.

Directories are organizational hints, not provenance or trust boundaries.
Every Markdown note carries a stable ID, lifecycle/review state, and explicit
contribution metadata. SQLite is the normalized query index for those authored
plaintext facts.

The existing directories remain useful subject groupings:

- [`vibes/`](./vibes/README.md) — a legacy grouping for long-term plans,
  research, audits, and sketches. It no longer implies authorship; migrate or
  rename it gradually rather than through a disruptive bulk move.
- [`plans/`](./plans/) — active plans. **Maintainer-authored.**
  - [`plans/next-stage.md`](./plans/next-stage.md) — the current one (docs
    split, tooling, hierarchical crates, WASM roadmap). An AI-drafted execution
    breakdown lives in [`vibes/plans/current-program.md`](./vibes/plans/current-program.md).
- [`design/`](./design/README.md) — **design docs**: focused, iterable decision
  records (one file per proposal, each with an explicit Status). Agent-draftable
  scaffolding (template + index in its README); graduating content to `docs/` is
  a maintainer step.
- Structured topic notes (`ideas/`, `experiments/`, …) — created as needed.
  *Aspirational*: what we want, may drift from what exists. What actually
  exists belongs in [`../docs/`](../docs/README.md).

Authorship and review claims come only from note metadata. Historical notes are
currently marked `source = "legacy"`, `agent = "claude"`, and
`harness = "claude"` as a corpus-level migration approximation; individual
claims may have mixed provenance and remain unreviewed until audited.

## Querying notes and tasks

`bun run notes` builds a deliberately small knowledge graph in
`target/covalence-notes.sqlite`: every note, task, and TODO is a node; links,
dependencies, membership, and code references are labelled edges.

```sh
bun run notes
bun run notes -- --stale 30
bun run notes -- --task inductive-datatypes
# every definition and use of stable terminology ID T0001
bun run notes -- --term T0001
bun run notes -- --sql "select * from edges where predicate='depends-on'"
bun run notes -- --graph
```

Task manifests in [`projects/`](./projects/) group existing TODOs and relevant
notes/files. Atomic work remains source-local; the manifest adds only project
structure.

## Stable terminology

A terminology note declares `- **Term ID:** T0001`; prose refers to it with
`[[term:T0001]]`. The index creates a `term` node, a `defined-by` edge, and a
`uses-term` edge for every reference. IDs are permanent and deliberately
meaningless: changing a name or moving its definition does not break references.
Undefined and duplicate IDs fail visibly rather than being guessed.

For an interactive browser, run:

```sh
bun run dev:map
```

This regenerates the knowledge-graph snapshot and opens the current `/map`
application. The static shell fetches `/covalence-map.json`; set
`VITE_COVALENCE_MAP_DATA_BASE` to load the same contract from another origin.
The application and shared-package boundary is recorded in
[`vibes/plans/knowledge-browser-apps.md`](./vibes/plans/knowledge-browser-apps.md).
