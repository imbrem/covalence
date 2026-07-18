# notes/ — the map

Three tiers, split by *trust and authorship* (see
[`plans/next-stage.md`](./plans/next-stage.md) §Notes for the rationale):

- [`vibes/`](./vibes/README.md) — the AI-generated corpus (long-term plans,
  design records, sketches). Cross-referenced but not consistent; mine for
  ideas, verify before relying. Its own README is the index.
- [`plans/`](./plans/) — active plans. **Maintainer-authored.**
  - [`plans/next-stage.md`](./plans/next-stage.md) — the current one (docs
    split, tooling, hierarchical crates, WASM roadmap). An AI-drafted execution
    breakdown lives in [`vibes/plans/next-stage-breakdown.md`](./vibes/plans/next-stage-breakdown.md).
- [`design/`](./design/README.md) — **design docs**: focused, iterable decision
  records (one file per proposal, each with an explicit Status). Agent-draftable
  scaffolding (template + index in its README); graduating content to `docs/` is
  a maintainer step.
- Structured topic notes (`ideas/`, `experiments/`, …) — created as needed.
  *Aspirational*: what we want, may drift from what exists. What actually
  exists belongs in [`../docs/`](../docs/README.md).

**Authorship (current policy):** everything outside `vibes/` is
maintainer-authored (not fully AI-generated) until the vision is fully written
out by hand. Agents: contribute to `vibes/`; don't author the other tiers.

## Querying notes and tasks

`bun run notes` builds a deliberately small knowledge graph in
`target/covalence-notes.sqlite`: every note, task, and TODO is a node; links,
dependencies, membership, and code references are labelled edges.

```sh
bun run notes
bun run notes -- --stale 30
bun run notes -- --task inductive-datatypes
bun run notes -- --sql "select * from edges where predicate='depends-on'"
bun run notes -- --graph
```

Task manifests in [`projects/`](./projects/) group existing TODOs and relevant
notes/files. Atomic work remains source-local; the manifest adds only project
structure.

For an interactive browser, run:

```sh
bun run dev:map
```

This regenerates the knowledge-graph snapshot and opens the current `/map`
application. The static shell fetches `/covalence-map.json`; set
`VITE_COVALENCE_MAP_DATA_BASE` to load the same contract from another origin.
The application and shared-package boundary is recorded in
[`vibes/plans/knowledge-browser-apps.md`](./vibes/plans/knowledge-browser-apps.md).
