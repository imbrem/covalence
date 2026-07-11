# notes/ — the map

Three tiers, split by *trust and authorship* (see
[`plans/next-stage.md`](./plans/next-stage.md) §Notes for the rationale):

- [`vibes/`](./vibes/README.md) — the AI-generated corpus (long-term plans,
  design records, sketches). Cross-referenced but not consistent; mine for
  ideas, verify before relying. Its own README is the index.
- [`plans/`](./plans/) — active plans. **Maintainer-authored.**
  - [`plans/next-stage.md`](./plans/next-stage.md) — the current one (docs
    split, tooling, hierarchical crates, WASM roadmap). An AI-drafted execution
    breakdown lives in [`vibes/next-stage-breakdown.md`](./vibes/next-stage-breakdown.md).
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
