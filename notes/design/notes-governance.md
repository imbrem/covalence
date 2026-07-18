# Notes governance and cleanup

- **Status:** Draft
- **Owner:** maintainer
- **Last touched:** 2026-07-18

## Current state

The corpus contains 118 files, about 1.8 MiB and 209,000 words. Several
individual notes exceed 5,000 words; 28 files contain explicit AI/scaffold
language or related provenance markers. The present `plans` / `design` /
`vibes` distinction is useful, but `vibes` mixes research, historical plans,
handoffs, implementation descriptions, speculative designs, and durable
vision. Readers cannot reliably infer currency from location.

## Target taxonomy

Keep the number of top-level classes small and give each a lifecycle:

```text
docs/                 current, verified description of what exists
notes/vision/         durable goals and mathematical direction
notes/decisions/      ADR-like accepted/superseded decisions
notes/design/         active proposals with explicit status and owner
notes/projects/       active workstream briefs and DAGs
notes/lab/            experiments, research logs, benchmark notebooks
notes/inbox/          temporary captures awaiting triage
notes/archive/        superseded historical material, not agent context
```

Tasks do not live in prose registries. Source-local TODO IDs are atomic open
work; project manifests group IDs, benchmarks, dependencies, owners, and
acceptance conditions.

## Document contract

Every non-scratch note begins with compact metadata:

```yaml
status: draft | review | accepted | superseded | parked
owner: name
updated: YYYY-MM-DD
scope: architecture | theory | project | experiment
supersedes: []
related_todos: []
```

The first screen contains:

1. a decision or purpose summary;
2. what is true now;
3. what remains open;
4. links to authoritative code, evidence, and successor documents.

Prefer one claim per paragraph, concrete nouns, stable identifiers, and tables
only for real comparisons. Remove conversational filler, repeated motivation,
fake quotations, agent self-reference, “obviously/simply,” generic conclusions,
and duplicated roadmaps. Long derivations and research evidence belong in
appendices or lab notes; accepted decisions should normally be under roughly
1,500 words.

## Cleanup method

Do not bulk-rewrite the corpus stylistically. That destroys provenance and
creates an unreviewable diff. Process one topic cluster at a time:

1. inventory documents and identify the current authority;
2. extract still-valid claims with code/evidence links;
3. write one concise replacement or promote facts to `docs/`;
4. mark predecessors superseded and link the successor;
5. archive or delete redundant material;
6. update indexes and run link/metadata/length checks.

Start with the active API/kernel cluster, then Lisp/ACL2, then K/SpecTec/WASM.
Historical plans and handoffs are high-value early archive candidates.

## Automation

Add a `bun run notes` tool that builds a note database containing path,
metadata, headings, links, word count, git age, status, owner, related TODOs,
and referenced crates. Initial checks should flag:

- missing or invalid metadata;
- broken relative links;
- duplicate titles;
- active notes not present in an index;
- accepted/current notes with stale code links;
- draft notes over a configurable length;
- superseded notes missing a successor;
- project notes without acceptance conditions or TODO IDs.

The database should feed the Covalence map. It must report quality signals, not
automatically rewrite prose.

## Working habits

- Capture freely into `notes/inbox`; triage it weekly.
- Begin a workstream with a one-page project brief and dogfood script.
- Record decisions when they are made, not as retrospective narrative.
- End each workstream by promoting current facts to `docs` and archiving its
  temporary notes.
- Review note/TODO/dependency deltas alongside code.
- Keep human-authored mathematical statements visibly distinct from
  agent-generated implementation analysis.

