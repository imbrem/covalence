+++
id = "N0044"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:gpt-5.6-sol"
at = "2026-07-19T00:00:00+01:00"
source = "workmux-handoff"
agent = "gpt-5.6-sol"
harness = "codex"
+++

# Verified weighted graph demo: workmux handoff

## Goal

Build a compact vertical slice that accepts bounded DOT or NetworkX text,
interprets exact decimal edge weights, produces graph-algorithm witnesses,
checks those witnesses independently, and presents the result in the existing
interactive graph viewer.

The result should demonstrate several Covalence principles at once:

- graph kinds and representations are abstract APIs;
- text interchange is separate from graph semantics;
- numeric interpretation is explicit and exact;
- algorithms produce untrusted candidates;
- small checkers establish finite evidence;
- theorem-producing HOL replay remains a later, separate capability.

Until HOL replay exists, the UI and documentation must call results
**independently checked finite evidence**, not kernel theorems or verified
proofs.

## Existing foundation

- Graph-kind traits and finite simple graph backends:
  `crates/lib/graph/src/theory.rs`.
- Path and topological-order witness checkers: the same module.
- Bounded DOT plus syntax and semantic round-trip checking:
  `crates/lib/graph/src/interchange.rs`.
- Weighted directed edge lists and directed-multigraph adjacency:
  `crates/lib/graph/src/networkx.rs`.
- Exact canonical decimals: `crates/lang/decimal/src/lib.rs`.
- Static renderers: `crates/lib/graph/src/render.rs`.
- Interactive graph components:
  `packages/covalence-ui/src/lib/graph/`.
- Current product surface: `apps/covalence-web/src/routes/graph/+page.svelte`.

Do not replace the bounded DOT parser in this branch. Keeping it avoids a
dependency on the in-flight parser-combinator work. Full DOT remains
`TODO(cov:graph.dot-full, major)`.

## Required architecture

```text
DOT / NetworkX source
        |
        v
syntax document
        |
        v
FiniteDiGraph<String> + CanonicalDecimal weights
        |
        +----> deterministic BFS / Dijkstra / Kahn candidate generation
        |                     |
        |                     v
        +------------> small independent witness checkers
                              |
                              v
                 presentation DTO + checked status
                              |
                              v
                    interactive graph viewer
```

Keep the generic `FiniteDiGraph` representation distinct from the ordered,
linear-input canonical port graph. Do not force graph-theory objects through
the port-graph model merely to reuse its renderer. Introduce a small
presentation DTO if necessary.

## First milestone

1. Add deterministic BFS path and Kahn topological-order witness producers.
2. Route their outputs through the existing checkers before returning them.
3. Interpret NetworkX weights through `CanonicalDecimal`.
4. Add exact weighted-path checking and a deterministic Dijkstra producer.
5. Normalize bounded DOT and NetworkX import behind one explicit facade.
6. Add a web mode where a user can:
   - paste DOT or NetworkX text;
   - choose source and target vertices;
   - see the accepted path highlighted;
   - inspect the exact total weight;
   - see a checked topological order when the graph is acyclic;
   - view canonical DOT and NetworkX output side by side.

Use a nontrivial dependency DAG as the checked-in demo fixture.

## Acceptance conditions

- Correct BFS, Dijkstra, and topological-order candidates are accepted.
- Forged paths, incorrect path weights, and invalid topological orders are
  rejected by tests.
- Equal imported graphs agree across bounded DOT and NetworkX representations.
- Exact decimal weights never pass through binary floating point.
- The interactive demo highlights the checked witness and explains its trust
  status.
- The graph core does not acquire a dependency on the web application,
  NativeHol, or parser-combinator implementation crates.
- Relevant Rust and Svelte tests pass.
- `bun run todos:check` and `bun run deps:check` pass at handoff.
- Any TCB delta is zero; if it is not, stop and report rather than committing
  the expansion.

## Worktree discipline

- Suggested branch: `verified-weighted-graph-demo`.
- Claim this vertical slice only; avoid full DOT grammar work.
- Commit source-only checkpoints. Regenerate map/TODO/dependency artifacts at
  the integration boundary.
- Stop at the first complete, reviewable demo rather than adding more graph
  algorithms.
- Report commits, tests, benchmark observations, TODO changes, dependency
  changes, TCB changes, and the next recommended slice.

