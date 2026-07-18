# notes/design/ — design docs (index)

Working area for **design docs**: focused, iterable decision records for changes
big enough to want a shared shape before code. This complements the two existing
notes tiers:

- [`../vibes/`](../vibes/README.md) — the broad AI-generated design corpus (vision,
  long-form design records, sketches). Mine for ideas; verify before relying.
- [`../plans/`](../plans/) — maintainer-authored active plans (e.g.
  [`next-stage.md`](../plans/next-stage.md)).
- **`design/` (here)** — one file per proposal, each carrying an explicit
  **Status**, so a reader can see at a glance what is being decided, what is
  accepted, and what is parked. Where `vibes/` is a corpus and `plans/` is the
  roadmap, `design/` is the **queue of open decisions**.

## How we iterate

1. Copy [`TEMPLATE.md`](./TEMPLATE.md) to `notes/design/<slug>.md`, fill in
   *Context / problem*, *Goals / non-goals*, and a first *Proposal*. Mark it
   **Draft** and add a row to the table below.
2. Iterate on **Open questions** turn by turn — that section is the conversation.
   Keep the doc grounded in the code (link crates/files/stable TODO IDs).
3. When the shape settles, mark it **Accepted** and start the work; record
   deferred pieces as source-local `TODO(cov:...)` markers and link their IDs.
4. When it lands, fold durable content into [`../../docs/`](../../docs/README.md)
   (maintainer-authored) or mark the doc **Superseded** and link the successor.
   Don't leave accepted docs to rot.

**Status vocabulary:** `Draft` (being written) · `In review` (shape up for
feedback) · `Accepted` (agreed, work may proceed) · `Superseded` (replaced —
link the successor) · `Parked` (real, but not now).

**Authorship:** this area is agent-draftable scaffolding — agents may create and
iterate design docs here. Graduating a doc's content into `docs/` is a
maintainer step (see the repo authorship policy in
[`../../CLAUDE.md`](../../CLAUDE.md)).

## Active design docs

| Doc | Status | What it decides |
|---|---|---|
| [`api-extraction-audit.md`](./api-extraction-audit.md) | Draft audit | Strengths, risks, and next refinements for the logic, Nat, and inductive APIs. |
| [`content-logic-and-wit-boundaries.md`](./content-logic-and-wit-boundaries.md) | Draft | Minimal blob relation and interpretation boundary; stable logic/theory APIs, numerics, and WIT modules. |
| [`graph-api.md`](./graph-api.md) | Draft | Finite relational graph traits, verified properties, DOT/NetworkX interchange, and legacy port-graph migration. |
| [`human-agent-development-loop.md`](./human-agent-development-loop.md) | Draft | Dogfood-first mathematical briefs, worktree isolation, review packets, and the evolving Covalence map. |
| [`notes-governance.md`](./notes-governance.md) | Draft | Notes taxonomy, lifecycle, concise style rules, incremental cleanup, and future indexing automation. |
| [`relational-base-rewrite.md`](./relational-base-rewrite.md) | Draft (maintainer to flesh out) | Persist proven facts as **signed SQLite**; the base rewrite to relations-as-untrusted-functions that makes the TCB dumpable as data. |

## See also

- [`../vibes/vision/project-map.md`](../vibes/vision/project-map.md) — the map of crate groups
  and active threads (where everything is).
- [`../vibes/kernel/tcb/what-is-the-tcb.md`](../vibes/kernel/tcb/what-is-the-tcb.md) — what the trusted
  base actually is, from the golden manifests + audit.
- [`../vibes/vision/k-framework-vision.md`](../vibes/vision/k-framework-vision.md) — the
  K-framework north star (a north-star note, not yet a `design/` proposal).
