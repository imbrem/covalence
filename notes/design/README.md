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
   Keep the doc grounded in the code (link crates/files/SKELETONS).
3. When the shape settles, mark it **Accepted** and start the work; record
   deferred pieces as skeletons in the nearest `SKELETONS.md` and link them.
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
| [`relational-base-rewrite.md`](./relational-base-rewrite.md) | Draft (maintainer to flesh out) | Persist proven facts as **signed SQLite**; the base rewrite to relations-as-untrusted-functions that makes the TCB dumpable as data. |

## See also

- [`../vibes/project-map.md`](../vibes/project-map.md) — the map of crate groups
  and active threads (where everything is).
- [`../vibes/what-is-the-tcb.md`](../vibes/what-is-the-tcb.md) — what the trusted
  base actually is, from the golden manifests + audit.
- [`../vibes/k-framework-vision.md`](../vibes/k-framework-vision.md) — the
  K-framework north star (a north-star note, not yet a `design/` proposal).
