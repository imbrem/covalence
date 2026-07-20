+++
id = "N005G"
status = "draft"
review = "unreviewed"
[[contributions]]
role = "author"
actor = "agent:gpt-5.6-sol"
at = "2026-07-20T00:00:00+01:00"
source = "history-system"
agent = "gpt-5.6-sol"
harness = "codex"
+++

# Historical snapshots

Each child directory records one repository state and is named by an
unambiguous Git commit prefix. Snapshots are immutable: later updates belong in
a new snapshot. Git remains the authority for files at the named commit.

- [`cd384d36/`](./cd384d36/README.md) — 2026-07-20 consolidation point after
  the relational substrate and trusted database algebra design.

A snapshot has an overview, a substrate report, and concise reports for major
projects. Claims link to code, TODO IDs, or design notes and distinguish
implemented, partial, planned, and unverified. The existing index discovers
`notes/**/*.md`; run `bun run notes` after adding a snapshot.

