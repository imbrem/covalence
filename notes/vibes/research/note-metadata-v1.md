+++
id = "N0002"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:gpt-5.6-sol"
at = "2026-07-18T23:57:36+01:00"
source = "codex-development-wave"
agent = "gpt-5.6-sol"
harness = "codex"
+++

# Note metadata v1

This is the first bounded plaintext provenance convention for Covalence notes.
It is deliberately smaller than the eventual document and theorem knowledge
model. All current notes now carry this header; missing metadata, duplicate
addresses, or malformed contribution provenance are indexing errors.

## Header

An annotated Markdown note begins with TOML between `+++` delimiters:

```toml
+++
id = "N0042"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "human:tekne"
at = "2026-07-18T11:30:00+01:00"
source = "human-authored"
agent = "none"
harness = "editor"

[[contributions]]
role = "research"
actor = "agent:forester-provenance-research"
at = "2026-07-18T12:00:00+01:00"
source = "codex-development-wave"
agent = "gpt-5.6-sol"
harness = "codex"

[[sources]]
id = "S0042"
kind = "documentation"
target = "https://example.test/reference"
version = "1.0"
accessed = "2026-07-18"
locator = "section 2"
purpose = "API behavior"
+++
```

`id`, `status`, and `review` are required. Note and source IDs are stable and
opaque. Actor IDs start with `human:` or `agent:`. Contributions are ordered
and require `role`, `actor`, `at`, `source`, `agent`, and `harness`. `source`
records the provenance class; `agent` records the model or author class; and
`harness` records the tool through which the contribution was produced. These
are authored facts, unlike the Git-derived revision fields.

The initial lifecycle statuses are `draft`, `in-review`, `accepted`,
`superseded`, and `parked`. Review is a separate dimension:
`unreviewed`, `checked`, `accepted`, or `superseded`.

A source requires `id`, `kind`, and `target`; `version`, `accessed`, `locator`,
and `purpose` are optional. Reusing a source ID with conflicting attributes is
an indexing error.

An optional checked review is represented separately from the note's summary
review state:

```toml
[[reviews]]
actor = "human:tekne"
verdict = "checked"
at = "2026-07-19T09:00:00+01:00"
comment = "Checked claims against the linked release."
```

## Derived data

Run `bun run notes` after changing note metadata. Authored plaintext is
authoritative. The command parses it into normalized tables in
`target/covalence-notes.sqlite`, then produces both JSON map copies from
ordered SQLite queries. JSON and SQLite are regenerated artifacts, not editing
surfaces.

The `revisions` table derives the latest committed hash and timestamp for each
note from Git. A note must not contain the hash of the commit that contains the
note, because that reference would be self-referential.

Useful queries are:

```sh
bun run notes -- --note N0042
bun run notes -- --actor agent:forester-provenance-research
bun run notes -- --sql "select * from citations where note_id = 'note:notes/path.md'"
```

The normalized tables are `note_metadata`, `actors`, `contributions`,
`sources`, `citations`, `reviews`, and `revisions`. The generic `nodes` and
`edges` graph also exposes actors, sources, `contributed-by`, `reviewed-by`,
and `cites`, while keeping provenance details in the companion tables.
