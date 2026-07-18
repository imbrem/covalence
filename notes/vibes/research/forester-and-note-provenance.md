# Forester compatibility and note provenance

- **Status:** draft
- **Authorship:** agent `/root/forester_provenance_research`
- **Authored at:** 2026-07-18T23:50:59+01:00
- **Review:** unreviewed
- **Sources:** Forester 5.0 source and package metadata; Jonathan Sterling's
  public forest; OCaml/opam documentation

This is an agent-authored technical recommendation, not repository
documentation. The source audit used Forester 5.0 and the current upstream
`main` branch on 2026-07-18.

## Recommendation

Treat Forester as an optional authoring-tool integration and as a compatibility
target, not as Covalence's knowledge model.

Concretely:

1. Add OCaml/opam to the reproducible development environment as an optional
   tool group. Pin Forester 5.0 when enabling the group, but do not put Forester
   on the default build path.
2. Run a small, reversible pilot: export a read-only Covalence forest from the
   note database and import a deliberately small Forester source subset. Test
   this on a handful of definitions, design notes, and code references.
3. Preserve Forester-style stable addresses and graph semantics where useful,
   but keep Covalence's canonical relation vocabulary and provenance model
   independent of Forester.
4. Make the data path unequivocal:

   ```text
   authored plaintext
          |
          v
   parsed facts + diagnostics
          |
          v
   regenerated SQLite query database
          |
          +--> versioned JSON interchange
          +--> covalence-map pages
          +--> Forester export
          +--> embeddings and other derived indexes
   ```

   JSON must be exported by querying SQLite, rather than being independently
   assembled from plaintext. That gives every consumer the same semantics while
   leaving Git-tracked plaintext authoritative.

This keeps Forester immediately useful and makes the OCaml investment pay
twice—Forester now, SpecTec tooling later—without committing the long-term
Covalence document model to another program's internal AST or release cycle.

## What Forester provides

Forester describes itself as a compiled markup language for scientific
hypertext. Its implementation is usefully layered into core syntax/types,
parser, compiler, frontends, search, server, and LSP libraries. A forest is
configured by `forest.toml`, which names tree directories, asset directories,
foreign forests, a base URL, and a home tree. The compiler recursively finds
`.tree` files and produces a themed, essentially static site.

A tree's address is its filename without `.tree`; its physical subdirectory is
irrelevant, and duplicate addresses are rejected. Named addresses become URIs
relative to the forest's base URL. Forester can allocate either sequential or
random addresses, optionally with a namespace prefix; current allocation uses a
base-36 suffix. This is a good precedent for Covalence: an address should be
stable and meaningless, while titles and taxonomy remain editable metadata.

The source language is substantially richer than a Markdown dialect. It has
TeX-like commands and groups, lexical scopes, definitions, functions, objects
and patches, public/private imports, transclusion, links, nested subtrees,
namespaced XML elements, and embedded Datalog propositions and queries.
Frontmatter supports a URI, title, dates, authors/contributors, taxon, display
number, designated parent, source path, tags, arbitrary metadata, and a
last-changed time.

During analysis Forester records graph facts such as links, transclusions,
authorship, tags, and taxa. Built-in Datalog rules derive transitive
transclusion, references, backlinks/context, and direct or indirect
contributions. This is closer to Covalence's desired note/task/theorem graph
than a folder taxonomy is.

Forester 5 also has:

- themed static HTML generation;
- a JSON manifest query (`forester query all`), with source paths in development
  mode;
- foreign-forest ingestion;
- an LSP with navigation, symbols, completion, diagnostics, and tree creation;
- an optional Eio HTTP server and search support.

The JSON manifest is a useful integration seam but is not a complete,
documented interchange format: it contains discovery metadata, not the full
source or semantic graph. The compiler's internal represented JSON and emitted
HTML/XML should therefore not become Covalence's stable API.

## Cost of adopting it

The official Forester 5.0 package requires OCaml 5.3, Dune 3.13, Menhir, and a
fairly broad OCaml dependency closure. It includes OCamlGraph, Eio,
Datalog, Yojson, TOML, LSP/JSON-RPC, Unicode, HTML, URI, and diagnostic
libraries. The upstream package is GPL-3.0-or-later.

That is reasonable for an opt-in developer tool under Nix/opam, but too large
and too fast-moving to make a prerequisite of `bun run notes`, the Rust build,
or the semi-static map viewer. Invoking the released executable as a tool also
creates a cleaner integration boundary than linking its OCaml libraries into
the primary build. Any later redistribution, vendoring, or code reuse needs a
specific license review; format compatibility based on an independently
specified subset is the lower-coupling path.

The current project already has Nix, so the least disruptive experiment is a
separate output or shell feature such as `.#forester`, with an opam lock/pin
owned by that optional environment. The default shell should merely explain how
to enable it. SpecTec should share the OCaml toolchain layer, not acquire a
dependency on Forester itself.

## Three integration choices

### Adopt Forester as the canonical authoring system

This gives the best editor and language immediately: transclusion, Datalog,
foreign forests, stable addresses, LSP, and mature site generation.

It also gives the least control over theorem/program nodes, source spans into
Rust and Covalence modules, provenance, server-fed JSON, and SQLite query
semantics. Migrating all existing Markdown before those requirements stabilize
would be expensive and would make a GPL OCaml tool operationally central.
Do not choose this yet.

### Keep Forester as an optional tool

This is the recommended first step. Import selected `.tree` constructs into the
same normalized facts as Markdown, and export database facts as a generated
forest. Developers who install Forester get its LSP and renderer; everyone else
keeps the Bun-only notes pipeline. Round-trip fidelity is not required at first:
each file declares its authoring format, and generated exports are not edited.

### Implement a Forester-compatible Covalence subset

This is the likely long-term direction, but “compatible” must be stated in
levels:

1. **Address compatibility:** preserve tree IDs, URI resolution, and links.
2. **Graph compatibility:** preserve links, transclusions, hierarchy,
   authorship, tags, taxa, and source locations.
3. **Source compatibility:** parse a published subset of `.tree` syntax.
4. **Presentation compatibility:** emit routes and metadata that themes or
   external forests can consume.

Full language compatibility includes Forester's macro/object/scope semantics and
embedded Datalog, and should not be promised casually. A bounded subset should
reject unsupported constructs with source-located diagnostics rather than
silently approximating them. Golden tests can run both compilers against a
small corpus and compare normalized graph facts rather than generated HTML.

## Proposed plaintext provenance

Replace directory-implied authorship with explicit, compositional metadata.
Authorship is not a boolean: a human may originate a note, an agent may expand
it, and another human may verify it. Content lifecycle and review are separate
dimensions.

For Markdown, a minimal TOML frontmatter could be:

```toml
+++
id = "N0042"
status = "draft"                 # content lifecycle
review = "unreviewed"            # provenance/accuracy review

[[contributions]]
role = "author"
actor = "human:tekne"
at = "2026-07-18T11:30:00+01:00"

[[contributions]]
role = "research"
actor = "agent:forester-provenance-research"
at = "2026-07-18T12:00:00+01:00"

[[sources]]
kind = "url"
target = "https://opam.ocaml.org/packages/forester/"
accessed = "2026-07-18"
+++
```

Use stable opaque IDs for notes, terms, actors, and sources; human-readable
names are attributes. Suggested normalized relations are:

```text
note(id, title, status, review, path)
actor(id, kind, display_name)
contribution(note_id, actor_id, role, authored_at, ordinal)
source(id, kind, target, version, accessed_at)
cites(note_id, source_id, locator, purpose)
review(note_id, actor_id, verdict, reviewed_at, comment)
revision(note_id, commit, committed_at, blob_hash)
```

`commit` should normally be derived from Git, not typed into frontmatter: a file
cannot contain the hash of the commit that contains that hash. The indexer can
join each contribution to the first commit containing it and each current note
to its latest commit. An optional external agent-run ID can identify a session;
the Git commit then identifies the auditable artifact. Timestamps in plaintext
record when an act occurred; Git supplies independently queryable commit time.

Use a small review vocabulary initially:

- `unreviewed`: no human accuracy review;
- `checked`: a named reviewer checked sources and claims;
- `accepted`: suitable as current project guidance;
- `superseded`: retained for incoming links but not current guidance.

Do not infer these states from prose such as “maintainer to review.” Legacy
notes without valid metadata should be indexed as `unparsed legacy`, exactly as
the map now does, and migrated opportunistically. Once explicit metadata is
accepted, `notes/vibes/` can disappear without losing the distinction between
human and agent work.

### Migration without bulk churn

The migration need not move or rewrite the corpus:

1. Teach the parser the new frontmatter while preserving its current legacy
   heuristics. Missing frontmatter is valid and produces explicit
   `unparsed legacy` provenance.
2. Add metadata only when a note is otherwise touched or actively reviewed.
   Moving the file is not part of that change.
3. Once indexed provenance coverage is high, allow new agent-authored notes
   outside `vibes/`; the validator rejects new unannotated notes but
   grandfathers the old corpus.
4. Finally move useful notes to topic-based locations in small, reviewable
   commits. Stable note IDs keep incoming edges intact. Delete obsolete notes
   rather than preserving directory structure for history.

At every stage, the only authored truth is the plaintext file and its explicit
metadata. SQLite is a disposable, regenerated normalization and query index.
JSON, HTML, Forester trees, embeddings, and graph layouts are exports derived
from SQLite. Neither a database edit nor a generated-file edit is an accepted
authoring operation.

## Pilot and acceptance tests

The first pilot should be deliberately narrow:

1. Specify and parse the provenance frontmatter without rewriting note bodies.
2. Populate SQLite in one transaction, validate unique stable IDs and actor
   references, then export the map JSON from ordered SQL queries.
3. Give every map note page provenance, sources, incoming links, and revision
   history.
4. Export five notes to Forester with stable addresses and links.
5. Import a five-tree Forester corpus covering title, taxon, author, link, and
   transclusion.
6. Compare normalized facts, test broken-link diagnostics, and measure build
   time. Keep the experiment only if it reduces custom UI/indexing work.

## Open questions

- Should Covalence IDs share Forester's prefix-plus-base36 appearance, or only
  its stability and URI behavior?
- Is bidirectional Markdown/Forester editing actually valuable, or are a
  Forester import and generated export enough?
- Which actor identity is stable across agent providers: repository-local
  agent ID, signed external identity, or both?
- Does “checked” mean sources were inspected, claims were reproduced, proofs
  were kernel-checked, or should those be separate review predicates?
- Should theorem/program blocks live inside note plaintext, or be referenced
  as content-addressed artifacts with source spans? This decision should precede
  any ambitious Forester source-compatibility promise.

## Primary sources

- [Forester official source repository](https://git.sr.ht/~jonsterling/ocaml-forester)
- [Forester 5.0 opam package and dependency metadata](https://opam.ocaml.org/packages/forester/)
- [Forester 5.0 generated OCaml documentation](https://ocaml.org/p/forester/5.0/doc/index.html)
- [Jonathan Sterling's public forest](https://git.sr.ht/~jonsterling/public-forest)
- [Archived public-forest example and build instructions](https://github.com/jonsterling/forest)
- [opam package-management documentation](https://opam.ocaml.org/doc/Usage.html)
