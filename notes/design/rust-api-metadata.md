+++
id = "N003E"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:gpt-5.6-sol"
at = "2026-07-19T00:45:35+01:00"
source = "api-metadata-design"
agent = "gpt-5.6-sol"
harness = "codex"
+++

# Rust API metadata and discovery

## Decision

Use a small attribute proc-macro crate as the authoring interface for stable
Covalence API metadata, but keep the normalized metadata outside compiled
programs:

```rust
#[covalence_api(
    id = "A0002",
    title = "Natural numbers",
    status = "experimental",
    depends_on(A0001),
)]
pub trait NatSyntax: Logic {
    // ...
}

#[covalence_api_impl(
    api = "A0002",
    name = "NativeHol",
    representation = "HOL natural-number leaves and definitions",
)]
impl NatSyntax for NativeHol {
    // ...
}
```

The macro should validate syntax and stable IDs, then return the annotated item
unchanged except for hidden documentation metadata. It must emit no runtime
registration, linker section, constructor, or theorem-producing code.

The repository indexer should continue to read tracked plaintext directly.
Later it can ingest rustdoc JSON as an additional projection, but rustdoc JSON
is currently experimental and should not be the authoring source of truth.

## Crate and trust boundary

Put the proc macros in a dedicated `covalence-api-macros` crate. API crates may
depend on it only as compile-time annotation machinery. The dependency graph
and TCB audit must distinguish proc-macro/build dependencies from runtime
dependencies so the annotations never appear to enlarge the executable TCB.

The macro implementation may use `syn` and `quote`: annotation parsing is not a
proof rule, and avoiding standard parsers would make the metadata validator
less auditable. The crate must nevertheless be small, contain no `unsafe`, and
have compile-fail tests for malformed and duplicate metadata.

## Indexed model

The normalized SQLite graph should contain:

- `api:A…` nodes with title, status, declaration path, and item path;
- `implementation` nodes with backend and representation;
- `depends-on`, `implements`, and `defined-in` edges;
- incoming `documented-by`, `tested-by`, `contains`, and `used-by` edges as
  those extractors become available.

An API is a capability surface, not necessarily a crate or one Rust trait.
Annotations should normally sit on the narrow root trait or public module that
names the surface. Individual subordinate traits can use a future `part_of`
field if item-level navigation proves useful.

## Retrieval contract

`bun run notes -- --api A0002` is the initial query. The next query should be a
bounded context pack:

```text
bun run notes -- --context api:A0002
```

It should return the declaration, direct dependencies, implementations,
associated notes and tasks, open TODOs, tests, and short source excerpts. This
is the default context-loading path for humans and agents before changing an
API.

## Migration

1. Keep the present JSON doc tags while the schema settles.
2. Implement and test the proc macro without changing API semantics.
3. Teach the plaintext indexer to parse the attribute syntax through one
   helper.
4. Migrate tags mechanically and reject duplicate IDs in CI.
5. Add rustdoc aliases for stable IDs where that improves ordinary cargo-doc
   search.
6. Expand the index only from demonstrated retrieval needs.

