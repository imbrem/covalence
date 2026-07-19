+++
id = "N002S"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:gpt-5.6-sol"
at = "2026-07-18T23:17:22+01:00"
source = "codex-development-wave"
agent = "gpt-5.6-sol"
harness = "codex"
+++

# Knowledge-browser applications

Status: working architecture sketch

## Products

The repository should contain three separate applications:

1. **`covalence-web`** is the prover/runtime interface. It connects to a
   Covalence server and presents executable artifacts, stores, proof sessions,
   and audit views.
2. **`covalence-map`** is the repository and generated-documentation browser.
   It presents notes, tasks, TODOs, source references, APIs, declarations,
   theorems, dependencies, and history. It should grow into the Covalence
   analogue of `cargo doc`.
3. **`category-wiki`** is a separate collaborative category-theory site. It
   consumes published mathematical content, supports editing, and checks proofs
   either in the browser or through a shared Covalence server.

These are separate deployable applications under `apps/`, not modes of one
application. They share packages under `packages/`.

## Bounded-width layering

```text
application routes, policy, persistence, collaboration
                         |
          document and graph feature packages
                         |
             common UI and API clients
                         |
           generated, versioned data contracts
```

The shared layer should contain mechanisms, not product policy:

- graph canvas, layouts, selection, search, filters, and accessible tabular
  fallback;
- document, declaration, theorem, proof-status, source-location, and
  cross-reference views;
- versioned TypeScript types and loaders for generated map/document indexes;
- syntax and mathematical rendering;
- browser and remote-server proof-client interfaces.

Application-owned concerns include routes, navigation, branding, authorization,
editing workflows, collaboration, publication, and persistence.

Proof checking is a service capability behind an interface. The viewer must not
make a browser runtime, shared server, or trusted proof result part of its
rendering model.

## Data contracts

Keep the current generic graph projection small:

```text
Node(id, kind, title, status, path, words, updated)
Edge(source, predicate, target, detail)
```

Richer indexes should be layered alongside it rather than widening every node.
For example, a generated documentation index can add declarations, signatures,
theorem statements, source spans, and proof dependencies while projecting
navigation relationships into the generic graph.

Generated facts are authoritative; layout coordinates, collapsed groups,
filters, and other view state are disposable overlays.

## Migration from the prototype

The first standalone `covalence-map` app validates the generated data and graph
interaction. Its static shell fetches a narrow JSON contract from local static
files by default; another origin can provide the same contract later. Next:

1. move the generic Cytoscape adapter and graph types into a shared package;
2. move map loading, filtering, detail panels, and fallback views into a
   `covalence-knowledge` feature package;
3. add a link or embedded read-only view in `covalence-web` only if useful;
4. add generated API/proof declarations without coupling them to notes/tasks;
5. scaffold `apps/category-wiki` only when its publishing and collaboration
   model is concrete enough to test.

This order avoids copying the prototype while also avoiding a premature
universal document schema.
