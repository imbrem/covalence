# Verified graph API and interchange

- **Status:** Draft
- **Owner:** maintainer
- **Last touched:** 2026-07-18
- **Related:** [`content-logic-and-wit-boundaries.md`](content-logic-and-wit-boundaries.md),
  `crates/lib/graph`, and `crates/lib/graph/wit/graph.wit`.

## Direction

The existing ordered port graph is not the universal Covalence graph API. It is
a valuable concrete model whose insertion-order and linear-input semantics were
designed for component linking and string diagrams. Preserve it as a
first-class **port graph** backend and build adapters to the graph concepts that
apply to it; stop treating it as the default representation of every graph.

The general API starts from finite relations and defines distinct primary
traits rather than a single graph trait controlled by flags:

```text
Graph             finite undirected simple graph
DiGraph           finite directed simple graph
MultiGraph        finite undirected graph with edge identity
MultiDiGraph      finite directed graph with edge identity
HyperGraph        finite undirected hypergraph
DirectedHyperGraph finite directed hypergraph
PortGraph         nodes with typed, directed input/output ports
```

Each trait has the incidence/adjacency vocabulary natural to its kind.
`Weighted<G>`, `VertexLabeled<G>`, and `EdgeLabeled<G>` are orthogonal
extensions or associated capabilities, not new storage formats. Shared
supertraits capture only genuinely common operations such as finite vertex
enumeration.

These traits do not fix storage, insertion order, identifier choice, or
serialization. Concrete backends may use adjacency lists, matrices, edge
lists, relations, NetworkX-compatible data, or port graphs. Conversions state
which information they forget: for example a port graph's underlying digraph
forgets port identity, types, and ordering, while its string-diagram
interpretation preserves those structures.

## Verified properties and algorithms

Separate computed witnesses from checked propositions:

- a path witness is checked edge by edge;
- a connectivity witness is a path;
- an acyclicity witness may be a topological order;
- a cycle witness disproves acyclicity;
- a shortest-path witness contains a path plus distances/potentials sufficient
  to prove no shorter path exists;
- spanning trees, components, colorings, and planar embeddings likewise have
  explicit certificate types.

Algorithms are untrusted producers of witnesses. Small checkers lower witness
validity to the logic relation API and yield theorems. Negative and optimality
claims require certificates strong enough to check positively; they must not be
accepted merely because a search found no counterexample.

This gives useful benchmark stages:

```text
bytes → parse witness → graph value → algorithm witness → checked proposition
```

Track parsing throughput, graph construction size, witness size, checker time,
and final proposition/theorem size independently.

## Interchange

DOT is the first parser target. Its parser must retain enough source and
semantic information to prove that the resulting graph interprets the input
bytes. DOT's defaults, subgraphs, compass points, identifiers, and directed vs
undirected edge syntax should be modeled explicitly rather than discarded by a
convenience parser.

NetworkX interoperability should cover its common read/write families in
increments:

1. node-link JSON and adjacency JSON;
2. adjacency lists, multiline adjacency lists, and edge lists;
3. weighted edge lists;
4. GraphML and GEXF;
5. Pajek and other formats as demand warrants.

Each format gets a data model, byte/text interpreter, import/export relation,
round-trip laws, and property-preservation theorems. “Same graph” should be an
explicit isomorphism or labeled isomorphism, not Rust structural equality.

## Dependency DAG

```text
logic relations ───────> graph theory traits ───> property certificates
finite collections ────┘          │                        │
text/parsing APIs ──> DOT/NetworkX interpreters ────────────┤
port graph/string diagrams ─> specialized backend + adapters│
                                                        benchmarks
```

The plain-data graph traits and certificate structures can begin without a
concrete HOL backend. The theorem-producing checker API should wait for the
logic relation extraction now in progress. Parser work should reuse the
planned byte/string/parser APIs instead of making a graph-specific parsing
framework.

## First vertical slice

1. Define finite directed and undirected graph traits plus an owned edge-list
   reference backend.
2. Define path and topological-order certificates with pure checkers.
3. Parse a strict, useful DOT subset into the reference backend.
4. Export/import NetworkX node-link JSON and weighted edge lists.
5. Adapt checker results to logic propositions and theorem-producing APIs.
6. Benchmark DAG parsing, acyclicity checking, reachability, and weighted
   shortest paths on stable fixture corpora.

## Architecture rule

Do not force general graph-theory semantics into the port-graph representation,
and do not erase port/order/type information to make it fit a simpler trait.
General algorithms target the appropriate abstract graph trait. Port-graph and
string-diagram algorithms target their richer specialized trait, with explicit
forgetful or interpretation adapters where general algorithms are useful.
