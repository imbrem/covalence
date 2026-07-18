+++
id = "N0007"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:claude"
at = "2026-07-18T22:51:29+01:00"
source = "legacy"
agent = "claude"
harness = "claude"
+++

# Content, logic, and WIT boundaries

- **Status:** Draft for discussion
- **Owner:** maintainer
- **Last touched:** 2026-07-18
- **Related:** [`relational-base-rewrite.md`](relational-base-rewrite.md),
  [`../vibes/observers/backend-decoupling.md`](../vibes/observers/backend-decoupling.md),
  `crates/kernel/base/src/algebra.rs`, `crates/kernel/hol/api`,
  `crates/lang/inductive`, and `crates/lib/wasm/core/wit/store.wit`.

## Decision summary

Content addressing is not a theorem representation and does not add a
content-aware object to the TCB. Its foundation is a finite, monotone relation
of byte facts:

```text
Stored(hash_algorithm, digest, blob)
```

For a fixed algorithm and digest the relation is assumed to be functional:

```text
Stored(a, d, x) ∧ Stored(a, d, y)  ⇒  x = y
```

This is the collision-freedom assumption, stated explicitly and scoped to a
hash algorithm. A store is an implementation for finding rows in this
relation; it is not itself a source of theorems. The conceptual relation is
"everything ever hashed", while any memory or SQLite store is only a finite
snapshot.

Meaning is deliberately separate:

```text
Interprets(interpreter, blob, value)
```

An address for a term, theorem statement, program, database, or other
higher-level object is an ordinary blob address plus an interpreter. All
higher-level content-addressing APIs lower to these relations. They must not
introduce trusted hashing of in-memory terms or a deserializer that can mint a
theorem.

Stable consumer APIs should be developed before the foundation rewrite. Logic
and theory traits form an abstraction above the foundation. They will be
realizable by today's kernel and by the new relational foundation, and a
deliberately restricted form of those APIs will project to WIT for separately
compiled Covalence modules.

## Vocabulary

- **Foundation kernel:** the smallest trusted certificate machinery. This is
  the layer being redesigned around positive relations.
- **Host logic:** the logic in which Covalence develops mathematics and
  metatheory; intended to be HOL-ω. Today this spans parts of base, core, eval,
  and init.
- **Object logic:** a logic represented in the host logic, such as Metamath,
  ACL2, K, or Dedukti.
- **Logic API:** backend-neutral types, terms, propositions, theorems, binders,
  equality, and derivation operations.
- **Theory API:** a representation-independent mathematical or semantic
  interface built on a logic API, such as naturals, inductives, Lisp, or WASM.
- **Backend:** a realization of a logic or theory API.
- **Driver:** untrusted construction code using APIs and backends.
- **Project/module:** a separately distributable Covalence component, normally
  a WASM component plus content-addressed statement data.
- **Interpreter:** a relation assigning meaning to bytes. Parsing, decoding,
  type checking, and statement decoding are interpreters, not blob-store
  properties.

“Base layer” should mean **foundation kernel** when trust is intended. “Middle
layer” is too ambiguous; use **host logic**, **logic API**, or **theory API**.
“Inner logic” should be replaced by **object logic** unless it specifically
means the host logic used inside a translation.

## Trust boundary for content addressing

### Logical model

`Stored(a, d, b)` says that bytes `b` have digest `d` under algorithm `a`.
An implementation may use an append-only table:

```sql
CREATE TABLE blobs (
    algorithm TEXT NOT NULL,
    digest    BLOB NOT NULL,
    bytes     BLOB NOT NULL,
    PRIMARY KEY (algorithm, digest)
);
```

The schema illustrates the relation; it is not trusted code. Lookup, networking,
caching, and hash execution remain ordinary untrusted computation. A retrieved
row is checked by recomputing its digest. Positive membership can later be
reflected through the relational foundation like any other executed relation.
Absence from a finite snapshot proves nothing about the global relation.

Collision freedom is an explicit assumption package, not an accidental
property hidden in a Rust map. Algorithms have distinct assumption identities,
and policy can reject weak algorithms without changing the foundation. The
foundation needs only byte equality, relation membership, and functionality;
it does not need SHA-256, SQLite, Merkle trees, terms, or theorem serialization.

### Interpretation

Interpretation is partial and may be relational rather than functional:

```text
Interprets(I, bytes, x)
```

Examples include “these bytes decode as this UTF-8 string”, “this database
encodes these base facts”, and “this encoding denotes this host-logic
proposition”. Determinism, canonical encoding, soundness, and round trips are
separate theorems about an interpreter. Stacking interpreters gives stacking
APIs without changing identity:

```text
bytes --UTF-8--> text --Metamath parser--> database --translator--> proposition
```

A “content-addressed theorem” is a proved theorem about the interpretation of
addressed statement bytes. An opaque live theorem handle is never serialized
and recovered by trust.

### Addressing a database

A database snapshot is another blob. SQLite bytes may be hashed directly, and
an external `(algorithm, digest)` names that exact artifact. The database must
not contain its own digest as part of the hashed bytes; a module manifest or
store row names it externally.

Byte identity and logical database identity differ. SQLite page layout,
vacuuming, and metadata may yield different blobs for equivalent rows. That is
acceptable for artifact identity. If reproducible semantic identity is needed,
a canonical logical export is a separate interpreter and format, not extra
foundation machinery.

Reloading yields bytes and rows, never theorem values. Facts become theorems
only by replay, checked relation execution, or an explicitly scoped attestation
assumption.

## Stable API stack

The dependency direction is:

```text
foundation kernel
        ↑
foundation adapter
        ↑
logic API
        ↑
theory capability APIs
        ↑
drivers / Lisp / SMT / Metamath / project modules
```

The logic API owns its traits and vocabulary. It must not depend on
`covalence-init`, concrete evaluators, or native backend implementations.
Today's `covalence-hol-api` violates that direction and is the first extraction
target. The existing `CertificateAlgebra` is a useful foundation seam, but it
is not the complete high-level logic API.

Theory APIs split into capabilities. For naturals, for example:

```text
NatSyntax       zero, successor, literals, observation
NatAdd          addition operations
NatOrder        order operations
NatLaws         theorem-producing algebraic laws
NatDecision     optional accelerated decision procedures
```

A partial backend implements fewer capability traits. Normal methods should not
contain `todo!()` or return “not implemented”. This makes gaps statically
visible, permits focused conformance suites, and maps naturally to versioned
WIT interfaces. Syntax, laws, interpretations, and accelerators are separate.

## Numerics as the first stress test

Numerics should deliberately have several backends:

- native/word-like encodings for execution;
- successor and double/successor naturals;
- integers as signs plus naturals and as difference encodings;
- Church or System F encodings;
- solver-backed views for SMT/SAT;
- later, rationals, floating point, and ball arithmetic.

The product is not merely several implementations but explicit relations:

```text
Iso<A, B>:
    forward: A → B
    backward: B → A
    backward(forward(a)) = a
    forward(backward(b)) = b
```

When isomorphism is too strong, use named interpretation, refinement, or
partial-equivalence packages rather than weakening `Iso`. Conformance tests
are shared per capability; round-trip and operation-preservation proofs test
consilience. SMT proposition size, proof construction time, import throughput,
and WASM boundary overhead are first-class metrics.

## Traits projected to WIT

Arbitrary Rust traits cannot compile faithfully to WIT: WIT lacks Rust
generics, associated types, higher-kinded types, and proposition-indexed method
signatures. Covalence should define a **WIT-projectable trait subset**, not
promise to export every Rust trait.

One declarative API description (an attribute macro or small schema) should
generate:

1. ergonomic Rust capability traits;
2. monomorphized WIT interfaces and worlds;
3. host and guest bindings;
4. a conformance harness for Rust and component implementations.

WIT uses opaque resource handles for types, terms, propositions, and live
theorems, plus records/variants for addresses, statement identifiers, and
errors. A theorem resource has process/component lifetime and is not a
serialized proof object. Versioned interfaces represent capabilities; a module
imports only those it needs.

The current `cov:store` WIT remains a useful lookup service, but its key should
be refined to an address containing algorithm identity and digest. Its
documentation must state that `get` is untrusted retrieval. Existing
term/theorem-shaped WIT files are backend projections, not foundation APIs.

## Covalence project artifact

The initial project format can remain small:

- a WASM component importing versioned Covalence capability interfaces;
- a statement database containing only serialized statement bytes and stable
  entrypoint identifiers;
- optional metadata naming required capabilities and interpreters.

For single-file distribution, the statement database can be a WASM custom
section. The entire component is hashed externally as an ordinary blob. The
embedded database does not claim the component's own address, avoiding a
self-hash cycle. A module proves a statement by entrypoint using host-provided
opaque handles; loading statement data does not mint its theorem.

SQLite is a reasonable first statement database because the system already
uses it and it supports global queries. A compact canonical format can be
introduced later without changing the content or interpretation model.

## Parallel workstreams

```text
A. Logic seam ───────┬──> C. Numerics backends ──> E. consilience benchmarks
                     ├──> D. Inductive/Lisp split
B. API schema + WIT ─┘             │
F. Blob relation/store ──> G. project artifact/runtime ──> module ecosystem
                     \─────────────> relational foundation integration
```

### A. Extract the logic seam

1. Move ownership of the `Hol`-like trait into a dependency-light API crate.
2. Give it associated backend types and an associated error type.
3. Move the current implementation into a native backend adapter.
4. Remove `covalence-init` and evaluator dependencies from the API crate.
5. Port one real consumer without changing semantics.

Acceptance: a consumer compiles against only logic and capability APIs while
the old kernel remains underneath.

### B. Prove the Rust-to-WIT shape

Start with opaque term/proposition/theorem resources plus `NatSyntax` and
`NatAdd`. Generate or hand-pair one Rust trait and WIT interface to discover
canonical-ABI constraints before building a generator. Exercise it with an
out-of-process WASM guest.

### C. Split numerics into capabilities

Refactor the monolithic `Nat` and `Int` traits. Preserve existing operations
through temporary blanket adapters. Implement two natural representations and
an `Iso` package, then use one conformance suite for both.

### D. Extract inductive and Lisp adapters

Keep `covalence-inductive` logic-agnostic; move its HOL realization out of
`init` behind the logic API. Keep kernel-independent Lisp syntax and generic
`Repr`/`Semantics` axes, and move the concrete HOL carrier into a backend
adapter. This consumes A; it is not a prerequisite.

### F. Make the blob model explicit

Introduce untrusted `BlobAddress { algorithm, digest }` and a blob-relation
library shared by memory, filesystem, and SQLite stores. Retrieval verifies the
digest. Update `cov:store` WIT without adding theorem concepts. Add a SQLite
snapshot round-trip and address-the-database test.

### G. Spike the project format

Build one component containing a tiny statement database and importing the
numeric WIT capability. Hash the finished component externally, load it,
resolve a statement entrypoint, and return an opaque theorem handle. This
validates the boundary before the foundation rewrite.

## Metrics and gates

- zero `covalence-init` dependencies from stable API crates;
- consumer imports of concrete `core` term representations trend to zero;
- two numeric backends pass one capability conformance suite;
- one proved round-trip and one operation-preservation theorem between them;
- native and WASM proof construction latency measured separately;
- SMT proposition size and SAT/SMT construction throughput do not regress;
- Metamath import throughput remains an end-to-end benchmark;
- blob retrieval cannot produce accepted bytes without digest verification;
- loading a project or database adds no theorem-minting site.

## Immediate recommendation

Start A, B, and F together. A supplies a real stable surface, B prevents it from
becoming impossible to expose through WIT, and F fixes content identity without
waiting for logic or foundation design. Use numerics as the first shared
consumer. Extract inductives next, then Lisp, because their generic cores
already provide useful seams.

The first vertical demonstration should be deliberately narrow:

```text
two Nat backends
  + one proved isomorphism
  + one generated/projected WIT capability
  + one separately compiled guest
  + statement bytes addressed through the blob relation
```

That demonstration exposes foundation requirements, ABI costs, trait
ergonomics, and content/database behavior with measurable results.

## Open questions

- Is algorithm identity a symbolic name, a content-addressed interpreter, or
  initially a closed registry?
- Is collision freedom admitted globally per algorithm or supplied as a scoped
  project assumption?
- Should the first SQLite artifact identify exact bytes only, or also ship a
  canonical logical export?
- Which subset of the current `Hol` surface is required by the first numeric
  guest?
- Should a schema generate Rust and WIT equally, or should a WIT-shaped Rust
  trait be the source of truth?
- How are WIT resource lifetimes and theorem ownership represented across
  nested module calls?
