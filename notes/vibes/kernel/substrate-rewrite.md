+++
id = "N0054"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:gpt-5.6-sol"
at = "2026-07-20T00:00:00+01:00"
source = "substrate-first-pass"
agent = "gpt-5.6-sol"
harness = "codex"
+++

# Substrate rewrite: SQLite-backed nucleus

This is a first-pass plan, deliberately short of a final API. It names the
boundaries, removes contradictions in older proposals, and identifies the
experiments needed before the maintainer's handwritten design is transcribed.
The current base may be replaced deeply. Higher-level capability APIs should be
refined and retained wherever they express the right mathematics.

## Vocabulary

| Term | Meaning |
|---|---|
| **substrate** | The computational and persistence foundation exposed to higher layers. |
| **nucleus** | One running kernel state machine: proton plus neutron and their checked transitions. |
| **proton** | Ephemeral in-memory terms, theorem values, inference state, and fast structural operations. |
| **neutron** | The nucleus's in-memory SQLite database: finite relational state, evidence, provenance, and persistence image. |
| **snapshot** | A serialized neutron database, optionally content-addressed and signed. |
| **replay** | Checking an untrusted snapshot/evidence stream by applying nucleus transitions. |
| **accelerator** | Optional computation whose result is accepted only through a scoped checked rule or replay path. |

Avoid the ambiguous old names “base”, “pure”, and “kernel” in new design prose
unless referring to a concrete existing crate.

## Non-negotiable invariants

1. **Rows do not mint facts.** SQL operations manipulate state and evidence;
   theorem construction remains behind checked nucleus transitions.
2. **Only a small SQL fragment is trusted.** Much of the TCB should be simple
   queries over trusted in-memory tables, but only typed, fixed query shapes are
   nucleus transitions. Arbitrary SQL can propose candidate state and cannot
   promote it.
3. **Positive observations are finite and explicit.** Hashes, executions,
   signatures, and imports are represented by the observations present in this
   nucleus, not universal claims about an external world.
4. **Trust is inspectable.** A theorem or accepted snapshot exposes its logical
   assumptions, accelerators/executors, signer policy, and source state.
5. **Unaccelerated checking exists.** Accelerator semantics can be tested and
   proved without depending circularly on the accelerator being validated.
6. **Higher objects lower.** Terms, theorems, modules, and databases are
   content-addressed as blobs plus an interpretation, not as extra hash
   primitives in the substrate.
7. **Transactions are atomic nucleus transitions.** Proton updates and neutron
   commits cannot leave an externally visible half-transition.
8. **The durable format is versioned and deterministic.** Schema, canonical
   dump/hash rules, and migrations are explicit.
9. **Substrate equality is not HOL equality.** Row identity, projections, and
   meta-judgements can be used to implement HOL, but do not inherit HOL meaning
   until an explicit grounding/bridge supplies it.
10. **Relations lift without interpretation.** Every substrate relation can be
    named as an uninterpreted HOL relation. Separate assumptions state what its
    observations mean.

## Conceptual state

The maintainer's live relational sketch is [`N0056`](../../plans/relational-design.md),
refined by the concrete SQLite design in
[`N005H`](../../plans/covalence_substrate_design.md). Its initial API direction is
stronger than merely persisting theorem records:

- everything, including `MThm`, should have a relational interpretation;
- a `Set` separates its logical element type (`Expr<Self::Elem>`) from the
  witness representation actually stored;
- an `MThm` over a set carries a witness and certifies which logical element it
  denotes or places in that set;
- a relation is a set with projectable columns, numbered canonically and
  optionally named;
- serializable sets connect logical elements to SQLite rows;
- schema metadata records how table keys refer to objects.

The full sketch adds five important pieces:

1. Columns have substrate types and roles. `DEF(ty)` introduces an opaque
   object, `USE(table, ty)` references an object defined by another table, and
   `NAME(ty)` ranges over a global unrealized namespace such as a cryptographic
   `seen` relation. Data columns participate directly in a relation; metadata
   columns do not unless named by its interpretation.
2. Rows support projections such as `lhs@id` or `hash@id`. A row ID may witness
   a structured object while field projections expose its components without
   adding artificial equalities like `id = blob`.
3. Relations are normally open-world. A scoped `COMPLETE` declaration is the
   exceptional evidence that a table exhausts a relation along selected
   projections, enabling closed-set and negative reasoning. Duplicate rows may
   carry meaning for multisets, so `ROWID` and `WITHOUT ROWID` cannot be treated
   as interchangeable implementation details.
4. A single database may carry relations grounded by different TCBs. Grounding
   is flexible and partial, and may be selected per table or by a TCB column.
5. Well-known O256 names identify substrate types, relations, runtimes, and
   specifications without relying on local strings. Their grounding should be
   anchored to manifests/specifications; random names remain available for
   genuinely fresh identities.

This makes the key API question not “how do we serialize today's theorem
struct?” but “what common relational interface is implemented by proton values
and neutron tables?” The first prototype should therefore exercise one set with
two witness representations—an in-memory witness and a SQLite row—plus a
checked theorem-preserving conversion between them.

The substrate metamodel should precede any fixed application schema:

```text
substrate types
well-known and fresh names
relation definitions
column definitions: DEF | USE | NAME | DATA | METADATA
column substrate types and optionality
relation/table groundings and their TCB
completeness declarations
row/field projections
```

`N005H` makes physical schema requirements part of checking a table
interpretation. The expression itself refers to typed slots; the interpretation
binds those slots to columns through partial representations. Closed expressions
have an empty context and no schema dependency.

A table interpretation is a predicate on rows. Its basic positive theorem is
`All(rows, interpretation)`; `Any`, `Not(All)`, and `Not(Any)` are useful dual
forms with distinct witness or completeness requirements. Translation of
SQLite values through a representation is partial. Initially require schema
validation proving referenced values decode; do not make epsilon fallback the
default meaning of malformed or `NULL` data.

`DEF` and `USE` are mutation disciplines. A `DEF<T>` column maps each distinct
physical key to an erased value of `T`, scoped at least by table, column, and
representation. Reusing a key with changed defining fields requires a proof
that the meanings agree, or atomic removal of the old definition and all
invalidated dependents. `USE<T>` names its defining source. The same physical
column interpreted at different types creates independent maps.

The focused expression plan is [`N005I`](./substrate-expressions.md). It reserves
**schema** for SQLite structure, calls expression inputs a **context**, and
moves column binding into a **table interpretation**. Its dynamic expression
tree is the durable reference semantics; a Rust associated-type API is a
checked façade over that representation. Use that vocabulary below.

Application relations—terms, typing, implications, blob observations,
executions, derivations, signatures, and roots—are then ordinary instances of
that metamodel. The database may also contain indexes, caches, denormalized
query aids, and ignored application tables. Its mathematical interpretation
must explicitly select the relations and columns that matter. A schema is not
itself a logic.

### Worked relational shapes

The design should be tested against these examples before generalization:

```text
App(id DEF(HolTerm), lhs USE(Tm, HolTerm), rhs USE(Tm, HolTerm))
HasTy(tm USE(Tm, HolTerm), ty USE(Ty, HolType))
Imp(lhs USE(Tm, HolTerm), rhs USE(Tm, HolTerm))
Member(lhs, rhs) + COMPLETE(rhs)
Cas(id DEF(Blob), hash NAME(Digest), key DATA?, data DATA?)
```

A fixed-type table can omit a type column; a family of constructor relations
may instead use discriminants, sums, or dependent table sources. Basic
substrate polymorphism is now a design question driven by storage reuse, not by
HOL polymorphism. Start monomorphic and prove that real examples require more
before extending the trusted metamodel.

The proton owns compact live representations and theorem handles. References
between proton and neutron need generation/transaction discipline so stale
handles cannot cross rollback or snapshot replacement. Whether terms are
interned by digest, integer row ID, arena handle, or a combination remains an
experiment.

The neutron is the canonical relational form, not merely persistence. Proton
structures are optimized indexes/witnesses over it. A future e-graph is a third
optimized form with the same obligation: checked import/export or
reconstruction against neutron relations. The trusted database operation sketch
is [`N0057`](./trusted-database-algebra.md).

## Trusted database algebra

The intended TCB is dominated by a small typed relational fragment compiled to
prepared SQL: trusted lookup, projection, typed selection, compatible union,
equi-join, semijoin, and intersection. Difference and negative reasoning
require explicit completeness. Aggregates, recursive CTEs, implicit coercions,
collations, user functions, and arbitrary SQL are outside the initial trusted
fragment.

Core multi-database transitions attach trusted and untrusted databases under
separate capabilities; merge compatible trusted states; compare candidate rows
with trusted rows or premises; reprove candidates and retain only checked
conclusions; signature-promote exact snapshots under policy; and extract
root-reachable trusted subdatabases. Filtering must weaken completeness/global
claims when it cannot preserve them.

This gives the distributed system its basic unit: every worker receives a DB
snapshot and returns a whole DB or filtered subDB. Coordination is checked merge
and selective promotion rather than shared theorem-arena mutation.

## Signed and untrusted states

A signature does not automatically confer trust. Loading has two modes:

- **accept**: a policy recognizes the signer and state format, so the snapshot
  becomes a trusted serialized nucleus state with that policy recorded;
- **replay**: rows and signatures are untrusted inputs, and relevant derivations
  are reconstructed through checked transitions.

These modes may yield extensionally equal theorem sets while retaining
different trust dependencies. That is a useful consilience test.

Trust reporting has two orthogonal components:

- **execution/grounding TCB**: why rows under a well-known relation name are
  faithful observations of the named computation or meta-judgement;
- **HOL assumption set**: which implications connect those uninterpreted
  observations to HOL truth or object-logic derivability.

For example, a runtime may populate a well-known `WasmStep` relation under an
execution TCB, while an ordinary segregated HOL assumption states that selected
steps refine a particular WASM specification. Keeping these separate allows the
same execution state to be interpreted under competing specifications.

## Relation to the current code

Reusable pieces already exist, but none should dictate the new core:

- `crates/store/core` has memory and SQLite content stores;
- `crates/store/kv` has sync/async storage capabilities;
- `crates/vcs/object` has hashed table/tree formats;
- `crates/kernel/core` currently wires a content store to a shell-like kernel;
- `crates/kernel/base` has experiments in positive relational execution;
- the high-level logic/data/Lisp/parsing APIs provide migration consumers.

The current `Kernel`, `SyncBackend`, object formats, and relational minting
model are candidates for replacement. In particular, old prose saying a store
lookup or database row “mints” a theorem is superseded by this design.

## Rewrite DAG

```text
S0 terminology + invariants
 ├─ S1 SQLite model + context-indexed expressions
 ├─ S2 table interpretation + Set/Relation/MThm API
 └─ S3 high-level API inventory and compatibility harness
       ↓
S4 DEF/USE mutation model + dual witness spike
       ↓
S5 trusted query + multi-DB algebra
       ↓
S6 proton/neutron transition API
 ├─ S7 blob + snapshot identity
 ├─ S8 derivation replay
 └─ S9 trust/signature policies
       ↓
S10 WASM instance/lifecycle relations
       ↓
S11 differential old/new backend
       ↓
S12 audit, benchmark, then replace old substrate
```

## Work packages

### S0 — design vocabulary

Acceptance: one glossary, explicit authority boundary, and removal or clear
supersession of contradictory notes. This document is the initial artifact.

### S1 — SQLite model and context-indexed expressions

Model only SQLite features with logical significance: storage classes, `NULL`,
affinity, strictness, columns, relevant constraints, keys/rowid, and rows.
Exclude indices and defer generated columns. Specify context-indexed `Expr`,
partial representations, table bindings from slots to columns, and dynamic
input analysis. Initially choose fail-closed validation over epsilon
totalization. Add static input analysis only after the dynamic semantics works.

### S2 — table interpretation and relational paper API

Specify table predicates and `All`, `Any`, `NotAll`, and `NotAny`; then `Set`,
`Relation`, witnesses, projections, and `MThm` independently of Rust layout.
State which forms require row witnesses or completeness. Add substrate types;
`DEF`, `USE`, `NAME`, data and metadata roles; row identity; duplicates; sums;
named and generic table variables; and partial host groundings. Include SQLite
`INTEGER` range checks and a dynamic rendition beside the Rust-shaped API.

### S3 — freeze consumers, not representations

Inventory operations actually required by Metamath, ACL2/Lisp, SMT/SAT,
parsing, and WASM. Turn them into capability-sized interfaces and black-box
conformance suites. Record latency, allocation, database size, and replay cost
for representative workloads. Do not add a compatibility method merely because
the current kernel exposes it.

### S4 — definition discipline and dual witness spike

Implement one term relation and one typing relation twice: direct in-memory
witnesses and SQLite rows. Demonstrate construction, projection, foreign-key
validation, open-world membership, one scoped completeness claim, and checked
conversion preserving the same `MThm` statement. Measure prepared-query and
allocation costs; discard the implementation if its types distort the paper
API. Exercise `DEF` key reuse with both a proved-equal replacement and a
rejected conflict, and include nullable or malformed candidate rows.

### S5 — trusted query and multi-database algebra

Define the typed query AST and trust propagation for lookup, projection,
selection, union, equi-join, semijoin, and intersection. Implement multi-DB
attach, compatible trusted merge, candidate comparison, proof-filtered
promotion, and root-reachable subDB extraction. Differentially execute every
primitive against SQLite and a tiny independent relation interpreter. Specify
exactly which SQLite version/configuration behavior enters the TCB.

### S6 — nucleus transition API

Write the state-transition model and define the sole boundary where proton and
neutron change together. Separate:

- state membership;
- theorem authority;
- assumptions and trust dependencies;
- snapshot equivalence;
- merge/join conditions;
- failure and rollback.

Candidate shape: prepare evidence, validate against the current state, construct
theorem and relational deltas, commit transaction, then publish handles. Specify panic,
OOM, interruption, rollback, concurrency, and stale-handle behavior.

### S7 — content and snapshots

Implement the finite blob observation relation and canonical snapshot identity.
Hashing the database requires a canonical logical representation; hashing raw
SQLite file bytes is only acceptable if byte-level determinism is explicitly
part of the format. Support database-as-blob without recursively assuming its
own hash.

### S8 — replay

Define a minimal derivation/event log sufficient to reconstruct exported roots.
Replay must not trust SQL query results. It should be possible to retain full
execution evidence, compact it to intermediate checkpoints, or retain only a
proved theorem, with each choice visible in provenance.

### S9 — signatures

Keep cryptographic verification separate from authorization policy. Specify
what exactly is signed: canonical snapshot identity, schema/version,
interpretation, roots, and possibly trust assumptions. Demonstrate accept and
replay modes for the same snapshot.

### S10 — WASM lifecycle

Model initialization and linking explicitly rather than jumping straight to a
single `executes` tuple. Candidate relations include `StartInit`,
`LinkMemory`, `LinkModule`, `LinkFunction`, `FinishInit`, and `Call`, with
before/after state identities. Runtime kind/version/subset, concrete executor,
hardware or attestation identity, and timestamps are separate relations or
metadata. Lift each relation uninterpreted into HOL, then state refinement to
SpecTec/K/other WASM semantics as ordinary conditional assumptions or proofs.

### S11 — differential backend

Run the old implementation and new nucleus behind the same high-level APIs.
Compare exported statements, assumptions, and proof results—not internal term
IDs. This is the primary defense against a premature flag day.

### S12 — vertical slice and replacement

Recommended first three slices:

```text
App + HasTy → dual witnesses → projection → same MThm
bytes → Cas/seen relation → snapshot → reload/replay
WASM init/link/call → uninterpreted HOL lift → one semantic bridge
```

Metamath import is the first scale benchmark; SMT/SAT stresses proposition and
bitvector representation; ACL2/Lisp stresses recursive definitions and
execution traces. Only after correctness and performance gates pass, move
audited modules onto a fresh main line one by one. Delete adapters as their last
consumer migrates.
Keep old snapshots readable through a versioned importer, not permanent core
branches.

## Metrics

- trusted source lines and mint/transition sites;
- theorem replay throughput and peak memory;
- set.mm import wall time and scaling curve;
- SQLite rows, bytes, transactions, and hot-query latency;
- trusted query-fragment size and independently cross-checked row count;
- trusted merge, candidate filtering, and subDB extraction throughput;
- snapshot size and deterministic rebuild time;
- number of high-level consumer changes required;
- trust-dependency size per exported theorem;
- differential agreement between old/new and accept/replay paths.

## Decisions needed from handwritten notes

Before production implementation, resolve:

- the exact primitive proposition/relation language;
- the laws and object-safety/dynamic equivalent of `Set`, `Relation`, and
  `MThm`;
- whether `DEF` identities denote opaque chosen values, witness identities, or
  both through separate projections;
- the precise semantics and trusted checks for `COMPLETE`;
- whether the four table propositions are primitive or derived, and how
  insertion and deletion affect each;
- the representation-failure and `NULL` policy after the first prototype;
- the scope of a `DEF` mapping and the transaction required for key reuse;
- the ergonomic Rust form of context-indexed expressions (the dynamic form and
  its authoritative input set are fixed by `N005I`);
- whether sums/dependent table sources are primitive or compiled to monomorphic
  relations;
- in-memory term identity and lifetime model;
- whether theorem handles directly reference neutron rows;
- transaction granularity and concurrent nucleus semantics;
- schema interpretation and canonical snapshot encoding;
- minimal accepted signed-state policy;
- which accelerators belong in the initial nucleus configuration;
- how multiple TCB groundings coexist in one database and compose;
- which well-known O256 namespaces are specification-derived and which permit
  random freshness.

The unfinished key/object ideas in `N0056` and `N005H` should be completed
before the schema is frozen. In particular, decide whether a key identifies a
logical object, a witness row, a content-addressed blob, or a typed reference
connecting those layers.
