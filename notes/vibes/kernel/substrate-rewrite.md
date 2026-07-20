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
2. **SQLite is state, not the logical foundation.** Bugs in a query may cause a
   failed replay or wrong candidate result, but must not silently fabricate a
   theorem unless that query is explicitly inside the selected TCB policy.
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

## Conceptual state

The maintainer's live relational sketch is
[`N0056`](../../plans/relational-design.md). Its initial API direction is
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

This suggests the key API question is not “how do we serialize today's theorem
struct?” but “what common relational interface is implemented by proton values
and neutron tables?” The first prototype should therefore exercise one set with
two witness representations—an in-memory witness and a SQLite row—plus a
checked theorem-preserving conversion between them.

The first useful neutron schema should express roles, not freeze table names:

```text
blob observations     (algorithm, key, digest, bytes)
execution observations(executor, program, input, start, output, end)
assumptions            (scope, proposition/interpreter reference, provenance)
derivations            (rule, inputs, output, replay payload)
signatures             (key, signed object/state, signature)
roots                  (named exported theorem/state roots)
metadata               (ignored by mathematical interpretation unless named)
```

The database may contain indexes, caches, denormalized query aids, and ignored
application tables. Its mathematical interpretation must explicitly select the
relations that matter. A schema is not itself a logic.

The proton owns compact live representations and theorem handles. References
between proton and neutron need generation/transaction discipline so stale
handles cannot cross rollback or snapshot replacement. Whether terms are
interned by digest, integer row ID, arena handle, or a combination remains an
experiment.

## Signed and untrusted states

A signature does not automatically confer trust. Loading has two modes:

- **accept**: a policy recognizes the signer and state format, so the snapshot
  becomes a trusted serialized nucleus state with that policy recorded;
- **replay**: rows and signatures are untrusted inputs, and relevant derivations
  are reconstructed through checked transitions.

These modes may yield extensionally equal theorem sets while retaining
different trust dependencies. That is a useful consilience test.

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
 ├─ S1 high-level API inventory and compatibility harness
 ├─ S2 minimal mathematical state model
 └─ S3 SQLite behavior/profiling spike
       ↓
S4 proton/neutron transaction API
 ├─ S5 blob + snapshot identity
 ├─ S6 derivation replay
 └─ S7 trust/signature policies
       ↓
S8 second backend + differential tests
       ↓
S9 migrate one vertical proof path
       ↓
S10 audit, benchmark, then replace old substrate
```

## Work packages

### S0 — design vocabulary

Acceptance: one glossary, explicit authority boundary, and removal or clear
supersession of contradictory notes. This document is the initial artifact.

### S1 — freeze consumers, not representations

Inventory operations actually required by Metamath, ACL2/Lisp, SMT/SAT,
parsing, and WASM. Turn them into capability-sized interfaces and black-box
conformance suites. Record latency, allocation, database size, and replay cost
for representative workloads. Do not add a compatibility method merely because
the current kernel exposes it.

### S2 — mathematical model

Write a small paper model of a nucleus state and its transitions. Separate:

- state membership;
- theorem authority;
- assumptions and trust dependencies;
- snapshot equivalence;
- merge/join conditions;
- failure and rollback.

Prove or mechanically test the invariants on a toy implementation before
choosing the production Rust types.

### S3 — SQLite spike

Prototype an in-memory database with transactions, prepared statements,
snapshot export/import, deterministic logical dumps, and the likely hot joins.
Measure it against current set.mm and parser/SMT-shaped access patterns. This
spike is disposable and contains no theorem authority.

### S4 — nucleus transition API

Define the sole boundary where proton and neutron change together. Candidate
shape: prepare evidence, validate against the current state, construct theorem
and relational deltas, commit transaction, then publish handles. Specify panic,
OOM, interruption, rollback, concurrency, and stale-handle behavior.

### S5 — content and snapshots

Implement the finite blob observation relation and canonical snapshot identity.
Hashing the database requires a canonical logical representation; hashing raw
SQLite file bytes is only acceptable if byte-level determinism is explicitly
part of the format. Support database-as-blob without recursively assuming its
own hash.

### S6 — replay

Define a minimal derivation/event log sufficient to reconstruct exported roots.
Replay must not trust SQL query results. It should be possible to retain full
execution evidence, compact it to intermediate checkpoints, or retain only a
proved theorem, with each choice visible in provenance.

### S7 — signatures

Keep cryptographic verification separate from authorization policy. Specify
what exactly is signed: canonical snapshot identity, schema/version,
interpretation, roots, and possibly trust assumptions. Demonstrate accept and
replay modes for the same snapshot.

### S8 — differential backend

Run the old implementation and new nucleus behind the same high-level APIs.
Compare exported statements, assumptions, and proof results—not internal term
IDs. This is the primary defense against a premature flag day.

### S9 — vertical slice

Recommended first slice:

```text
bytes → finite seen relation → one proof object → snapshot → reload/replay
      → same exported theorem and trust report
```

Then add a stateful WASM execution observation. Metamath import is the first
scale benchmark; SMT/SAT stresses proposition and bitvector representation;
ACL2/Lisp stresses recursive definitions and execution traces.

### S10 — replacement

Only after correctness and performance gates pass, move audited modules onto a
fresh main line one by one. Delete adapters as their last consumer migrates.
Keep old snapshots readable through a versioned importer, not permanent core
branches.

## Metrics

- trusted source lines and mint/transition sites;
- theorem replay throughput and peak memory;
- set.mm import wall time and scaling curve;
- SQLite rows, bytes, transactions, and hot-query latency;
- snapshot size and deterministic rebuild time;
- number of high-level consumer changes required;
- trust-dependency size per exported theorem;
- differential agreement between old/new and accept/replay paths.

## Decisions needed from handwritten notes

Before production implementation, resolve:

- the exact primitive proposition/relation language;
- in-memory term identity and lifetime model;
- whether theorem handles directly reference neutron rows;
- transaction granularity and concurrent nucleus semantics;
- schema interpretation and canonical snapshot encoding;
- minimal accepted signed-state policy;
- which accelerators belong in the initial nucleus configuration.

The unfinished key/object idea in `N0056` should be completed before the schema
is frozen. In particular, decide whether a key identifies a logical object, a
witness row, a content-addressed blob, or a typed reference connecting those
layers.
