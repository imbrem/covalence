+++
id = "N0053"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:gpt-5.6-sol"
at = "2026-07-20T00:00:00+01:00"
source = "neel-meeting-synthesis"
agent = "gpt-5.6-sol"
harness = "codex"
+++

# Neel meeting: current vision and concrete proposals

This note extracts the actionable design from
[`N0049`](../../../chats/neel_meeting_1.md). The meeting is the newest statement
of intent. Older design notes are prior art, not constraints where they conflict
with this synthesis.

## One-sentence direction

Covalence should be a small relational **substrate** for persistent proof and
computation, surrounded by many narrow, overlapping semantic frontends whose
translations are checked and compared inside the prover.

## The nucleus

The complete kernel state machine is the **nucleus**. Its two cooperating parts
are:

- the **proton**: in-memory terms, theorem values, and checked inference;
- the **neutron**: an in-memory SQLite database containing the relational and
  persistable portion of kernel state.

Neither a database row nor a query result mints a fact. A row is state, input,
or replay evidence. Only a checked nucleus transition can construct theorem
authority. The proton and neutron may be deeply redesigned together; the
stable target is the higher-level capability API, not today's representation.

A database file is a serialization of neutron state. Under an explicit signer
policy, a signed database can be accepted as a trusted serialized kernel state.
Without that trust decision, a database—even one carrying signatures—is an
untrusted candidate state whose relevant transitions must be replayed. Trust is
therefore attached to a state and policy, not inferred from the mere presence
of rows or signatures.

## Semantic atlases

Do not require one universal frontend for a language. Build small interpreters
for honest subsets or approximations, each lowering to shared relations and
theories. Their overlaps form an atlas:

- K, SpecTec, Ott subsets, Lisp, ACL2, and future language tools can express
  overlapping operational rules;
- different implementations may optimize different patches;
- unsupported input must produce an honest error or stated approximation;
- agreement on overlaps is proved as **consilience**, not assumed by sharing
  implementation code;
- a frontend may itself be specified in a frontend, providing another checked
  comparison route.

This turns cheap generated code into many small, auditable compilers rather
than a few monoliths. The important artifact is a checked lowering or relation,
not confidence in the code generator.

## AI as a proof-oriented compiler

The desired authoring level resembles mathematical Haskell: definitions and
specifications are written at high abstraction, then agents and deterministic
tools lower them and discharge routine inductions or compiler-correctness
obligations. Generated programs may become decision procedures, but their
authority comes from checked relationships to their specifications.

Serious dogfooding should follow stable APIs. During API discovery, fast
experimentation is allowed; the later clean-main pass should migrate modules
one at a time with audit-quality statements and proofs.

## Thin waists

The initial interoperable waists are:

- relations and a small relational algebra;
- raw bytes for data and content addressing;
- S-expressions and Lisp for computation and linked structures;
- WASM for portable executable modules;
- SQLite for relational kernel state, persistence, querying, and exchange;
- HOL-omega above the substrate for ordinary mathematical specification.

The substrate itself is relational in a stronger sense than this list first
suggested: sets have logical element types and stored witness types; relations
are projectable sets; `MThm` certifies membership using a witness; and SQLite
tables are one realization of those witnesses. This interface, rather than a
fixed theorem-record schema, is the prospective thin waist.

The maintainer's follow-up design [`N005H`](../../plans/covalence_substrate_design.md)
makes this concrete: expressions are indexed by the schema needed to interpret
their columns, tables denote predicates on rows, and positive, existential, and
negative table claims require different evidence. `DEF` and `USE` govern
identity-preserving mutation, not merely serialization layout.

Higher formats are identified by a decoder/interpreter plus bytes. Higher
content-addressed objects lower to hashed blobs and interpretations rather than
adding special object kinds to the trusted floor.

## Content and identity

The primitive observation is a finite relation such as
`seen(hash_algorithm, key, hash, blob)`: the hashes actually computed in a
kernel state. Collision freedom and conformance to a hash specification are
explicit assumptions or proved properties of a particular finite state.
Optional acyclicity strengthens this into Merkle-style reasoning.

The same pattern covers legacy hash spaces and signatures. For example, a Git
SHA-1 state can be checked and related to a stronger digest map rather than
globally trusting SHA-1. Higher-level term or theorem addressing must lower to
blob addressing plus an interpreter.

## Execution as a relation

Execution should be recorded relationally, including state where necessary:

```text
executes(executor, program, input, start_state, output, end_state)
```

The executor might be wasmi, wasmtime, V8, hardware, QEMU, a container, or a
remote attested service. Rows record claimed or observed executions; checked
nucleus transitions decide how those observations support a theorem. SQL can
compose traces, select retained checkpoints, or discard execution details after
deriving a smaller theorem state.

## Existing-code verification

C should not be assigned one fictional semantics. Treat C, compiler IRs, and
binaries as a lattice of partial semantic atlases. Useful goals are bounded:

- prove absence of a chosen class of undefined behavior;
- extract a deterministic first-order functional specification;
- relate selected source subsets, MLIR/SSA, and actual binaries;
- use old source as a scaffold for recovering a durable specification;
- prefer verified generation for new low-level code.

SQLite is an especially valuable long-range case: it is both strategically
useful to validate and the proposed persistence engine. This is not a Phase-1
dependency of the substrate rewrite.

## Accelerator discipline

The unaccelerated system must be sufficient to state and check the semantics of
accelerators. Otherwise an erroneous accelerator can certify itself. Optional,
independently auditable accelerators should include bytes first, then natural
and integer arithmetic, fixed-width bitvectors, strings/Unicode, and eventually
floating point. Fixed-width bitvectors must be first-class rather than a thin
Nat wrapper.

## Near-term product sequence

1. Make the existing SMT and Lisp paths convincing demonstrations.
2. Specify and prototype the SQLite-backed nucleus and primitive blob identity.
3. Connect portable WASM modules through the execution relation.
4. Stabilize high-level APIs against both the old and new substrate backends.
5. Begin an SSA/compiler toolchain using small atlas frontends.

## Comparison with the previous design corpus

### Retained and sharpened

- The small trusted core, explicit assumptions, and accelerator discipline.
- Relations as a narrow waist and HOL-omega as the main mathematical layer.
- Content addressing, WASM execution, signed exchange, and federation.
- Trait-based high-level APIs with multiple implementations and proofs across
  them.
- Metamath, SMT/SAT, Lisp/ACL2, and SpecTec/K/WASM as complementary stress
  tests rather than isolated demos.
- The eventual audited clean-main migration.

### Replaced

- “Content addressing as a kernel extension” becomes finite blob observations
  in neutron state plus interpretations in higher layers.
- “Store/executor observation mints a relational theorem” becomes “the row is
  state or evidence; a checked nucleus transition constructs authority.”
- A primarily in-memory closed-world base becomes the proton/neutron nucleus,
  with SQLite participating in every running kernel state.
- Narrative project snapshots become a short portfolio DAG plus queryable
  TODO/task state.
- One canonical semantics per source language becomes an atlas of explicit
  partial semantics with proved overlap.

### Demoted to experiments

- Exact current `covalence-pure`, closed-world-language, and `Rel::execute`
  representations.
- Current hash-consing, VCS object, observer, and backend interfaces.
- The existing crate split below the stable high-level APIs.
- CN as an end-state verification language; it remains possible atlas input.

### Added or newly central

- SQLite as the live relational half of a kernel, not merely persistence.
- Serialized and signed whole-kernel state with distinct accept and replay
  modes.
- Stateful execution observations that can describe WASM, containers,
  hardware, and remote attestation uniformly.
- SSA/MLIR and binary verification as the preferred bridge from legacy C.
- Fixed-width bitvectors as substrate-grade data rather than a Nat wrapper.
- Typed column roles (`DEF`, `USE`, `NAME`, data, metadata), row-field
  projections, and scoped completeness.
- Unconditional lifting of substrate relations to uninterpreted HOL relations,
  with their mathematical meaning supplied separately.
- A split between execution/grounding trust and HOL semantic assumptions.
- Multiple TCB groundings and multiple substrate implementations over the same
  relational API.
- A deliberately small trusted SQL algebra for large-scale kernel reasoning,
  state merge, candidate filtering/promotion, and subdatabase exchange.
- Proton structures and future e-graphs as optimized physical forms of the
  canonical neutron relations rather than independent semantic authorities.

## Questions intentionally left open

- Exact proton/neutron ownership and transaction boundary.
- Minimal relational logic implemented by the substrate.
- Which signed-state policies are primitive versus ordinary HOL theories.
- Canonical database schema and migration/versioning rules.
- Representation of in-memory terms and references into neutron state.
- Whether theorem values are serialized directly or reconstructed from a
  compact derivation/state certificate.
- The precise high-level API that both the current and rewritten substrate
  must implement.
