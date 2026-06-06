# Path to the Vision

> **STATUS: PROPOSED — working-draft path, not committed.** Sibling to
> the [layered-framework
> proposal](../layered-framework/README.md) (which designs the kernel).
> This doc designs *how we get there* without stalling other in-flight
> work. For the canonical snapshot of what's actually built today, see
> [`where-we-are.md`](../../../where-we-are.md).

The big picture in
[`ARCHITECTURE.md`](../../../../ARCHITECTURE.md) reads as one project
because the philosophy is one ("scoped truths about named artifacts,
no global lies"). Operationally it's at least three: a theorem prover,
a content-addressed VCS, and a federated trust infrastructure. They
share a single substrate — a content-addressed blob store and an
eventual tree store — and they will eventually unify (the VCS becomes
a theory inside the prover). But until that endgame, they should ship
as *two parallel streams over the shared substrate*, not as one giant
serialized plan.

This proposal lays out that path.

---

## Contents

1. [The kill list](#1-the-kill-list)
2. [The shared backbone](#2-the-shared-backbone)
3. [Oracle-everything stratification](#3-oracle-everything-stratification)
4. [`attest` / `decide` as the first oracle](#4-attest--decide-as-the-first-oracle)
5. [The four phases](#5-the-four-phases)
6. [What changes about the layered-framework proposal](#6-what-changes-about-the-layered-framework-proposal)
7. [Open decisions](#7-open-decisions)

---

## 1. The kill list

Precondition for the rest. Everything below assumes these are done.

| Item | Action | Reason |
|---|---|---|
| `covalence-hol`, `covalence-opentheory` | Move to `references/` (or workspace-exclude); pin at known-good commit; drop from CI | They're reference for the eventual port; they're not a forward-development target. The "untrusted APIs driving the main kernel" role lands *after* the framework ships, not before. |
| Application shells (REPL, serve, client, LSP, VSCode, web) | Mark `// LEGACY: bound to superseded API, rewrite after framework MVP` at each crate's `lib.rs`; do not modify | They bind to a kernel API that's being rewritten. Don't migrate now; rebuild against the new API in [Phase 2](#5-the-four-phases). |
| Phase A–H ([`refactor-plan.md`](../../../refactor-plan.md)) | Terminate. Mark in `refactor-plan.md` that further Phase work is sunk cost | The phases are refactoring the kernel that's being rewritten. Phase H (Arena::hash inside kernel) is explicitly *deleted* by the framework — moves to a `TermHasherOracle` outside. |
| Phase P (EProp/EThm) | Terminate at P3. Don't extend. EProp/EThm stay in the legacy kernel for the reference period | The new framework adopts the [facts-not-proofs](../layered-framework/notes/facts-not-proofs.md) discipline as a userspace egraph oracle, not by extending Phase P into the new kernel. |
| `MVP_DESIGN.md` (WASM-component-as-proposition) | Mark superseded; *retain as the seed of the WASM oracle crate* (see §4) | Not legacy — the `attest`/`decide` mechanism is the first instance of the general oracle primitive. The code is reused, the framing changes. |

The Phase 0 deliverable is exactly this table executed. No new
functionality. Cheap; unblocks everything.

---

## 2. The shared backbone

The prover and the VCS converge on **one piece of infrastructure**: a
content-addressed substrate. Today it's split across three crates with
overlapping concerns:

| Crate | Today's role | Backbone role |
|---|---|---|
| [`covalence-store`](../../../../crates/covalence-store) | blob storage trait + memory/SQLite/git backends | the **blob store oracle** surface — `BlobStoreAuthority` owns `has_bytes(name, payload_hash)` + `in_store(s, n)` + `subset(s1, s2)` |
| [`covalence-object`](../../../../crates/covalence-object) | `Dir`/`Table` serialization + git tree conversion | the **tree store oracle** surface — `TreeStoreAuthority` owns `tree_entry(node, name, child)` + the merge-certificate schema |
| [`covalence-git`](../../../../crates/covalence-git) | git-compatible objects + LFS | a *backend implementation* of the blob store oracle for the Git on-disk format |

Cleaning this up is a single coherent move: factor the current
trait-and-backend grab-bag into **one oracle-shaped API**
(`TreeStoreAuthority` + `BlobStoreAuthority`) with the existing
backends underneath. The trait surfaces are what the framework's
`observe()` calls bottom out into; the backends stay where they are.

**No new crate is strictly required** for V1 — the work fits inside
`covalence-store` + `covalence-object`. A `covalence-tree` extraction
becomes worth it only when the API has stabilized enough to live
independently.

The [TCB-store list in
`AGENTS.md`](../../../../AGENTS.md) currently includes the
read/write primitive and the merge-certificate checker. This proposal
**narrows** that further (see §3): those become oracle observations
under a store authority's relations, with collision-freedom and
merge-correctness as user-supplied meaning-axioms.

---

## 3. Oracle-everything stratification

The strongest version of the LCF discipline: **only the framework is
in the TCB**. Everything else — hash functions, signature schemes,
executors, verifiable reads, store membership, merge-certificate
checking, blob backends, tree backends, FUSE projection — is an
*oracle*. The framework's only trust primitives are observations and
meaning-axioms; soundness lives in the user's discipline about which
meaning-axioms to discharge.

This is *stronger* than [`02-framework.md`
§5](../layered-framework/02-framework.md) (which makes Stores a
framework primitive) and stronger than [`AGENTS.md`'s TCB
list](../../../../AGENTS.md) (which puts the store read/write
primitive and merge-certificate checker inside). The argument for
pushing further:

- **Extensibility without TCB swell.** Adding SHA-1, BLAKE3, IPFS,
  Arweave, Git-LFS as new "stores" is adding *oracle authorities*, not
  new TCB code. We can support N cryptographic schemes; we audit one.
- **Honest scope.** "No collisions in this store" is *already* an
  assumption the framework can't compute; making the store itself an
  oracle forces it to be a written-down meaning-axiom rather than a
  trusted Rust function. The honesty argument from
  [`04-store.md` §3](../layered-framework/04-store.md#3-why-stores-are-framework-primitive)
  works just as well — *better*, actually — when the store is an
  authority whose `in_store` relation requires meaning-axioms to use.
- **Symmetry.** Every "trusted source" (hash function, executor,
  store backend, signature verifier) has the same shape: an
  authority, a set of opaque relations, a meaning-axiom that the user
  is responsible for. One stratification, many instances.

The trade-off — more upfront work to describe each store oracle's
relations explicitly — is real and worth taking. It's the same
trade-off the framework itself makes (no baked-in HOL connectives;
HOL is a theory you write down). It compounds the same way: every
oracle you add is described in *its* documentation, and the audit
surface stays flat.

### What ends up in the TCB under this stratification

| Component | Status under this proposal |
|---|---|
| LF rules (assume, ⟹-intro/elim, ⋀-intro/elim, refl/sym/trans/cong, β/η) | **TCB** |
| `Authority` + `observe` + safe-axiom check | **TCB** |
| `define` | **TCB** |
| Term/type representation; α-equivalence; substitution; closed-ness | **TCB** (meta-trust, per `02-framework.md`) |
| Hash functions (BLAKE3, SHA-256, …) | oracle |
| Signature schemes (Ed25519, …) | oracle |
| Executors (WASM, x86, native) | oracle |
| Blob store reads + writes + verifiable-read witnesses | **oracle** (`BlobStoreAuthority`) |
| Store membership + subset | **oracle** (lives in the same store authority's relations) |
| Tree store reads + writes + merge certificate | **oracle** (`TreeStoreAuthority`) |
| Mount machinery | oracle (it's just a Horn-clause shape over the store authorities) |
| Format-validity | oracle |
| FUSE projection | oracle |

The TCB list collapses to *just the framework crate*. ~700–800 LoC, as
in [`02-framework.md`](../layered-framework/02-framework.md) — but
genuinely smaller in scope, because Stores leave.

---

## 4. `attest` / `decide` as the first oracle

The currently-superseded `MVP_DESIGN.md`'s WASM-component-as-proposition
model — `attest()` host import, `decide()` returning Sat/Unsat — is the
**first concrete instance of the general oracle primitive**. The framing
changes, the code mostly survives.

| Old framing | New framing |
|---|---|
| Kernel host import `attest()` | `WASMExecutorAuthority.eval(component_hash, input_hash, output_hash)` observation |
| Decision procedure runs a component and returns Sat/Unsat | Userspace `decide(prop)` strategy: pick a decision procedure (a WASM component), drive it to attest, discharge via meaning-axiom, produce a Thm |
| `decide` returns a three-valued `Decision` | `decide` returns either a Thm (Sat → Thm prop, Unsat → Thm ¬prop) or "I don't know" (no Thm) |
| Trust the kernel's host bridge to wire attest correctly | Trust the meaning-axiom you wrote for the WASM executor authority |

This integrates naturally with the [oracle-everything
stratification](#3-oracle-everything-stratification): a WASM oracle is
an authority that owns an `eval` relation; a store oracle is an
authority that owns `in_store` / `subset` / `has_bytes` relations.
Same shape, different relations.

**The existing kernel's attest/decide implementation becomes the seed
for the `covalence-oracle-wasm` crate.** It survives the rewrite — the
Wasmtime bridge, the host-import plumbing, the component loading —
just under new ownership: in an oracle crate rather than in the kernel
crate.

This is why "freezing the shells" in §1 doesn't mean "deleting the
attest infrastructure." The shells freeze; the attest mechanism
relocates.

---

## 5. The four phases

### Phase 0 — Clear the desk

Execute the §1 kill list. ~1 week. Output: a workspace where one
forward kernel is being built (the framework, not yet existing) and
nothing else is competing for attention.

### Phase 1 — Harden the shared backbone

Both streams blocked until this is done.

- **B1.** Settle the `BlobStoreAuthority` trait surface: opaque
  relations `has_bytes(name, payload_hash)`, `in_store(store_id,
  name)`, `subset(s1, s2)`. Move the verifiable-read logic
  (Merkle-witness checking) into the *implementations* of this trait,
  not into the framework. Existing backends (memory, SQLite, git)
  implement the trait.
- **B2.** Settle the `TreeStoreAuthority` trait surface: opaque
  relations `tree_entry(node, name, child)`, merge-certificate shape.
  Reuse `covalence-object`'s `Dir`/`Table` machinery as the
  implementation; the trait wraps it.
- **B3.** Stabilize the `Name256` opaque carrier (per
  [`01-conventions.md`](../layered-framework/01-conventions.md)) and
  add the bridge from `covalence-hash`'s typed hashes to `Name256`.
- **B4.** Acceptance test: write a blob, read it back with a tampered
  byte, the (now oracle-implemented) verifiable-read fails. Same
  test as before; different layer.

No new crates strictly required — fits inside `covalence-store` +
`covalence-object` + a small bridge. A future `covalence-tree`
extraction is optional once the API is stable.

### Phase 2 — First end-to-end loops, in parallel

Streams diverge here; they share the substrate from Phase 1 and
otherwise run independently.

**VCS stream (mostly continuing existing momentum):**

- **V1.** `cov cog commit` over a working tree, producing a tree-store
  node via `TreeStoreAuthority`.
- **V2.** `covalence-fuse` reads via the same authority; existing
  scaffold (commits `b66c655` + `3f9207a`) is in the right shape, just
  rewires its backend.
- **V3.** Round-trip: working tree → commit → mount → read. Smoke
  test as a single binary integration test.

**Prover stream (new):**

- **P1.** Scaffold `covalence-framework`. LF only: terms, types,
  sequents, the eight LF rules, β/η, `define`. ~400 LoC. Single dep
  on `covalence-rand`. No Authority/Store/observe yet.
- **P2.** Add `Authority` + `observe` + safe-axiom check. ~150 LoC.
- **P3.** Add `meaning_axiom` helpers + the conservative-extension
  check. ~100 LoC.
- **P4.** Build one *trivial* oracle (a Rust function that calls
  `framework.observe()`). Demo: declare an authority, make one
  observation, discharge via meaning-axiom, derive a 3-line theorem,
  print it. **No WASM oracle yet** — that's the next item but not
  blocking this milestone.
- **P5.** Build `covalence-oracle-wasm` by porting the existing
  `attest()`/`decide()` machinery from `covalence-kernel` and
  `covalence-shell` (per §4). The WASM oracle becomes the first
  non-trivial oracle. End-to-end test: a WASM component asserts a
  fact; the kernel derives a Thm conditional on the meaning-axiom.

End of Phase 2: VCS round-trips a tree; framework derives a theorem in
isolation; WASM oracle bridges the executor plane. Neither stream
*needs* the other yet — but both ride the same substrate.

### Phase 3 — Stitch at the substrate

Now that the substrate is exercised by both streams, the join becomes
natural.

- **S1.** Wire `BlobStoreAuthority`'s `in_store` and `has_bytes`
  observations into a Thm that asserts "blob `n` is recorded in store
  `s` and its content hashes to `h`." This is the bridge spec — a few
  lines of HOL on top of one oracle observation.
- **S2.** Serialize a Thm into a blob via the substrate; reload it as
  `Prop<Untrusted>`. Round-trip test.
- **S3.** First joint demo: commit a tree via VCS; derive a framework
  Thm about the committed tree's contents (using the
  `BlobStoreAuthority` + `TreeStoreAuthority` observations + a small
  user meaning-axiom set); serialize the Thm into the same tree.

End of Phase 3: the substrate is mutually exercised. The Git-repo
theorem demo from [`04-store.md`
§9](../layered-framework/04-store.md#9-worked-example-git-repo-demo)
becomes a script combining VCS operations with framework Thms; no new
infrastructure required.

### Phase 4 — Reunification (long tail; not on MVP critical path)

Define the VCS operations as a theory **inside** the framework. Prove
that the trusted Rust VCS implementation matches the theory (a single
big embedding, derived once). The VCS becomes "this theory + its
extracted runtime." Mount-as-implication
([`ARCHITECTURE.md`](../../../../ARCHITECTURE.md) §10.2) lands
naturally as a Horn-clause shape over store authorities.

This is the "the VCS will cease to be a separate thing" endgame from
the planning conversation. It's contingent on Phases 1–3 being stable,
not a prerequisite for any of them.

---

## 6. What changes about the layered-framework proposal

The [layered-framework
proposal](../layered-framework/README.md) is the canonical kernel
design; this proposal **adopts it** with two refinements:

1. **Stores are oracles, not framework primitives.**
   [`02-framework.md` §5](../layered-framework/02-framework.md) and the
   whole of
   [`04-store.md`](../layered-framework/04-store.md) describe Stores
   as framework primitives. Under §3 of this proposal, Stores leave
   the framework — they become a `BlobStoreAuthority` /
   `TreeStoreAuthority` shape, with `in_store` / `subset` /
   `has_bytes` as oracle relations and collision-freedom /
   downward-closure as user-supplied meaning-axioms. The framework
   shrinks accordingly. The worked examples
   ([`04-store.md` §8 SHAttered](../layered-framework/04-store.md#8-worked-example-shattered),
   [§9 Git-repo](../layered-framework/04-store.md#9-worked-example-git-repo-demo))
   still work; they're re-expressed in terms of oracle observations
   rather than framework primitives.

2. **`attest` / `decide` are not legacy.** The
   [`prover-mvp-plan.md`](../../../prover-mvp-plan.md) "out of scope"
   list excludes `attest()` and the decide pipeline as legacy. Under §4
   of this proposal, they're the *first concrete oracle* — the WASM
   executor's observation shape — and the existing kernel
   implementation seeds `covalence-oracle-wasm`. The shells freeze;
   the attest code relocates and ships in Phase 2 / P5.

Neither refinement changes the overall layered shape. They sharpen
what counts as a framework primitive (smaller) and clarify what
happens to the not-quite-legacy attest/decide infrastructure (it
becomes the first oracle, not deleted code).

---

## 7. Open decisions

These are decidable now and should be before Phase 1 starts.

- **Crate naming for the framework.** `covalence-framework` (per
  layered-framework proposal) vs `covalence-kernel` reused for the
  new kernel. Recommend: reuse `covalence-kernel`, with the legacy
  contents moved to `references/`. The name "kernel" is what the
  ecosystem expects; "framework" is internal vocabulary.
- **Whether `covalence-shell` continues.** Two options: (a) shell
  stays as the WASM-bridge home (becomes `covalence-oracle-wasm`'s
  internal); (b) shell goes away, oracle crates each own their own
  bridges. Recommend (b) — one crate per oracle is the cleaner
  stratification.
- **Whether to extract `covalence-tree` now or after Phase 1
  settles.** Recommend after — the trait surface needs to live in
  `covalence-store` / `covalence-object` long enough to know what
  the right factoring is.
- **What relations the blob store oracle owns.** Minimum proposal:
  `has_bytes(name, payload_hash)`, `in_store(store_id, name)`,
  `subset(s1, s2)`. Add `not_collides(s, h)` if collision-freedom
  needs to be observable rather than just assumable. Decide before B1.
- **What relations the tree store oracle owns.** Minimum proposal:
  `tree_entry(node, name, child)`, plus the merge-certificate shape
  as a single multi-arg observation. Decide before B2.

Until decided, the rest of this document references them generically;
fix the names once chosen.

---

## 8. Cross-references

- [`../layered-framework/README.md`](../layered-framework/README.md)
  — the kernel layer this path targets.
- [`../layered-framework/02-framework.md`](../layered-framework/02-framework.md)
  — the kernel blueprint; this proposal removes Stores from §5 and
  takes "outside the TCB" further than §6 does.
- [`../layered-framework/04-store.md`](../layered-framework/04-store.md)
  — the Store worked examples; this proposal re-expresses them as
  oracle observations.
- [`../layered-framework/notes/facts-not-proofs.md`](../layered-framework/notes/facts-not-proofs.md)
  — the discipline the framework adopts; supersedes Phase P as the
  intended egraph integration.
- [`../../../where-we-are.md`](../../../where-we-are.md) — current
  snapshot; this proposal supersedes the "currently-favored
  direction" section by adding the path.
- [`../../../refactor-plan.md`](../../../refactor-plan.md) — Phases
  A–H and P are terminated by §1 of this proposal.
- [`../../../prover-mvp-plan.md`](../../../prover-mvp-plan.md) —
  superseded by Phase 2 of this proposal.
- [`../../../../ARCHITECTURE.md`](../../../../ARCHITECTURE.md) §11
  (storage) and §12 (formats) — vocabulary this proposal uses.
- [`../../../../AGENTS.md`](../../../../AGENTS.md) — TCB list; this
  proposal narrows it further (verifiable reads and merge
  certificates move out).
- [`../../../../MVP_DESIGN.md`](../../../../MVP_DESIGN.md) — not
  legacy under this proposal; it's the seed of the WASM oracle (§4).
