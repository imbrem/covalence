# Prover MVP Plan

Companion to [`prover-architecture.md`](./prover-architecture.md). This
document is **tactical**: it lists the phases, deliverables, and acceptance
tests to get from the current state of the tree to the first end-to-end
demo of the new prover.

The architecture doc says *what we're building*. This doc says *what we do
each step of the way*.

---

## MVP Demo Target

A REPL session that:

1. Declares a concept `oracle_says : blob → blob → bool`, keeping the
   `ConceptHandle` in Rust.
2. Compiles, stores, and loads a WASM component that calls a host import
   `cov:hol/observe` with `(input_blob, output_blob)`, marking
   `oracle_says(input_blob, output_blob) = true`.
3. Adds a user trust assumption to the root Context:
   `∀ i o. oracle_says(i, o) = true ⇒ P(i, o)` for some user-supplied
   predicate `P`.
4. Derives the Thm `P(input_blob, output_blob)` via MP.
5. Serializes the Thm to a blob in the content-addressed store and prints
   its hash.

The session is reachable from `cov repl` (Forsp postfix syntax).

Explicitly **out of MVP scope**: the WASM-spec axiom relating `oracle_says`
to actual WASM execution semantics. We assume the user adds the trust
assumption directly. Proving the spec axiom is later work.

---

## Phases

Each phase produces a working tree that builds and tests cleanly. Land
phases as separate commits or short-lived branches; each phase has
acceptance tests before merge.

### Phase 1 — Arena + UF rewrite

**Scope.** Replace the current arena (HOL Light style: separate `types`/
`terms`/`thms` Vecs, `aconv` over structure) with the new design:

- One `Arena` containing a flat `entries: Vec<{ canonical: TermId,
  definition: TermDef }>`.
- Union-find write ops: `union(a, b)` and `rewrite(t, t')`.
- Congruence propagation on union.
- Frozen-vs-mutable distinction; `Arc<Arena>` for frozen.
- Foreign-import tagged handles `TermRef = Local | Foreign(arena_id,
  term_id)`.

Still uses HOL Light's named term language. Soundness fixes from "more work
on prover" carry forward.

**Deliverables.**
- `covalence-hol/src/arena.rs` rewritten.
- New traits in `traits.rs` reflecting `&mut Thm` rule signatures (or
  whatever ends up natural).
- The current 31 tests pass against the new structure (port them).

**Acceptance.**
- `cargo test -p covalence-hol` green.
- A new property test: random sequences of `union(...)` calls preserve
  the invariant that two terms have the same canonical id iff they
  should.

### Phase 2 — Locally-nameless terms + closed/open

**Scope.** Switch the term language from `Var(NameId, TypeId)` (HOL
Light) to `Bound(u32) | Free(NameId, TypeId)`. Tag each term entry with
"closed?" computed on insertion. The UF refuses non-congruence unions of
open terms. Update all inference rules to the new term shape.

**Deliverables.**
- New `TermDef` variants.
- `Thm::abs` introduces a binder over a `Free` (locally-nameless ABS).
- `Thm::beta` reduces `(λ. body) arg` via index substitution.
- Open-term rejection on `union()` with a clear error.

**Acceptance.**
- Port the HOL Light primitive-rules test set; all green.
- Targeted tests: attempting to union two distinct free variables
  fails; congruence unions on open terms succeed.

### Phase 3 — Prop / Thm / Context

**Scope.** Introduce the data layer above the arena.

- `Prop = { arena, assumptions: Vec<Arc<Prop>> }`.
- `Thm` as a compile-time-tagged Prop (newtype or phantom — pick at
  implementation time).
- `Context = { assumptions: Vec<Arc<Prop>>, parent: Option<Arc<Context>> }`.
- `Thm` carries `Arc<Context>`.
- Two new inference rules: `add_assumption` and `not_from_false`.

**Deliverables.**
- `covalence-hol/src/prop.rs`, `thm.rs`, `context.rs`.
- Existing rules ported to take `&mut Thm`; some take `Thm` by value.
- The kernel's old `axioms: Vec<ThmId>` field is removed — axioms are
  just Props in the root Context now.

**Acceptance.**
- New tests:
  - Push a context, prove a Thm under it, pop the context — the Thm's
    referenced Context remains valid (Arc-shared).
  - Adding an assumption and then later deriving the conclusion's
    discharge form is sound.
  - Round-trip a Thm through `Arc<Thm>` and use it nonlinearly.

### Phase 4 — `bits` primitive type

**Scope.** Replace the inherited `ind` (if any survives) with `bits`. The
arena gains a fast-path representation for short bit strings; the logic
sees `nil`/`cons`/`len`/`eq` as canonical constructors. Define `blob` in
a standard-library Prop on top.

**Deliverables.**
- `bits` constants registered in the kernel's built-in constant table.
- Arena: a `BitsLiteral([u8; N])` term form for short literals,
  transparent to the rest of the kernel.
- A small standard-library Prop file declaring `blob : *` (alias for
  `bits`) and its operations.

**Acceptance.**
- Bit-string equality between literal forms and `cons`-built forms
  unifies via congruence.
- Round-trip: parse a `bits` literal, build via `cons`, prove they're
  equal.

### Phase 5 — Concepts API (Rust-only)

**Scope.** Add the concept system.

- `Kernel::declare_concept(name, kind) -> ConceptHandle`.
- `ConceptHandle::add_theory_axiom(prop)` — kernel validates conclusion
  shape `… ⇒ c[α](…) = true`.
- On accepted axiom: kernel adds it to the relevant Context **and**
  immediately unions any concrete `c[α](t₁,…,tₙ)` in the conclusion with
  `true` in the UF.
- No `enter()`, no `attest_all()`. Those are untrusted-library territory.

**Deliverables.**
- `covalence-hol/src/concept.rs`.
- Conclusion-shape checker.
- Documentation block in the doc.

**Acceptance.**
- Declare a concept, observe a tuple, prove a Thm using the observation
  via a trust assumption.
- Owner-axiom shape check rejects `c(x) = false` and accepts the legal
  shapes.

### Phase 6 — Serialization

**Scope.** Define a flat byte format for `Prop`. Round-trip
`serialize -> deserialize -> Prop<Untrusted>`. Untrusted Prop is
embeddable as a `bool` term but is not a Thm.

**Deliverables.**
- `covalence-hol/src/serial.rs`.
- A versioned binary format (header + tables, building on
  `covalence-object`'s `Table` machinery).
- `deserialize(bytes) -> Result<Prop<Untrusted>, Error>`.

**Acceptance.**
- Round-trip every Thm produced by the Phase 5 tests; bytes match
  across multiple serializations of the same logical content.
- Tampering with the bytes either fails deserialization or yields a
  Prop that the kernel will not accept as a Thm.

### Phase 7 — WASM bridge

**Scope.** A new host import interface in `covalence-kernel/src/engine.rs`:

```
package cov:hol;
interface observe {
  declare-concept: func(name: string, arity: u32) -> concept-handle;
  observe: func(handle: borrow<concept-handle>, args: list<term>);
  // term resource etc.
}
```

The Rust caller setting up the wasmtime store decides which concepts the
hosted component has handles to. The component sees only the handles it
was granted.

Existing `cov:hol/kernel` HOL bridge (the resource API for
type/term/thm) carries over but is rewritten against the new arena
trait.

**Deliverables.**
- `cov:hol/observe` interface in `engine.rs`.
- Existing HOL bridge port.
- An example WASM component (in a test fixture) that takes two blob
  imports, calls observe with them, and exits.

**Acceptance.**
- Engine test: run the example component; the observation appears in
  the host kernel's Context.
- Engine test: a component without a handle to a concept cannot observe
  it (the host import returns an error / the linker refuses to wire it).

### Phase 8 — REPL bindings + MVP demo

**Scope.** Add Forsp primitives to the REPL for the new operations:

- `<name> declare-concept`
- `<handle> <arg1> <arg2> ... attest` (variadic over the stack)
- `<assumption-prop> add-context-assumption`
- `<thm> serialize` → blob
- `<blob> deserialize` → untrusted prop

Wire them into `covalence-repl`.

**Deliverables.**
- REPL primitives.
- A script (or integration test) that runs the MVP demo end-to-end.

**Acceptance.**
- The MVP demo described at the top of this doc runs from the Forsp
  REPL and produces the expected serialized Thm hash.
- The test verifies the demo's output is stable across runs.

---

## Out of Scope for MVP

The following are explicitly *not* MVP work, even though they're called
out in the architecture doc. They land in follow-up phases once MVP is
demonstrated.

- **WASM spec axiom.** Tying `executed(w, i, o)` to actual WASM
  operational semantics. The MVP user supplies the trust assumption
  directly.
- **Signed import.** `isValidSignature` as a concept, cross-process
  Thm import. Uses the same machinery as the WASM bridge but adds
  EdDSA wiring.
- **Goal API.** Untrusted "partially proved Prop" type with a tactic
  language.
- **Sub-capabilities (`enter()`).** Owner can hand out narrower
  ConceptHandles. Untrusted convenience layer.
- **Egraph-style rewriting.** Higher-level rewriting / saturation
  strategies on top of the minimal UF.
- **Object-logic interpretations.** ZF, GT, category-theoretic
  semantics — all post-MVP follow-on.
- **Tactics.** Forsp / external tactic-language support beyond the
  REPL primitives needed to drive the demo.
- **Cogit integration.** Storing Thms in cogit trees with provenance
  metadata.

---

## Crate Impact Summary

| Crate | Phase touch | Nature of change |
|---|---|---|
| `covalence-hol` | 1, 2, 3, 4, 5, 6 | Heavy: arena rewrite, term rewrite, Prop/Thm/Context, bits, concepts, serialization. |
| `covalence-opentheory` | 1, 2, 3 | Port over each kernel-API change. Same generic-over-`HolLightKernel` shape. |
| `covalence-kernel` | 1, 2, 3, 7 | HOL bridge rewrite each time the trait changes; new `cov:hol/observe` in phase 7. |
| `covalence-repl` | 8 | New Forsp primitives. |
| `covalence-wasm` | 7 | If we need new resource types in the runtime. |
| `covalence-serve` | 8 | Web/HTTP exposure of the new REPL commands (probably trivial). |
| `covalence-isabelle` | — | Stays deleted. |
| `covalence-sat`, `covalence-smt`, `covalence-lean`, `covalence-metamath`, `covalence-forsp` | — | Untouched in MVP. Re-evaluated post-MVP for which become standard libraries vs. archived. |
| `MVP_DESIGN.md`, `DESIGN.md` | 8 | At MVP completion, mark superseded by this doc. |

---

## Open Questions

These don't block starting on Phase 1, but should be resolved before the
phase they're listed under.

- **Phase 1.** Does the UF entry's `definition` need a generation
  counter to detect stale views during congruence propagation, or is
  monotonic-rewrite-only enough? Pick when implementing.
- **Phase 2.** Free-var "name" — `NameId` (interned string) or
  `u32` opaque? Probably `NameId` for printing, but the kernel itself
  doesn't care.
- **Phase 3.** Newtype vs phantom-tag for Thm — decide at implementation
  time. Phantom integrates more cleanly with the `Prop<Untrusted>` of
  phase 6.
- **Phase 5.** What's the `ConceptKind` declaration look like? Probably
  `{ arity: u32, type_params: u32 }` — fix when implementing.
- **Phase 7.** Term-as-WASM-resource representation: opaque borrowed
  TermId, or a small wire format the component can introspect? Lean
  toward opaque borrow for MVP.

---

## How to Use This Doc

- Treat phases as the unit of work. Each phase is a self-contained
  PR-sized change with its own acceptance tests.
- Don't skip ahead — the dependencies are real (arena before
  locally-nameless before Prop, etc.).
- When you finish a phase, update [`prover-architecture.md`](./prover-architecture.md)
  if the architecture changed (it shouldn't, much — that doc is the
  spec).
- When you start a new session, read the architecture doc first to
  re-orient, then pick the next phase here.
