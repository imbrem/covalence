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

1. Declares an **anonymous** concept (no name yet — naming is
   post-MVP), call it `H`, of kind `bits → bits → bool`. Conceptually
   "the oracle has been observed to map this input to this output".
   The `ConceptHandle` stays in Rust.
2. Compiles, stores, and loads a WASM component that calls a host
   import `cov:hol/observe` with `(input_blob, output_blob)`, marking
   the corresponding `c[bits, bits](input_blob, output_blob) = true`
   theory axiom on `H`.
3. Adds a user trust assumption to the root Context:
   `∀ i o. H(i, o) = true ⇒ P(i, o)` for some user-supplied
   predicate `P`.
4. Derives the Thm `P(input_blob, output_blob)` via MP.
5. Serialises the Thm to a blob in the content-addressed store and
   prints its hash.

The session is reachable from `cov repl` (Forsp postfix syntax).

Explicitly **out of MVP scope**: the WASM-spec axiom relating
observations to actual WASM execution semantics; the naming protocol
for serialisable concepts; content-addressed type-defs and functions.
We assume the user adds the trust assumption directly. Proving the
spec axiom and naming are later work.

---

## Phases

Each phase produces a working tree that builds and tests cleanly. Land
phases as separate commits or short-lived branches; each phase has
acceptance tests before merge.

### Phase 1 — Arena + namespaces + builtins

**Scope.** Replace the current arena with the new design end-to-end:

- Separate ID namespaces (`BuiltinId` baked into the enum;
  `TypeName`, `ConstName`, `VarName`, `ConceptId` each in its own
  table).
- Immutable `TypeDef` and `TermDef` enums with builtin variants
  (`Bool`, `Bits`, `Fun`, `Eq`, `True`, `False`, `BitsLit`,
  `BitsHashed`). User constants and type constructors are the only
  paths through the user-side tables.
- Arena-aware canonical IDs: each `UfEntry` holds
  `canonical: (ArenaId, TermId)` and a `closed: bool` flag.
- `TermRef = Local(TermId) | Foreign(ArenaId, TermId)` for cross-arena
  child links inside `Comb`/`Abs`.
- Frozen-vs-mutable distinction; `Arc<Arena>` for frozen.
- Append-only immutable structural side; UF state mutates separately.

No `definition: TermDef` field on UF entries — the structural form is
fixed at insertion. "Rewriting" no longer exists as a primitive; it's
implicit in the UF.

**Deliverables.**
- `covalence-hol/src/arena.rs` rewritten.
- New traits in `traits.rs` reflecting the new structural shape.
- Existing tests ported.

**Acceptance.**
- `cargo test -p covalence-hol` green.
- Property test: random sequences of `union(...)` calls preserve the
  invariant that two terms are level-0-equal iff they should be.
- Diamond-import test: arenas D, B, C, A as in the architecture doc
  §4.1; verify that shared-D subterms regain UF identity while
  B-originated vs C-originated terms remain structurally distinct
  unless explicitly unioned.

### Phase 2 — Locally-nameless terms + closed/open

**Scope.** Switch the term language from `Var(NameId, TypeId)` (HOL
Light) to `Bound(u32) | Free(VarName, TypeId)`. Tag each term entry
with `closed`, computed on insertion. The UF refuses non-congruence
unions of open terms. Update all inference rules to the new term
shape.

**Deliverables.**
- New `TermDef` variants matching §3.1 of the architecture doc.
- `Thm::abs` introduces a binder over a `Free` (locally-nameless ABS).
- `Thm::beta` reduces `(λ. body) arg` via index substitution.
- Open-term rejection on `union()` with a clear error; congruence
  union on open terms succeeds.

**Acceptance.**
- Port the HOL Light primitive-rules test set; all green.
- Targeted tests: attempting to union two distinct free variables
  fails; congruence unions on open terms via
  `union_if_congruent_step` succeed.

### Phase 3 — Equality predicates and `union_if_congruent_step`

**Scope.** Add the equality-at-level family and the explicit
congruence step.

- `eq_at_level(a, b, k)` for `k ∈ {0, 1, …, ∞}`, transparently
  following foreign-arena pointers.
- `union_if_congruent_step(a, b)` — if `a` and `b` decompose to the
  same shape and corresponding children are `eq_at_level(_, _, 0)`,
  union them; otherwise return failure (no error).
- Remove any leftover "automatic congruence" code from Phase 1's
  union path.

**Deliverables.**
- `covalence-hol/src/uf.rs` (or wherever these live) with the new
  builtins.
- Rewrite of `MK_COMB` to be a thin wrapper around
  `union_if_congruent_step`.

**Acceptance.**
- The level-0 / level-1 / level-∞ semantics each have direct tests.
- A failing congruence-step test (children not yet equal) returns
  failure cleanly without polluting the UF.
- An accepted congruence-step test produces a new union and updates
  level-0 equality lookups accordingly.

### Phase 4 — Prop / Thm / Context

**Scope.** Introduce the data layer above the arena.

- `Prop = { arena, assumptions: Vec<Arc<Prop>> }`.
- `Thm` as a compile-time-tagged Prop (newtype or phantom — pick at
  implementation time; lean toward phantom for §8 phantom-pair
  with `Prop<Untrusted>`).
- `Context = { assumptions: Vec<Arc<Prop>>, parent: Option<Arc<Context>> }`.
- `Thm` carries `Arc<Context>`.
- Two new inference rules: `add_assumption` and `not_from_false`.
- Kernel's old `axioms: Vec<ThmId>` removed; "axioms" are Props in
  the root Context.

**Deliverables.**
- `covalence-hol/src/prop.rs`, `thm.rs`, `context.rs`.
- Existing rules ported.

**Acceptance.**
- Push a context, prove a Thm under it, pop the context — the Thm's
  Context remains valid via Arc.
- `add_assumption` and `not_from_false` round-trip tests.
- Nonlinear Thm: clone a Thm, derive two distinct consequences,
  combine.

### Phase 5 — Anonymous concepts API (Rust-only)

**Scope.** Add the anonymous-concept system.

- `Kernel::declare_anonymous_concept(kind) -> ConceptHandle`.
- `ConceptHandle::add_theory_axiom(prop)` — kernel validates
  conclusion shape `… ⇒ c[α](…) = true`.
- On accepted axiom: kernel `union`s the conclusion's
  `c[α](t₁,…,tₙ)` with `True` in the UF.
- No `enter()`, no `attest_all()`, no named/root concept yet.

**Deliverables.**
- `covalence-hol/src/concept.rs`.
- Conclusion-shape checker.

**Acceptance.**
- Declare a concept, observe a tuple, derive a Thm using the
  observation via a trust assumption.
- Owner-axiom shape check rejects `c(x) = false`, accepts the legal
  shapes, accepts axioms with arbitrary HOL premises whose conclusion
  matches.

### Phase 6 — Serialisation (Prop only, no concepts)

**Scope.** Define a flat byte format for `Prop`. Round-trip
`serialize -> deserialize -> Prop<Untrusted>`. Untrusted Prop is
embeddable as a `bool` term but is not a Thm. Anonymous-concept
contents are *not* serialisable (and the format must reject Props
mentioning anonymous-concept constants for now).

**Deliverables.**
- `covalence-hol/src/serial.rs`.
- A versioned binary format building on `covalence-object`'s `Table`
  machinery.
- `deserialize(bytes) -> Result<Prop<Untrusted>, Error>`.

**Acceptance.**
- Round-trip every Thm produced by the Phase 5 tests (after stripping
  anonymous-concept content).
- Tampering with the bytes either fails deserialization or yields a
  Prop the kernel won't accept as a Thm.

### Phase 7 — WASM bridge: cov:hol/observe

**Scope.** A new host import interface in
`covalence-kernel/src/engine.rs`:

```
package cov:hol;
interface observe {
  // The Rust caller passes in pre-created ConceptHandles bound to
  // specific WIT interface names. The component sees only handles it
  // was granted.
  observe: func(handle: borrow<concept-handle>, args: list<term>);
}
```

Existing `cov:hol/kernel` HOL bridge (the resource API for
type/term/thm) is ported to the new arena trait.

**Deliverables.**
- `cov:hol/observe` interface in `engine.rs`.
- Port of the existing HOL bridge.
- Example WASM component (test fixture) that takes two blob imports,
  calls `observe` with them, and exits.

**Acceptance.**
- Engine test: run the example component; the corresponding theory
  axiom appears in the host kernel.
- Engine test: a component without a handle to a concept cannot
  observe it (the host linker refuses).

### Phase 8 — REPL bindings + MVP demo

**Scope.** Add Forsp primitives to the REPL for the new operations:

- `<kind> declare-anonymous-concept`
- `<handle> <arg1> <arg2> ... <n> observe`  (or similar arity-aware form)
- `<assumption-prop> add-context-assumption`
- `<thm> serialize` → blob
- `<blob> deserialize` → untrusted prop

Wire them into `covalence-repl`.

**Deliverables.**
- REPL primitives.
- A script (or integration test) that runs the MVP demo end-to-end.

**Acceptance.**
- The MVP demo described at the top of this doc runs from the Forsp
  REPL and produces the expected serialised Thm hash.
- The test verifies the demo's output is stable across runs.

---

## Out of Scope for MVP

The following are explicitly *not* MVP work, even though they're
called out in the architecture doc. They land in follow-up phases
once MVP is demonstrated.

- **Named / root concept; concept naming protocol.** Anonymous
  concepts only for MVP.
- **WASM spec axiom.** Tying observations to actual WASM operational
  semantics. The MVP user supplies the trust assumption directly.
- **Signed import.** `isValidSignature` as a concept, cross-process
  Thm import.
- **Content-addressed type definitions and function values.** The
  subtype-plus-spec pattern from architecture §7.4.
- **Definition splitting** (the "import the declaration without the
  body" pattern from architecture §7.3) — supported architecturally
  by the foreign-import machinery, but no first-class API or library
  utilities for it yet.
- **Goal API.** Untrusted "partially proved Prop" type with a tactic
  language.
- **Sub-capabilities (`enter()`).** Owner hands out narrower
  ConceptHandles.
- **Egraph-style closure strategies.** Saturating loops on top of the
  minimal UF.
- **Object-logic interpretations.** ZF, GT, category-theoretic
  semantics — all post-MVP follow-on.
- **Tactics.** Forsp/external tactic-language support beyond the
  REPL primitives needed to drive the demo.
- **Cogit integration.** Storing Thms in cogit trees with provenance
  metadata.

---

## Crate Impact Summary

| Crate | Phase touch | Nature of change |
|---|---|---|
| `covalence-hol` | 1, 2, 3, 4, 5, 6 | Heavy: arena rewrite with namespaces and builtins, locally-nameless terms, level-k equality, Prop/Thm/Context, concepts, serialisation. |
| `covalence-opentheory` | 1, 2, 4 | Port over each kernel-API change. Generic-over-`HolLightKernel` shape preserved. |
| `covalence-kernel` | 1, 2, 4, 7 | HOL bridge rewrite each time the trait changes; new `cov:hol/observe` in phase 7. |
| `covalence-repl` | 8 | New Forsp primitives. |
| `covalence-wasm` | 7 | New resource types in the runtime if needed. |
| `covalence-serve` | 8 | Web/HTTP exposure of new REPL commands (probably trivial). |
| `covalence-isabelle` | — | Stays deleted. |
| `covalence-sat`, `covalence-smt`, `covalence-lean`, `covalence-metamath`, `covalence-forsp` | — | Untouched in MVP. Re-evaluated post-MVP. |
| `MVP_DESIGN.md`, `DESIGN.md` | 8 | At MVP completion, mark superseded by this doc. |

---

## Open Questions

These don't block starting on Phase 1, but should be resolved before
the phase they're listed under.

- **Phase 1.** `ArenaId` allocation strategy: monotonic u32 from a
  kernel-global counter, vs. the arena's content hash (for frozen
  arenas only). Likely monotonic for live arenas, hash for serialised
  ones — but the canonical-tuple shape is the same either way.
- **Phase 1.** `BitsLit` size cutoff before falling back to
  `BitsHashed`. Pick when implementing — 256 bits is a reasonable
  default.
- **Phase 2.** Free-variable naming: `VarName` interned strings vs.
  opaque IDs. Probably interned strings for printing.
- **Phase 3.** Should `eq_at_level(_, _, ∞)` be a real primitive or
  computed by a library wrapping a level-counter? Trivial either
  way; pick when implementing.
- **Phase 4.** Newtype vs phantom-tag for Thm — phantom integrates
  more cleanly with `Prop<Untrusted>` in Phase 6. Decide at
  implementation time.
- **Phase 5.** `ConceptKind` declaration shape — type arity + args
  arity. Fix when implementing.
- **Phase 6.** Whether to reject Props referencing anonymous
  concepts at the serialisation boundary, or to substitute "unknown
  concept" placeholders. Reject is safer for MVP.
- **Phase 7.** Term-as-WASM-resource representation: opaque borrowed
  TermId, vs. a small wire format the component can introspect.
  Lean opaque-borrow for MVP.

---

## How to Use This Doc

- Treat phases as the unit of work. Each phase is a self-contained
  PR-sized change with its own acceptance tests.
- Don't skip ahead — the dependencies are real (arena before
  locally-nameless before Prop, etc.).
- When you finish a phase, update
  [`prover-architecture.md`](./prover-architecture.md) if the
  architecture changed (it shouldn't, much — that doc is the spec).
- When you start a new session, read the architecture doc first to
  re-orient, then pick the next phase here.
