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
- `TypeDef` and `TermDef` enums with builtin variants (`Bool`,
  `Bits`, `Fun`, `Eq`, `True`, `False`, `Bits(Inline | Indirect)`).
  Long bit-string literals go through an arena-side `bitvectors`
  table indexed by `BitsId`. No content-addressing knowledge in the
  kernel — `Indirect` is just an internal arena index, not a hash.
- Arena-aware canonical IDs: `TermUfEntry { canonical: (ArenaId,
  TermId), closed }` and `TypeUfEntry { canonical: (ArenaId, TypeId)
  }` (see Phase 3 for the type-side equality predicates; Phase 1
  just stands up the storage).
- `TermRef = Local(TermId) | Foreign(ArenaId, TermId)` for cross-arena
  child links inside `Comb`/`Abs`. Same shape for `TypeRef`.
- Frozen-vs-mutable distinction; `Arc<Arena>` for frozen arenas.
- Structural tables append-only at the user level. The kernel
  reserves `rewrite(t, new_def)` as a privileged primitive (Phase 3
  exposes it once the equality predicates exist to validate the
  replacement).

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

### Phase 3 — Equality predicates, congruence step, rewrite

**Scope.** Add the equality-at-level family and the explicit
congruence step, *for both terms and types*. Expose the `rewrite`
primitive.

- `eq_at_level(a, b, k)` for `k ∈ {0, 1, …, ∞}`, transparently
  following foreign-arena pointers. Same shape for
  `type_eq_at_level`.
- `union_if_congruent_step(a, b)` — if `a` and `b` decompose to the
  same shape and corresponding children are `eq_at_level(_, _, 0)`,
  union them; otherwise return failure (no error). Same shape for
  the type-level analog.
- `rewrite(t, new_def)` — replace `terms[t].definition` with
  `new_def`, requiring that the kernel can verify `t = new_def` via
  the UF (or via a supplied Thm). Mutates the structural form in
  place; the canonical pointer stays consistent.
- Remove any leftover "automatic congruence" code from Phase 1.

**Deliverables.**
- `covalence-hol/src/uf.rs` (or wherever) with the equality and
  congruence-step builtins.
- The `rewrite` primitive with its validity check.
- `MK_COMB` rewritten as a thin wrapper around
  `union_if_congruent_step`.

**Acceptance.**
- The level-0 / level-1 / level-∞ semantics each have direct tests
  for terms and for types.
- A failing congruence-step test (children not yet equal) returns
  failure cleanly without polluting the UF.
- An accepted congruence-step test updates level-0 equality
  lookups.
- `rewrite` accepts a valid replacement and reflects the new form
  in downstream traversals; rejects an unjustified replacement.

### Phase 4 — Prop / Thm / Context (with Context API)

**Scope.** Introduce the data layer above the arena.

- `Prop = { arena, context: Arc<Context>, concl: TermId }`. The
  assumption list lives inside the Context, not on the Prop directly
  — this encapsulates the assumption API.
- `Thm` as a compile-time-tagged Prop (newtype or phantom — pick at
  implementation time; lean phantom for the §8 pair with
  `Prop<Untrusted>`).
- `Context = { assumptions: Vec<Arc<Prop>>, parent: Option<Arc<Context>> }`.
- `Context` inspection API: `len`, `assumption(i)`,
  `assumption_context(i)`, `find_equality(i, lhs, rhs)`, `parent()`.
  The kernel never searches the Context implicitly; tactics walk it
  explicitly.
- Two new inference rules: `add_assumption` and `not_from_false`.
- Kernel's old `axioms: Vec<ThmId>` removed; "axioms" are Props in
  the root Context.

**Deliverables.**
- `covalence-hol/src/{prop,thm,context}.rs`.
- Existing rules ported.

**Acceptance.**
- Push a context, prove a Thm under it, pop the context — the Thm's
  Context remains valid via Arc.
- `add_assumption` and `not_from_false` round-trip tests.
- `Context::find_equality` returns matches for unioned-in-an-
  assumption equalities; returns no-match for unrelated terms.
- Nonlinear Thm: clone a Thm, derive two distinct consequences,
  combine.

### Phase 5 — Anonymous concepts API (Rust-only)

**Scope.** Add the anonymous-concept system. Constants only; the
**conceptType type hierarchy** (architecture §6.4) is *not* in MVP —
concepts here are constant families, no opaque types yet.

- `Kernel::declare_anonymous_concept(kind) -> ConceptHandle`.
- `ConceptHandle::add_theory_axiom(prop)` — kernel validates
  conclusion shape `… ⇒ c[α](…) = true`.
- On accepted axiom: kernel `union`s the conclusion's
  `c[α](t₁,…,tₙ)` with `True` in the UF.
- No `enter()`, no `attest_all()`, no named/root concept, no
  `conceptType` declarations.

**Deliverables.**
- `covalence-hol/src/concept.rs`.
- Conclusion-shape checker.

**Acceptance.**
- Declare a concept, observe a tuple, derive a Thm using the
  observation via a trust assumption.
- Owner-axiom shape check rejects `c(x) = false`, accepts the legal
  shapes, accepts axioms with arbitrary HOL premises whose conclusion
  matches.

### Phase 5b — Prop-as-bool and Context-as-bool imports

**Scope.** Add the two meta-level import operations from architecture
§2.5:

- `import_prop_as_bool(p) -> TermId` — produces a bool term in the
  current arena representing "Prop `p` is true."
- `import_context_as_bool(ctx) -> TermId` — produces a bool term
  representing "every assumption in `ctx` holds."

These are kernel primitives because they need to weave foreign-arena
references correctly. Useful for stating cross-context relations
(e.g. `isValidSignature(key, sig, import_prop_as_bool(p))`) without
having to materialise the Prop's contents at the meta level.

**Deliverables.**
- `Kernel::import_prop_as_bool`, `Kernel::import_context_as_bool`.

**Acceptance.**
- Round-trip: build a Prop, import its bool form into a fresh arena,
  prove a meta-statement about it, reduce back to the original.

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
- **Concept-owned type hierarchy (`conceptType`).** Architecture
  §6.4 — concepts get the constant-family API in MVP, not the
  type-hierarchy API. Type isomorphism axioms enter after MVP.
- **Content-addressed types and function values.** Architecture
  §§7.4/7.5 — uses the `conceptType` mechanism, so this lands
  together with it.
- **Definition splitting** (the "import the declaration without the
  body" pattern from architecture §7.3) — supported architecturally
  by the foreign-import machinery, but no first-class API or library
  utilities for it yet.
- **Type-level `union_if_congruent_step` exposure as a user-facing
  rule.** The type UF infrastructure is in place from Phase 3; we'll
  let tactics use it from a library wrapper once we have a concrete
  need.
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
| `covalence-hol` | 1, 2, 3, 4, 5, 5b, 6 | Heavy: arena rewrite with namespaces and builtins, locally-nameless terms, level-k equality (terms+types), rewrite primitive, Prop/Thm/Context with inspection API, concepts, prop/context-as-bool imports, serialisation. |
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
  kernel-global counter. Content hashes of frozen arenas live
  *outside* the kernel (in the runtime around it), so kernel-side
  IDs stay opaque.
- **Phase 1.** `Bits::Inline` size cutoff before promoting to
  `Bits::Indirect(BitsId)`. Pick when implementing — 256 bits is a
  reasonable default.
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
