# Prover MVP Plan

Companion to [`prover-architecture.md`](./prover-architecture.md). This
document is **tactical**: it lists the phases, deliverables, and acceptance
tests to get from the current state of the tree to the first end-to-end
demo of the new prover.

The architecture doc says *what we're building*. This doc says *what we do
each step of the way*.

---

## Crate Layout

The new design is built by rewriting one crate and adding another:

- **`covalence-kernel`** (existing crate, rewritten end-to-end). The new
  HOL kernel: Arena, Prop, Thm, Context, concepts, inference rules. It
  is generic over **abstract Store and Executor traits** — no
  wasmtime, no SQLite, no specific blob format. The kernel knows about
  the HOL logic and nothing else.
- **`covalence-shell`** (new crate). The concrete wiring: it picks
  specific Store/Executor implementations, wires up the existing
  wasmtime engine as a concept-observation runtime, hosts the
  untrusted utilities (Goal, tactic combinators, closure strategies,
  REPL primitives, etc.), and exposes everything the CLI/REPL needs.
- **`covalence-hol`** is **left untouched**. The arena-based
  experimental kernel that lives there today stays as a parallel
  reference; future sessions may or may not retire it once the new
  kernel is mature. The MVP work does not touch it.

What gets removed from the current `covalence-kernel` during the
rewrite is fair game — including the existing `attest()` host import,
the decide-returns-Sat/Unsat pipeline, and the WASM-component-as-
proposition model. Some of these will return in different form (e.g.
`attest()` will eventually be "observe `concept[wasm_hash]` for the
running module's identity," landing post-MVP). Others (the
True/Unknown/False decision caches) may not come back at all. That's
fine — the rewrite is total, not incremental.

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
for serialisable concepts; content-addressed types and function
values; the concept-owned type hierarchy. We assume the user adds the
trust assumption directly. Proving the spec axiom and naming come
later.

---

## Phases

Each phase produces a working tree that builds and tests cleanly. Land
phases as separate commits or short-lived branches; each phase has
acceptance tests before merge.

### Phase 0 — Crate scaffolding

**Scope.** Set up the two crates in the workspace before any logic
moves:

- Empty out `covalence-kernel`'s `src/` and start fresh. The old
  contents (engine, decide pipeline, Wasmtime bridge) are deleted —
  much of it will come back via `covalence-shell` in later phases.
- Create `covalence-shell` as a new workspace member. For now it
  contains a `lib.rs` exporting nothing.
- Update consumers (`covalence`, `covalence-serve`, `covalence-repl`)
  to depend on whichever of the two they need. During the rewrite
  some `cargo check` failures are expected; mark or comment out
  affected code paths to keep the workspace compiling.

**Deliverables.**
- Empty `covalence-kernel/src/lib.rs`.
- New `covalence-shell` crate.
- Workspace `cargo check` still passes (with whatever stubs are
  needed downstream).

**Acceptance.**
- `cargo check --workspace --all-features` clean.
- `cargo test --workspace --all-features` runs (tests may be
  stubbed/ignored; nothing should fail).

### Phase 1 — Arena + namespaces + builtins (in `covalence-kernel`)

**Scope.** Stand up the new arena in `covalence-kernel`:

- Separate ID namespaces (no shared `NameId`): `TypeName`, `ConstName`,
  `VarName`, `ConceptId` each in its own table. Builtins (§3.2 of the
  architecture doc) are TermDef/TypeDef enum variants, not entries in
  any namespace.
- **One** `TermDef` enum with every kind of term as a variant:
  structural ones (`Bound`, `Free`, `Const`, `Comb`, `Abs`) and
  builtins (`True`, `False`, `Eq(_, _)`, `Bits(_)`). Same for
  `TypeDef` (`Bool`, `Bits`, `Fun`, `TVar`, `Tyapp`). No
  "well-known" magic name IDs or side tables.
- `BitsValue = Inline([u8; N]) | Indirect(BitsId)`; long bit-string
  literals go through an arena-side `bitvectors` table indexed by
  `BitsId`. No content addressing in the kernel — `Indirect` is an
  internal arena index, not a hash.
- **Arena identity is by pointer** — no `ArenaId` u32 anywhere.
  Stored canonical references are `(Arc<Arena>, TermId)` /
  `(Arc<Arena>, TypeId)`. Two canonicals are equal when the
  `Arc<Arena>`s are `Arc::ptr_eq` and the inner IDs match.
- Read paths take **`&Arena`** where possible to avoid Arc refcount
  bumps; pointer-equality crosses the `Arc<Arena>` / `&Arena`
  boundary cleanly (compare both as `*const Arena`).
- `TermRef = Local(TermId) | Foreign(Arc<Arena>, TermId)` for stored
  state (e.g. inside a TermDef); read APIs typically project the
  `Arc` to a `&Arena` for traversal.
- UF storage stood up: `TermUfEntry { canonical: (Arc<Arena>,
  TermId), closed }`, `TypeUfEntry { canonical: (Arc<Arena>, TypeId)
  }`. Equality predicates over them land in Phase 3 and take
  `&Arena` arguments.
- Frozen-vs-mutable arenas; `Arc<Arena>` for frozen.
- Structural tables append-only at the user level; the kernel
  reserves `rewrite(t, new_def)` as a privileged primitive (exposed
  in Phase 3 once the equality predicates can validate the
  replacement).

**Deliverables.**
- `covalence-kernel/src/arena.rs` and supporting modules.
- Abstract `Store` trait sketch (see *Abstract traits* note below);
  no concrete implementation yet.

**Acceptance.**
- `cargo test -p covalence-kernel` green.
- Property test: random sequences of `union(...)` calls preserve the
  invariant that two terms are level-0-equal iff they should be.
- Diamond-import test: arenas D, B, C, A as in the architecture doc
  §4.1; verify shared-D subterms regain UF identity while
  B-originated vs C-originated terms remain structurally distinct
  unless explicitly unioned.

**Abstract traits note.** From Phase 1 onward, the kernel's `Store`
and (later) `Executor` are `trait` interfaces, not concrete types.
The kernel never imports `wasmtime` or `covalence-sqlite` directly.
The `covalence-shell` crate is what supplies concrete impls.

### Phase 2 — Locally-nameless terms + closed/open

**Scope.** Locally-nameless term language: `Bound(u32) | Free(VarName,
TypeRef)` plus the builtins. Tag each term entry with `closed`,
computed on insertion. The UF refuses non-congruence unions of open
terms. All inference rules use the new shape.

**Deliverables.**
- New `TermDef` variants matching architecture §3.1.
- `Thm::abs` introduces a binder over a `Free` (locally-nameless ABS).
- `Thm::beta` reduces `(λ. body) arg` via index substitution.
- Open-term rejection on `union()` with a clear error; congruence
  union on open terms via `union_if_congruent_step` succeeds.

**Acceptance.**
- HOL primitive-rules tests pass.
- Open-vs-closed targeted tests: attempting to union two distinct
  free variables fails; congruence unions on open terms succeed.

### Phase 3 — Equality predicates, congruence step, rewrite

**Scope.** Add the equality-at-level family and the explicit
congruence step, for both terms and types. Expose `rewrite`.

- `eq_at_level(a, b, k)` and `type_eq_at_level(a, b, k)` for
  `k ∈ {0, 1, …, ∞}`, transparently following foreign-arena pointers.
- `union_if_congruent_step(a, b)` — if `a` and `b` decompose to the
  same shape and corresponding children are `eq_at_level(_, _, 0)`,
  union them; otherwise return failure (no error). Same shape for
  the type-level analog.
- `rewrite(t, new_def)` — replace `terms[t].definition` with
  `new_def`, requiring the kernel to verify `t = new_def` via the UF
  (or a supplied Thm). Mutates the structural form in place; the
  canonical stays consistent.
- Remove any leftover "automatic congruence" code from Phase 1.

**Deliverables.**
- `covalence-kernel/src/uf.rs` with the equality and congruence-step
  builtins.
- The `rewrite` primitive with its validity check.
- `MK_COMB` rewritten as a thin wrapper around
  `union_if_congruent_step`.

**Acceptance.**
- The level-0 / level-1 / level-∞ semantics each have direct tests
  for terms and for types.
- A failing congruence-step test returns failure cleanly without
  polluting the UF.
- `rewrite` accepts a valid replacement and reflects the new form in
  downstream traversals; rejects an unjustified replacement.

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
- Kernel has no axiom list; "axioms" are Props in the root Context.

**Deliverables.**
- `covalence-kernel/src/{prop,thm,context}.rs`.
- Existing rules ported.

**Acceptance.**
- Push a context, prove a Thm under it, pop the context — the Thm's
  Context remains valid via Arc.
- `add_assumption` and `not_from_false` round-trip tests.
- `Context::find_equality` returns matches for unioned-in-an-
  assumption equalities; no match for unrelated terms.
- Nonlinear Thm: clone, derive two consequences, combine.

### Phase 5 — Anonymous concepts (Rust-only)

**Scope.** Anonymous-concept system, constant families only. The
concept owner can write theory axioms about the constant family.
Owner-declared **conceptType** opaque types (architecture §6.4) are
*not* in MVP — that's a separate primitive (`declare_concept_type`)
the kernel will get later, and anything asserted about a conceptType
goes via the user's Context anyway (not via the owner).

- `Kernel::declare_anonymous_concept(kind) -> ConceptHandle`.
- `ConceptHandle::add_theory_axiom(prop)` — kernel validates
  conclusion shape `… ⇒ c[α](…) = true`.
- On accepted axiom: kernel `union`s the conclusion's
  `c[α](t₁,…,tₙ)` with `True` in the UF.
- No `enter()`, no `attest_all()`, no named/root concept, no
  `conceptType` declarations.

**Deliverables.**
- `covalence-kernel/src/concept.rs`.
- Conclusion-shape checker.

**Acceptance.**
- Declare a concept, observe a tuple, derive a Thm using the
  observation via a trust assumption.
- Owner-axiom shape check rejects `c(x) = false`, accepts legal
  shapes, accepts axioms with arbitrary HOL premises whose
  conclusion matches.

### Phase 5b — Prop-as-bool and Context-as-bool imports

**Scope.** The two meta-level import operations from architecture
§2.5:

- `import_prop_as_bool(p) -> TermId` — produces a bool term in the
  current arena representing "Prop `p` is true."
- `import_context_as_bool(ctx) -> TermId` — produces a bool term
  representing "every assumption in `ctx` holds."

These are kernel primitives because they need to weave foreign-arena
references correctly. Useful for stating cross-context relations
(e.g. `isValidSignature(key, sig, import_prop_as_bool(p))`) without
materialising the Prop's contents at the meta level.

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
mentioning anonymous-concept constants).

**Deliverables.**
- `covalence-kernel/src/serial.rs`.
- A versioned binary format building on `covalence-object`'s `Table`
  machinery.
- `deserialize(bytes) -> Result<Prop<Untrusted>, Error>`.

**Acceptance.**
- Round-trip every Thm produced by the Phase 5 tests (after
  stripping anonymous-concept content).
- Tampering with the bytes either fails deserialisation or yields a
  Prop the kernel won't accept as a Thm.

### Phase 7 — Shell: Store + Executor concretes

**Scope.** Stand up the shell's concrete implementations of the
kernel's abstract traits, and put the WASM engine in service of the
concept system.

- `covalence-shell` exposes a `Store` impl (initially in-memory
  blob storage; SQLite-backed later if needed for MVP).
- `covalence-shell` exposes an `Executor` impl that runs WASM
  components and exposes a `cov:hol/observe` host import. The Rust
  caller passes pre-created ConceptHandles bound to specific WIT
  interface names; the component sees only handles it was granted.
- Old `decide()`-with-`attest()` pipeline does NOT come back in
  this phase. The component just calls `observe(handle, args)`; no
  attestation, no Sat/Unsat result. Eventually `attest()` will
  return as observation of `concept[wasm_hash]`, but that's
  post-MVP.

**Deliverables.**
- `covalence-shell/src/store.rs`, `executor.rs`.
- `cov:hol/observe` WIT interface and host implementation.
- Example WASM component (test fixture) that takes two blob
  imports, calls `observe` with them, and exits.

**Acceptance.**
- Shell test: run the example component; the corresponding theory
  axiom appears in the kernel.
- Shell test: a component without a handle to a concept cannot
  observe it (the host linker refuses).

### Phase 8 — REPL bindings + MVP demo

**Scope.** Add Forsp primitives to the REPL for the new operations
and run the MVP demo end-to-end.

Primitives (all wired through `covalence-shell`):

- `<kind> declare-anonymous-concept`
- `<handle> <arg1> <arg2> ... <n> observe`
- `<assumption-prop> add-context-assumption`
- `<thm> serialize` → blob
- `<blob> deserialize` → untrusted prop

**Deliverables.**
- REPL primitives in `covalence-repl` calling into `covalence-shell`.
- A script or integration test that runs the MVP demo.

**Acceptance.**
- The MVP demo runs from the Forsp REPL and produces the expected
  serialised Thm hash.
- The test verifies the demo's output is stable across runs.

---

## Out of Scope for MVP

- **Named / root concept; concept naming protocol.** Anonymous
  concepts only.
- **Concept-owned type hierarchy (`conceptType`).** Constants only
  in MVP.
- **WASM spec axiom.** Tying observations to actual WASM operational
  semantics. The MVP user supplies the trust assumption directly.
- **`attest()` host import returning.** It'll come back as
  "observe `concept[wasm_hash]`" but not in MVP.
- **`decide()` returning Sat/Unknown/Unsat.** Repurposed away in the
  rewrite; whether it comes back at all (and in what form) is open.
- **Signed import.** `isValidSignature` as a concept; cross-process
  Thm import.
- **Content-addressed types and function values.** Architecture
  §§7.4/7.5 — uses the `conceptType` mechanism, lands together with
  it.
- **Definition splitting** ("import the declaration without the
  body" pattern, architecture §7.3) — supported architecturally,
  no first-class library utility yet.
- **Type-level `union_if_congruent_step` as a user-facing rule.**
  Infrastructure in place from Phase 3; let tactics use it from an
  untrusted library wrapper later.
- **Goal API and tactic language.** Untrusted-library territory.
- **Sub-capabilities (`enter()`).**
- **Egraph-style closure strategies and assumption search.**
- **Object-logic interpretations** (ZF, GT, categorical
  semantics) — all post-MVP follow-on.
- **Cogit integration.** Storing Thms in cogit trees with
  provenance metadata.

---

## Crate Impact Summary

| Crate | Phase touch | Nature of change |
|---|---|---|
| `covalence-kernel` | 0, 1, 2, 3, 4, 5, 5b, 6 | Complete rewrite. Builds the new HOL kernel over abstract Store/Executor traits. Existing decide/attest pipeline is removed; some of it may return post-MVP through the shell. |
| `covalence-shell` | 0, 7, 8 | New crate. Concrete Store + Executor implementations, the WASM `cov:hol/observe` bridge, REPL plumbing, untrusted utilities. Inherits much of the *implementation* of the current `covalence-kernel`'s wasmtime/store wiring. |
| `covalence-repl` | 8 | New Forsp primitives calling `covalence-shell`. |
| `covalence-serve` | 0, 8 | Switches from `covalence-kernel` to `covalence-shell` where it needs concrete types. |
| `covalence` (CLI) | 0, 8 | Same — depend on the shell rather than the kernel directly. |
| `covalence-wasm` | 7 | Possibly: new resource types if the observe interface needs them. Otherwise no change. |
| `covalence-hol` | — | **Untouched** for MVP. Existing tests continue to pass against the existing arena-based code. Retiring it is a separate decision after MVP. |
| `covalence-opentheory` | — | **Untouched** for MVP. It's a client of `covalence-hol`. |
| `covalence-isabelle` | — | Stays deleted. |
| `covalence-sat`, `covalence-smt`, `covalence-lean`, `covalence-metamath`, `covalence-forsp` | — | Untouched. Re-evaluated post-MVP. |
| `MVP_DESIGN.md`, `DESIGN.md` | 8 | Mark superseded by this doc at MVP completion. |

---

## Open Questions

- **Phase 0.** Done — landed as commits `phase 0a` / `phase 0b` /
  `phase 0c` on top of `better plan`.
- **Phase 1.** Arena identity uses `Arc<Arena>` for stored
  references and `&'a Arena` for borrowed read paths. Pointer
  equality (`Arc::ptr_eq` / `std::ptr::eq`) works across both. No
  kernel-issued u32 `ArenaId` table (considered, rejected as
  unnecessary bookkeeping). For functions wanting either, the
  `ArenaRef<'a>` enum in architecture §2.2 is available.
- **Phase 1.** `BitsValue::Inline` size cutoff before promoting to
  `Indirect(BitsId)`. 256 bits is a reasonable default.
- **Phase 1.** What's the `Store` trait actually need to expose?
  Likely just `put(bytes) -> name`, `get(name) -> Option<bytes>`
  for MVP. The kernel itself barely uses it; mostly for arena
  freeze/thaw if at all.
- **Phase 2.** Free-variable naming: interned strings vs opaque IDs.
  Probably interned strings for printing.
- **Phase 3.** Should `eq_at_level(_, _, ∞)` be a real primitive or
  computed by a library wrapping a level counter? Trivial either
  way.
- **Phase 4.** Newtype vs phantom-tag for Thm — phantom integrates
  more cleanly with `Prop<Untrusted>` in Phase 6.
- **Phase 5.** `ConceptKind` declaration shape — type arity + args
  arity. Fix when implementing.
- **Phase 6.** Reject vs placeholder for Props referencing anonymous
  concepts at serialisation. Reject is safer for MVP.
- **Phase 7.** Term-as-WASM-resource representation: opaque borrowed
  TermId vs a small wire format. Opaque-borrow for MVP.
- **Phase 7.** Does `covalence-shell` re-export the kernel for
  downstream consumers, or do consumers depend on both? Re-export
  is friendlier; we can revisit if it hides too much.

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
