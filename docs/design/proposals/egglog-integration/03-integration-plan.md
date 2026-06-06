# 03 — Integration plan

Phases here are **catalogue entries shipped**, not "more egglog
features supported". Each entry in
[`04-theory-catalogue.md`](./04-theory-catalogue.md) is a
self-contained (theory, decision question) pair; this document
sequences which entries we land first and what shared
infrastructure they need.

## Recap of the two engineering layers

* **Layer A — Oracle replay.** Run external egglog, request a proof
  DAG via `(prove (= a b))`, walk the `ProofStore`, replay each
  `Justification` node into an `EThm` rule call. egglog is fully
  untrusted; the `EThm` constructors are the trust boundary. Same
  shape as `covalence-smt::alethe.rs` (Alethe replay from cvc5) and
  `covalence-sat::drat.rs` (DRAT replay from SAT solvers).
* **Layer B — Native runner.** Parse a subset of egglog syntax with
  a new `covalence-sexp` dialect, compile to a `Program`, run it
  against `Egraph` with our own match + apply + congruence-rebuild
  loop. Every union is an `EThm::union` call.

The layers are a tooling choice per catalogue entry. Some entries
ship A only; some ship B only; some ship both and let the user
choose. The scaffolding work is largely shared.

## Shared infrastructure (built once, used by every entry)

* **An egglog AST** mirroring `Command`, `Action`, `Fact`, `Expr`.
  Living in `covalence-egglog::ast`. Layer A parses egglog source
  (so it can pre-flight `program_supports_proofs` and so the
  proof's `Rule.name` resolves to a user rule); Layer B compiles
  the AST to its runner.
* **A `Theory` value type** holding a name, the rule ASTs, the
  sort signature, and any primitive-table bindings. Hashable. A
  catalogue entry *is* a `Theory` plus a decision-question
  driver. (See "Forward compatibility" below — this is also one
  of the Layer-C guardrails.)
* **A `RuleCatalog`** mapping rule names to (a) the rule's AST and
  (b) a replay handler that turns a `(Justification, σ)` event into
  a sequence of `EThm` calls. Built-in axioms (refl, sym, trans,
  cong, …) are hardcoded; user rewrites are synthesised from
  LHS/RHS at theory-registration time.
* **A primitive-sort table** describing which `i64`, `String`,
  `Bool` literals exist in the arena and how to embed them as
  `TermRef`s. Per-theory, since not every entry uses primitives.

The shared infrastructure is what Phase 0 builds. From Phase 1
onward, every phase is "one or more catalogue entries lit up against
the shared scaffold".

## Phasing

### Phase 0 — Scaffold

Build the shared infrastructure above. No catalogue entries land
yet; the goal is to have an empty runtime that *could* drive an
entry once one is written.

Crate layout:

```
crates/
  covalence-egglog/
    src/
      ast.rs          # AST mirroring egglog 2.0 (subset for now)
      parse.rs        # uses covalence-sexp + new EgglogDialect
      theory.rs       # Theory struct, hashing, registration
      catalog.rs      # RuleCatalog: name -> (AST, replay handler)
      primitives.rs   # per-theory PrimitiveTable
      walker/         # proof-walker emitting Justification events
        events.rs     # Event = { proposition, justification, σ }
        store.rs      # parse egglog's ProofStore (or JSON dump)
      lib.rs
    Cargo.toml
```

No `EThm`-calling code yet; that arrives with the first entry.

### Phase 1 — Catalogue entries: EUF + one pure equational theory

Two entries from the catalogue, both shipped via Layer A:

* **EUF (equality with uninterpreted functions).** The canonical
  congruence-closure decision problem; every `Justification`
  variant is a built-in axiom. Tests the end-to-end pipeline
  without needing any user-rewrite handler.
* **A pure equational theory** (suggested: monoid identities — a
  three-rule confluent system) for the user-rewrite path. Tests
  that the `RuleCatalog` correctly synthesises a handler from a
  rewrite AST.

This is also where the `oracle/` submodule appears:

```
crates/covalence-egglog/src/
  oracle/             # Layer A engine
    run.rs            # invoke external egglog, get ProofStore
    consume.rs        # EThm-driving consumer of walker events
    proof.rs          # mirror of egglog's Justification enum
```

Acceptance criteria:

* For each entry: a small egglog program is parsed, run through
  external egglog, the proof DAG is replayed, and an `EThm` whose
  `eq(a, b)` returns true is produced.
* Negative test: a program containing `delete` is rejected at the
  `program_supports_proofs` gate with a useful diagnostic.

Open questions for Phase 1:

* **Library vs CLI.** Linking `egglog = "2.0"` is the obvious win,
  but it pulls in a large dep tree. Likely answer: vendor egglog
  behind a Cargo feature so non-egglog users don't pay the cost.
* **Proof transport.** If we shell out, we need a serialisation;
  the egglog team hasn't frozen one. A thin JSON dump of the
  `Proof`/`Justification`/`Proposition` enums is the natural
  fallback; worth an upstream feature request.
* **Term identity.** egglog's `TermId` is a node in its own
  `TermDag`. The walker maps each `TermId` to a `TermRef` in our
  `Arena`; the catalog provides the constructor bindings.

### Phase 2 — Catalogue entries: theory of arrays, theory of lists

Two more catalogue entries, both still Layer A. They exercise:

* a fixed axiom set per entry (the array axiom; the list axioms);
* multiple sorts coexisting in one theory (lists need element + list);
* the rule-catalog handler shape for non-trivial rewrites.

If by this point the answer to "library vs CLI" is "library", and
the scaffold is comfortable, this is a fast phase.

### Phase 3 — Layer B's runner; re-instantiate Phase 1 entries on it

Build the native runner:

```
crates/covalence-egglog/src/
  native/
    program.rs        # compiled rules, schedule, initial actions
    runner.rs         # match + apply + congruence-rebuild loop
    match.rs          # e-matching over Egraph::arena
    extract.rs        # cost-model extractor
```

Re-instantiate the Phase 1 entries on the native runner. The
catalogue entry definitions stay the same; only the back-end
changes. Output is the same `EThm`; an end-to-end equivalence test
asserts that Layer A and Layer B agree on every Phase 1 example.

This phase is what forces us to confront **schedules and rulesets**
in earnest — they were "passthrough" in Phase 1 (egglog handled
the scheduling), but here we own them.

### Phase 4 — Datalog: relations and rule premises

Extend the kernel `Egraph` (or a sibling structure) to support
relations as joinable tables, then ship one Datalog-shaped
catalogue entry: **graph reachability**. Layer A inherits relation
support for free (it consumes egglog's view); Layer B needs the
storage.

Two design options for relation storage:

1. **Embed relations as `TermDef::App` rows.** A relation
   `(relation edge (i64 i64))` becomes a function symbol whose
   applications are arena terms. Joins become walks over the
   arena's indexed structure. Cheap to specify; expensive to
   evaluate.
2. **Add a parallel `RelationStore`.** A separate table store
   keyed by function symbol and argument tuple, indexed for joins.
   This is what egglog itself does. More code; better performance;
   cleaner separation.

Recommendation: option 2. The kernel already keeps arena and UF
separate; adding a third store fits the shape.

Acceptance criteria:

* Reachability entry decides reachability for small input graphs.
* Layer A and Layer B agree on the answer for the same input.

### Phase 5 — Lattice-valued analyses (merge functions and primitive sorts)

`function … :merge expr` with non-trivial merge expressions, plus
`i64`/`String`/`Bool` ops as first-class primitives in the arena.
Ship one analysis entry: **constant propagation** (the smallest
lattice).

Each primitive op becomes an arena `TermDef::Prim` variant with a
known evaluator. Each merge function corresponds to a rewrite that
fires on row collision. egglog's `Justification::MergeFn` becomes a
replay-time call to "rebuild the merge expression under σ, then
apply the merge rewrite".

We re-evaluate primitive arithmetic in our own kernel rather than
trusting egglog's — Layer A then checks that the egglog-reported
result matches ours.

### Later phases (unscheduled)

The remaining catalogue entries (AC word problem; confluent term
rewriting systems; richer analyses; specific decidable subfragments
of arithmetic; …) light up against the scaffold individually, in
whatever order the *interesting problems* drive. There's no inherent
ordering; each entry is independent.

**Out of scope without a specific use case.** Containers (`Map`,
`Vec`, `Set`, `BigInt`, `BigRat`) would each be a single
late-phase entry at best, and only if egglog ships proof encoding
for them upstream.

## Crate boundaries

```
covalence-egglog                  # this proposal
  ├── (no features)               # AST + parser + theory + catalog + walker
  ├── feature `oracle`            # Layer A: external egglog replay
  └── feature `native`            # Layer B: runner over Egraph

covalence-kernel                  # touched in Phase 4 only
  └── relations module (option 2 above)

covalence-python                  # touched only when we ship the Python frontend
  └── per-theory decorator API mirroring egglog-python (see 02-python-api)
```

The split keeps the proof-replay path independent of the runner. A
user who only wants ingestion gets a small dep footprint; a user
who wants native authoring gets the runner without the egglog
runtime.

## How this fits with the rest of Covalence

* **Same pattern as covalence-smt / covalence-sat.** Both already
  consume third-party proofs through a kernel-checked replay
  (Alethe, DRAT). Layer A is the egglog rendition of the same
  pattern; the file layout (`oracle/run.rs`, `oracle/consume.rs`)
  mirrors `covalence-smt::checker` + `covalence-smt::alethe`.
* **Same pattern as covalence-hol / covalence-opentheory.** These
  expose surface languages that compile down to the same `Thm`
  primitive. Layer B is the egglog rendition; the goal at the end
  of a Layer B run is an `EThm`, not a custom certificate.
* **The catalogue model maps to the morphism plane.** A catalogue
  entry is a *base* (in ARCHITECTURE v2 terms): a small theory with
  its own signature and decision question. Morphisms between bases
  let us lift a theorem proved in one entry's theory into a
  client's larger base — i.e., the catalogue is composable by
  design, not by extending any single entry.

## What blocks committing to this plan

1. **Is `Egraph` expressive enough?** Today's `Arena` is a HOL
   term language. Catalogue entries that need user-defined
   constructors will map each constructor name to a fresh
   `TermDef::App(ctor_id, args)`; whether this stays sound across
   the relation and merge-function phases is open. Resolved by
   Phase 4 design work.
2. **Does egglog 2.0's proof encoding cover the entries we want?**
   Anecdotally, the encodable fragment is "rewrites and simple
   rules over eqsorts" — i.e., everything in Phases 1–2 plus most
   of Phase 4. We need to confirm per-entry by running
   `program_supports_proofs` over the entry's canonical egglog
   encoding.
3. **Crate footprint.** Vendoring egglog as a dep is the easy
   choice but bloats the workspace. The alternative (shell out +
   JSON proof) needs egglog to grow a stable proof serialisation.
   Worth filing an upstream feature request once Phase 1 lands.
4. **Schedules with side effects.** `delete` and `subsume`
   intentionally break monotonicity. Layer B can't naively support
   them without giving up `EThm`'s monotone guarantee. Reasonable
   default: refuse, with a diagnostic. Most catalogue entries don't
   need them.

## Forward compatibility with a meta-provability layer

A long-term goal (see the README's "third mode") is to also obtain
`Thm (Provable_T(⌜P⌝))` from the same egglog run — a meta-claim
that the theory `T` derives `P`. The catalogue framing makes `T`
concrete (each entry fixes one), so this layer is unusually clean
*if* we don't foreclose it now. Four small constraints on Phases
0–4 buy that future:

1. **Separate the proof walker from the consumer.** The walker
   emits an event per `Justification` node (`{ proposition,
   justification, substitution }`); the `EThm`-calling code
   consumes that event stream. The walker takes no `EThm`
   dependency. A future Layer C consumes the *same* event stream
   to build a deeply-embedded `EggDeriv` HOL term. Phase 0's
   `walker/` submodule already encodes this split.
2. **Rule bodies stay as data, not closures.** Each `RuleCatalog`
   entry carries the rule's AST (LHS / RHS / premise shapes)
   alongside its replay handler. Layer A only reads the handler;
   a future Layer C reads the AST to reify rules into HOL. If we
   let handlers be opaque closures with hidden Rust state, the
   reification path is blocked.
3. **A theory is a first-class value.** `Theory` from Phase 0 is
   the load-bearing type here. Hashable, serialisable, the unit
   the catalogue indexes on. Layer C's `Provable_T`
   parameterises over `T`, so `T` must be something we can name,
   hash, and pass around. This also pays off in Layer A for
   proof-cache lookup keyed by `(T, proposition)`.
4. **Primitives declared, not hardcoded.** `i64`/`String`/`Bool`
   operations enter the runner through a `PrimitiveTable` that
   exposes each op's name and signature, not via match arms inside
   the saturation loop. A future HOL embedding declares matching
   primitive symbols and proves their semantics once; the Layer
   A/B/C runtimes all dispatch through the same table.

None of these add work to Phases 0–3 beyond mild discipline — they
are mostly "use a struct, not a closure" and "thread `&Theory`
explicitly". The cost of *not* doing them is a substantial
refactor when Layer C eventually wants in.

## What to do next (concrete)

If we want to start any of this:

1. **Validate the corpus.** Vendor a copy of egglog's `tests/*.egg`
   and run `program_supports_proofs` over each one. The result
   tells us what fraction of real egglog code is Layer-A-eligible
   without us writing any replay code.
2. **Prototype a single catalogue entry end-to-end.** Pick EUF:
   `(datatype …)` + two `(rewrite …)`s + `(prove (= a b))`. The
   whole prototype is probably under 500 LoC and tells us whether
   the `TermId`-to-`TermRef` mapping has any hidden hazards.
3. **Then revisit this proposal** with the prototype's findings
   and commit (or amend) the phasing.

These are independent of the bigger Phase P refactor — the
prototype uses today's `EThm` API as-is.

## See also

* [`00-foundations.md`](./00-foundations.md) — egglog semantics + 2.0 proofs
* [`01-commands.md`](./01-commands.md) — per-feature K/P/O map (a *constraint* on catalogue entries)
* [`02-python-api.md`](./02-python-api.md) — Python frontend shape per entry
* [`04-theory-catalogue.md`](./04-theory-catalogue.md) — the catalogue itself
* [`../../../prop-egraph-design.md`](../../../prop-egraph-design.md) — the `EThm` redesign this plan targets
* [`../../../../crates/covalence-smt/src/alethe.rs`](../../../../crates/covalence-smt/src/alethe.rs) — analogous oracle-replay path for SMT
* [`../../../../crates/covalence-sat/src/drat.rs`](../../../../crates/covalence-sat/src/drat.rs) — analogous oracle-replay path for SAT
