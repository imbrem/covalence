# `covalence-ml` — naive ML→WASM compiler (design sketch)

> Status: **sketch, not plan.** Captured during SpecTec scoping (2026-06-05). Not on the
> near-term roadmap; revisit when (a) a concrete SML program needs to run under our trust
> model, or (b) we want an independent executor mirror for OCaml-via-`wasm_of_ocaml`.

## North star

A from-scratch, **maximally-naive** ML→WASM compiler in Rust. Targets a small, auditable
trusted core (~3–8K LoC) rather than competing with mature compilers on perf or coverage.
Mature compilers (`wasm_of_ocaml`, MLton-wasm) ride alongside as **untrusted optimised
mirrors**; agreement between naive and mature on test inputs discharges to consilience.

## Why this fits the architecture

Three invariants from `AGENTS.md` / `ARCHITECTURE.md` converge on this answer:

1. **§5.2 HAZARD (spec-level independence).** `wasm_of_ocaml` and MLton-wasm share
   academic OCaml/SML lineage. A from-scratch Rust compiler is the **independent executor
   mirror** §5.2 demands. With it, "OCaml/SML semantics" becomes a consilience claim
   between two genuinely different compilers, not a leap of faith on one.

2. **TCB / "simple trusted core + clever untrusted machinery."** A small naive compiler
   is auditable; the meaning-axiom "this compiler respects ML semantics" is eventually
   *provable* against the Definition of SML — approximately unprovable for the mature
   compilers. The naive compiler is the **silvered node** in the ML→WASM segment of the
   executor graph.

3. **§2.6 "Derive, don't trust."** Language-layer analogue: keep the trusted compilation
   core minimal; promote to a fast/mature compiler only where measurement shows the win.
   Same posture as `pair`/`unit`/`DOWHILE` vs derived `sum`/`option`/`num`.

The architecturally-correct framing isn't "naive instead of mature" — it's **naive as
silvered node, mature as untrusted optimised mirror.**

## Target choices: stay high-level

Lean on the WASM proposals that are now standard or near-standard. Naive in *compiler*
logic, not naive in *codegen target*.

| Concern | Choice | Notes |
|---|---|---|
| **Memory management** | **WasmGC** (`(ref ...)`, struct/array types) | No hand-rolled Cheney collector; let the engine do it. Simpler, less runtime to audit, ~free perf. |
| **Exceptions** | **WASM Exception Handling** (`try`/`catch`/`throw`) | ML exceptions map directly. No result-sum encoding gymnastics. |
| **Tail calls** | **WASM tail-call proposal** (`return_call`, `return_call_indirect`) | Required for proper ML semantics; trampolines are a hack we shouldn't carry. |
| **Threads** | `wasm32-wasip1-threads` (already our engine baseline) | Match existing covalence-wasm config. |
| **Value representation** | WasmGC structs per ADT; per-constructor struct type; tagged with the constructor index | No universal `(tag, slot1, slot2)` cell. Lets the engine type-check heap accesses. |
| **Closures** | WasmGC struct `(funcref code, ref env)`; env is a per-closure-shape struct | Closure-conversion the obvious way. Always curried in v0. |
| **Pattern matching** | Naive linear case analysis | Decision-tree optimisation deferred. |
| **Polymorphism** | Type-erase after HM; values uniformly `anyref` at the boundaries | No monomorphisation. |
| **Modules** | **Incremental.** v0 has none; later add structures, then signatures, then functors | See "Roadmap" below. |

The engine requirement: WasmGC + EH + tail calls. All three are shipped in modern engines
(wasmtime, v8, SpiderMonkey) and supported by `wasm-encoder`. covalence-wasm needs to
expose them through the `ModuleBuilder` API — verify before committing.

## Source language: SML

**SML, not OCaml.** Three reasons:

1. Formal Definition exists (Milner/Tofte/Harper/MacQueen '97) — the meaning-axiom has a
   precise target.
2. No GADTs / OO / first-class modules / polymorphic variants — the core language is
   dramatically smaller than OCaml.
3. MLton-wasm exists as the optimised mirror; consilience pair `(naive-Rust-SML, MLton)` is
   achievable today.

OCaml programs (SpecTec, HOL Light) ride `wasm_of_ocaml` and never enter the naive path
directly. Where critical, port the data-consumer piece to SML and run *that* under the
trusted pipeline.

## Roadmap (incremental, with explicit checkpoints)

Each phase ships an artifact and earns trust before the next begins.

| Phase | Adds | Approx LoC | Checkpoint |
|---|---|---|---|
| **v0 — Core ML** | ADTs, HM, let-poly, patterns, records, `ref`/`array`, exceptions, basic basis (`List`/`String`/`Int`/`Array`/`IO`) | ~2–3K Rust + ~1–2K SML basis | Runs an SML interpreter (HaMLet-style); round-trips OpenTheory article reader |
| **v1 — Structures + signatures** | Module-level definitions, opaque/transparent ascription, sharing constraints (basic) | +1–2K | Compiles idiomatic single-functor-free SML libraries |
| **v2 — Functors** | Generative functors with the SML '97 semantics | +1–2K | Compiles HaMLet itself; can host MLton-style libraries |
| **v3 — Bootstrap multiplier** | SML-interpreter-in-SML compiled by naive → silvered eval node | (no new compiler code) | Any SML program runs under a single silvered node, regardless of compiler coverage |

Skip indefinitely (or push to "if we ever need it"): polymorphic equality (require explicit
`eq`), sharing constraints in their full generality, the SML basis bits that touch
`Posix`/`Socket` (WASI substitutes only).

## Cost budget

| Component | Size | Difficulty |
|---|---|---|
| Lexer + parser | 1–2K LoC | Easy |
| HM type checker (Core, no modules) | ~500 LoC | Medium |
| Codegen → WasmGC | 500–1500 LoC | Easy-medium (most of the work goes into picking the right WasmGC struct shapes) |
| Runtime + WASI glue (much smaller without hand-rolled GC) | ~200 LoC Rust | Easy |
| Basis library | 1–3K LoC of pure SML + thin shims | The actual bulk of work |
| **Total v0** | **3–6K LoC** | **2–3 months focused** |
| Module system increments | +2–4K | +2–4 months across phases |

## Bootstrap multiplier (phase v3)

Once the naive compiler exists, write a small **SML interpreter in SML** (~500 LoC; HaMLet
or similar), compile it once with the naive compiler, and now any SML program runs under

```
(naive-Rust→WASM) ∘ (engine) ∘ (SML-interp-in-WASM)
```

Catastrophically slow, but it's a **single silvered node that can evaluate the entire SML
language** — including parts the direct compiler doesn't handle. Trust anchor for
consilience checks against MLton/wasm_of_ocaml.

Same trick available for OCaml later: tiny OCaml interpreter written in SML, compiled
through naive pipeline, becomes the silvered-node evaluator for OCaml programs.

## Crate layout (when we get there)

- **`covalence-ml`** — the naive Rust→WASM compiler + minimal runtime + basis library.
  Self-contained, no OCaml deps. Outputs `.wasm` modules consumable by `covalence-wasm`.
  The trusted artifact.
- **`covalence-ml-mirror`** (or feature flags on `covalence-ml`) — thin orchestration
  around MLton-wasm and `wasm_of_ocaml`: build them, package outputs, run them as the
  *untrusted optimised mirror* via the same WASM oracle interface. Disagreement = test
  failure or oracle relation conflict surfaced through the kernel.

The two crates expose the same surface: "run this ML program on this input"; the kernel
sees them as two different oracle implementations of the same relation, and consensus over
them is straightforward §5.2 consilience.

## Open questions (defer until v0 starts)

- WasmGC type-system mapping: how to share struct types across compilation units (single
  module per program, or proper linking?).
- Exception type representation under WasmGC: tags carry struct-typed payloads?
- How much of the SML basis is *required* for our actual ML use cases vs nice-to-have?
- Naive compiler self-host: not a v0 goal; revisit after v3.
- Verification target: Definition of SML '97 is the obvious candidate, but a custom
  Covalence-ML semantics with HOL-level definitions might fit our architecture better
  (and avoid the SML standard's quirks like value restriction). Decide when we have
  someone actually proving compiler correctness.

## Out of scope (deliberate)

- **OCaml as a source language.** No canonical formal semantics; the meaning-axiom
  would be informal forever. OCaml programs ride `wasm_of_ocaml`, untrusted.
- **Poly/ML / Isabelle execution.** Architecturally subsumed by our arena-freeze
  mechanism (same "snapshot elaborated state" trick, done content-addressed). Isabelle
  *results* (theory exports / OpenTheory articles) ingest into arenas; Isabelle *the
  process* does not run in our sandbox. See `opentheory-define-type-op` memory.
- **Performance work.** Naive is the point. If `wasm_of_ocaml`-equivalent perf becomes
  necessary for an ML program, that program is the wrong fit for the trusted pipeline —
  put it on the mirror instead.
