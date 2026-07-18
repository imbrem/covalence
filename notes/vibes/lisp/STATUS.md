+++
id = "N001E"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:claude"
at = "2026-07-13T21:35:45+01:00"
source = "legacy"
agent = "claude"
harness = "claude"
+++

# Lisp demo — STATUS

*Branch `lisp-demo`. Agent-authored. Honest snapshot of what is actually built,
what is deferred, and where we are on the tower.*

## TL;DR

A working, kernel-proven **Little Schemer ch1** REPL ships. Every value the
`/lisp` page prints is read off a genuine kernel theorem `⊢ program = value`,
composed from the carved `sexpr` carrier's proved computation laws — **no new
trusted kernel rules**. It is the **equational special case** of the aspirational
`Reduces` step-relation: ch2 recursion, non-termination, and the parametric
`Repr × Semantics × Strategy` refactor are all still ahead.

Peers `/forsp` (real, over `covalence-forsp`) and `/forth` (a "coming soon"
placeholder) ride alongside; only `/lisp` is kernel-theorem-backed today.

## Architecture as built

Three crates, bottom-up:

**`covalence-repl-core`** (`crates/lib/repl-core`) — paradigm-neutral, no kernel
dep, `#![forbid(unsafe_code)]`, wasm-clean. Two traits:

- `Repl` — the lifecycle core: `State`/`Term`/`Eval` + per-phase error types,
  `start`/`parse`/`eval`/`next`/`show`, and a default `step = parse;eval;show`.
  Nothing S-expr- or kernel-specific (a Forth/Haskell/SMT REPL would implement
  the same trait). No concrete impl lives here by design.
- `ReductionStrategy` — the swappable seam for **how a reduction is proved**:
  `reduce(term) -> Result<Thm, _>` returning a kernel theorem `⊢ term = value`.
  Generic over `Term`/`Thm` so the crate stays kernel-agnostic; a future
  proven-WASM-interpreter strategy plugs in returning the same shape.

**`covalence-lisp`** (`crates/lang/lisp`):

- `Lisp` — the surface trait. Forth-style atom resolution (dictionary → numeral
  → symbol) as `resolve_symbol`/`resolve_number`/`resolve_string`, plus `nil`/
  `cons` and a default `lower` folding a parsed `SExpr` into a `Term`.
  Kernel-agnostic.
- `reader` — thin wrapper over `covalence_sexp::parse`.
- `hol` (feature `hol`) — the concrete kernel instance. `LispHol` lowers
  S-expressions to carved `sexpr` kernel terms (atoms via `atom (mk_blob …)`,
  lists via `scons`/`snil`); `SymbolicStrategy` is the `ReductionStrategy` that
  proves single-step projections `car/cdr (cons h t)` via
  `CarvedSExpr::proj_scons`.
- `eval` (feature `hol`) — the multi-step `Evaluator`: normalizes a nested closed
  ch1 program to weak normal form, chaining the carrier's computation laws with
  `Thm::trans` + congruence into a single `⊢ program = value`. Handles `quote`,
  `car`, `cdr`, `cons`, `atom?`, `consp`/`pair?`, `null?`, `eq?`.
- `session` (feature `hol`) — the concrete `Repl` instance. `eval_cell` runs
  parse → eval (→ a `Reduction`, i.e. the theorem + value) → `show`, which
  renders **only** the value carried in the `Reduction` (the theorem's RHS). The
  **honesty invariant**: there is no code path that prints a value that did not
  come off a theorem. `#help` / `#show EXPR` directives.

**web endpoints** (`crates/kernel/web/src/lib.rs`, wasm32-unknown-unknown +
wasm-bindgen) — `lisp_eval_cell` (fresh `Session` per call), `forsp_eval_cell`
(over `covalence-forsp`), `forth_eval_cell` (stub `{ok:false}`), each returning
the `{ok, result?, error?}` JSON convention. SvelteKit routes `/lisp`, `/forsp`,
`/forth` mirror `/haskell`.

## What works

- **Kernel-proven ch1 REPL.** `quote`/`car`/`cdr`/`cons`/`atom?`/`consp`/`null?`/
  `eq?` over quoted atom-lists; every printed value is the RHS of a hyps-free
  `⊢ program = value` theorem, auditable via `#show`.
- **26 integration tests** (`tests/little_schemer_ch1.rs`) + the 3 `hol.rs`
  de-risking tests for `SymbolicStrategy`.
- **wasm32 build.** `bun run build:web-kernel` compiles `covalence-forsp`,
  `covalence-lisp`, and the web kernel; wasm-bindgen + wasm-opt run clean.
- **`/lisp` / `/forsp` / `/forth` pages** live, with honesty labeling: `/lisp`
  states it is ch1 primitives (not yet recursion or a metacircular evaluator) and
  that every value is kernel-backed; `/forsp` notes its values are *not* yet
  carried by theorems; `/forth` is a placeholder.

## The tower and where we are

`SExpr → Reduction → Lisp → ACL2` (see [`README.md`](./README.md)):

| Layer | Status |
|---|---|
| **SExpr** | built — `covalence-sexp` surface tree + reader; kernel carved `sexpr` datatype + computation laws. The `carved → sexpr` rename (code-level) is still pending. |
| **Reduction** | **partial** — `ReductionStrategy` seam exists (equational special case); the parametric `Repr × Semantics × Strategy` refactor and the `Reduces` *step-relation* (for non-termination) are not built. |
| **Lisp** | **ch1 only** — reader → resolve → reduce → print + REPL + `/lisp`. No `defun`/env/recursion. |
| **ACL2** | not started. |

## Known gaps / next steps (prioritized)

1. **Route the REPL through the `ReductionStrategy` seam.** Today `Evaluator`
   (`eval.rs`) composes kernel rules **directly**; the `SymbolicStrategy` seam in
   `hol.rs` is only exercised by its own de-risking tests (`LispHol::eval` calls
   it, but `Session`/`eval_cell` bypasses it). Make the seam load-bearing so the
   abstraction actually mediates every reduction — the precondition for a
   drop-in proven-WASM-interpreter strategy.

2. **Parametric `Repr × Semantics × Strategy` + the `Reduces` step-relation +
   streaming (for NON-TERMINATION).** The equational `⊢ input = output` forces
   reduction to be a *function* — it demands an `output`. Recursive ch2 functions
   can diverge, so there is no value to equate to. The right object is a step
   relation `Step ⊆ (State × Term)²` and its closure `Reduces = Step*`, streamed
   lazily so divergence is expressible and non-hanging. See
   [`initial-ideas/parametric-reduction.md`](./initial-ideas/parametric-reduction.md)
   (which supersedes the single-seam minimal-spec) and
   [`initial-ideas/reduction-relations-and-state.md`](./initial-ideas/reduction-relations-and-state.md).

3. **Ch2 recursion.** `defun` special form + a binding environment threaded
   through `Evaluator` + the carved recursor/induction principle (currently
   `pub(crate)` in `covalence-init`) to prove `⊢ f args = value` for recursive
   `f`. Unlocks `lat?`/`member?`/`rember?`/… and, above them, the metacircular
   `eval`/`apply` interpreter (`minimal-spec/implementation-plan.md`).

4. **`carved → sexpr` rename + S-expression-API polish.** Drop the `carved`
   jargon in the *code* (`CarvedSExpr → SExpr`-family, `carved.rs → sexpr.rs`,
   `carved() → sexpr…()`), test-gated, coordinated with the kernel bundle name so
   it does not clash with `covalence_sexp::SExpr`. Plus round-trip property tests
   and the event/`SExpBuilder` fast path (see [`README.md`](./README.md)).

5. **Numeral literals** landed separately on branch `numeral-literals` (today
   `resolve_number` only classifies all-ASCII-digit tokens, which lower to the
   same raw-byte atom as symbols — the split is cosmetic here).
