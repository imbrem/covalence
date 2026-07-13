---
name: metamath-performance
description: Performance of the Metamath → HOL import (covalence-metamath + covalence-hol metalogic) — pipeline, hotspots, the bench, and the history of super-linearity fixes
disable-model-invocation: true
---

# Metamath import performance

Read **performance** first for the scaling-first methodology and the tools.
This skill is the import-specific map. Concrete numbers + current bottleneck live in `crates/kernel/hol/init/PERF.md` (the results log; update it as you go). Benchmark target: import all of `set.mm`
(~47k `|-` theorems) fast, with **linear-ish per-theorem cost** and 0 failures.

## The pipeline (where time goes)

1. **Parse** (`covalence-metamath::parse`) — one-time, ~0.8 s for set.mm.
2. **Per theorem** (`covalence-init::metalogic::mm_database::derive_theorem*`),
   "construct, don't trust": replay the proof to build a kernel theorem
   `⊢ Derivable_L ⌜S⌝` and check its conclusion against the claimed statement.
   - statements are encoded as flat `mm$concat` chains of `mm$c$…`/`mm$v$…`
     **free-variable leaves** (no HOL binders) — so a big term's free-var Bloom
     saturates and can't discriminate (use the term **fingerprint** instead).
   - each cited `|-` lemma → a `Closed_L` clause; the rule set's `Closed_L d` is
     the conjunction of all cited clauses. Substitution-instance = `Thm::all_elim`
     (β/∀-elim); `imp_elim`/`and_elim` for premises/conjuncts.
   - clauses are compiled once per worker (`ClauseCache`); `Closed d` + its
     conjuncts are built once per theorem (`ClauseCtx`).

## The bench

`crates/kernel/hol/init/examples/mm_import_bench.rs`:
- `<mm> [limit] [workers]` — full parallel import; prints `imported N (ok/failed)`,
  throughput, and a JSON distribution (`median_ms`, `p99_ms`, `slowest[]`).
  `[FAILED] <label>: <err>` is printed per failure.
- `--only <label> [reps]` — derive one theorem on one thread, persistent
  `ClauseCache` (matches the real import's amortization). `--only-cons` routes
  through a `HashCons`.

Find slow theorems from the `slowest[]` array of `profile:import`, then drill in
with `profile:theorem <label>` and flamegraph the whole run with `profile:flame`.

## Known hotspots (current, after the fixes below)

- `type_of_in` — typing closing abstractions at construction (TCB,
  `term_info`). Rides along with allocation volume.
- allocation churn (`Term::alloc` + malloc/free/`drop_in_place`) — ~30% single-
  thread, amplified ~6× under 24-worker contention (bandwidth-bound).
- `Term::cmp` — hyp-set (`Ctx`/`TermSet` = `BTreeSet<Term>`) comparisons.

## History of fixes (each unmasked the next — the log-normal trail)

1. **Packrat-memoize the former parser** (`mm_database` `parse`/`try_former`):
   backtracking recursive descent was exponential in expression nesting.
   `mulsasslem1` 120,250 ms→13 ms; `mulsass` 138 s→14 ms.
2. **16-bit structural fingerprint** on each term node (`covalence-core`
   `term.rs`): O(1) `Term::cmp`/`eq` fast-reject instead of walking shared
   prefixes (was 58% of a derive). Bloom can't do this here (saturates).
3. **`$e` open-form cache** (`mm_database` `replay_with`): each reference to an
   essential hypothesis rebuilt the entire `Closed_L` conjunction
   (`derivable`→`closed_conj`, O(#clauses)) → O(refs·clauses), both growing with
   proof size = the residual super-linear tail. Cache the built `$e` slot by
   label. yonedainv 1057 ms→104 ms; per-step cost flattened to ~linear; full
   import ~350 s→~117 s.
4. **Type-preserving `open`** (`covalence-core` `inst_typed` + `abs_with_ty`):
   fuse type computation into substitution, skip the redundant `type_of_in` on
   closing `Abs`. ~3–8% (limited: higher-order terms still re-type open
   subterms). Trusts substitution type-preservation (audited docstring).
5. **`shift_inner` bvi-skip**: don't rebuild closed subterms when shifting.

## Pitfalls / invariants

- **TCB:** `covalence-core` (`term.rs`, `subst.rs`, `thm/`) is trusted. Any perf
  change there must keep `cargo test -p covalence-core` green AND import set.mm
  with **0 new failures** (a wrong term/type surfaces as a replay conclusion
  mismatch or a downstream rule error). Memory note: kernel/defs/env changes
  must be cargo-test-gated, never merged build-only.
- The `--only` bench amortizes clause encoding via a persistent `ClauseCache`,
  matching the real import — so it measures per-theorem *replay*, not one-time
  parsing/encoding (which dominates a fresh-cache single derive but is amortized
  across the 47k corpus).
- Pre-existing: occasionally a single theorem fails the connective-replay
  conclusion check (e.g. `bj-1` at one point) — that's an importer-correctness
  bug, not perf; check it reproduces *without* your change before blaming perf
  work.
