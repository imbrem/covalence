# Metamath import performance — results log

Performance journal for the Metamath → HOL import (`covalence-metamath` parse +
`covalence-hol::metalogic::mm_database` "construct, don't trust" replay).
Methodology and tooling live in the **performance** / **metamath-performance**
skills; this file is the concrete record: numbers, the history of fixes, the
current bottleneck, and what's next.

Benchmark: import all of `set.mm` (~47k `|-` theorems) via the
`mm_import_bench` example. Hardware varies; treat numbers as ratios. Profiling
scripts (all auto-download set.mm to a temp cache):

| command                                          | purpose                                                                                   |
| ------------------------------------------------ | ----------------------------------------------------------------------------------------- |
| `bun run profile:import [limit]`                 | import timing, throughput, per-theorem distribution (median/p99/`slowest[]`), `perf stat` |
| `bun run profile:flame [limit] [workers] [freq]` | flamegraph of the whole import → `/tmp/cov-import-flame.svg` + top-self                   |
| `bun run profile:theorem <label>` (`CACHE=1`)    | in-depth single-theorem callgrind (`CACHE=1` = cachegrind D1/LL + call graph)             |

`mm_import_bench <mm> [limit] [workers]` = full parallel import;
`--only <label> [reps]` = one theorem, single thread, persistent `ClauseCache`
(matches the real import's amortization); `--only-cons` routes through a
`HashCons`.

## Current state (2026-06-23)

- **Full set.mm import: ~145 s, 47391 ok / 0 failed**, ~327 thm/s (24 workers).
  Down from ~350 s; the original worst single theorem was 138 s.
- Distribution: **median ~12.5 ms, p99 ~961 ms, slowest ~14 s** (parallel) /
  **~0.7–1 s single-thread** (fourierdlem103/104/112, dalem51/52, aks6d1c\*).
- The distribution is **still log-normal** ⇒ residual super-linearity remains
  (see "Open bottleneck"). The slowest theorems are ~1 s single-thread; the
  goal is a tight (linearithmic) distribution.

## History of fixes (each unmasked the next — the log-normal trail)

| #   | fix                                                                                                                                                                                                                  | crate          | effect                                                                            |
| --- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | -------------- | --------------------------------------------------------------------------------- |
| 1   | **packrat-memoize the former parser** (`mm_database` `parse`/`try_former`) — backtracking recursive descent was exponential in expression nesting                                                                    | covalence-hol  | `mulsasslem1` 120,250 ms→13 ms; `mulsass` 138 s→14 ms                             |
| 2   | **16-bit structural fingerprint** per term node → O(1) `Term::cmp`/`eq` fast-reject (was 58% of a derive walking shared prefixes; the free-var Bloom can't help — encoded tokens are all free vars, so it saturates) | covalence-core | cantnflem1 cmp 58%→~10%                                                           |
| 3   | **`$e` open-form cache** (`replay_with`) — each reference to an essential hypothesis rebuilt the whole `Closed_L` conjunction (`derivable`→`closed_conj`, O(#clauses)); cache the built slot per label               | covalence-hol  | yonedainv 1057 ms→104 ms; per-step cost flattened; import ~350 s→~145 s           |
| 4   | **type-preserving `open`** (`inst_typed` + `Term::abs_with_ty`) — fuse type computation into substitution, skip the redundant `type_of_in` on closing `Abs`                                                          | covalence-core | ~3–8% on heavy theorems (limited: higher-order terms still re-type open subterms) |
| 5   | **`shift_inner` bvi-skip** — don't rebuild closed subterms when shifting                                                                                                                                             | covalence-core | small; correctness-symmetric with `inst_opt`                                      |

## Open bottleneck (next target)

The heavy tail (Fourier, Desargues `dalem*`, `aks*`) is still super-linear:
**µs/step grows 3.8→25 as proof size grows 1930→28958** (≈ O(size¹·⁷)) across
the `fourierdlem*` family.

Localized via count-instrumentation (perf can't attribute through the recursive
`type_of_in`/`cmp`):

- **97% of allocations are per-step replay**, not the one-time `ClauseCtx`
  build (only ~3%: 124K of 4.45M allocs for fourierdlem103).
- **`replay_allocs / step` grows with proof size** (222→534) — each step builds
  terms proportional to the _accumulated_ expression size. The Fourier proofs
  construct wffs that grow as the proof progresses; term-building volume grows
  with them.
- Flat profile of a heavy theorem: `type_of_in` ~20%, allocator (`_int_malloc`
  - `free` + `drop_in_place` + …) ~30%, `close_at` ~6%, `Term::cmp` ~3%.

**DIAGNOSIS (decisive): it's lost sharing, not inherent term size.** Measured
`derive_allocs` vs the output term's `unique_node_count` (Arc-shared):

| theorem | derive allocs | output unique nodes | ratio |
|---|---|---|---|
| fourierdlem80  |   555 K | 12,370 |  **45×** |
| dalem51        |   672 K | 14,167 |  **47×** |
| yonedainv      |   935 K | 14,078 |  **66×** |
| fourierdlem103 | 4,595 K | 44,811 | **102×** |
| fourierdlem112 | 3,396 K | 28,807 | **118×** |

We allocate **45–118× more term nodes than the final theorem contains**, and the
ratio **grows with proof size** — so the replay is *rebuilding the same
structure over and over* (transient intermediate terms + non-shared duplicate
sub-wffs). Sharing/dedup CAN fix this — it's not solely the arena's job.

**The fix: alloc-free hash-consing during replay.** Two blockers:
1. **DONE** — `HashCons::cons` no longer materialises a candidate `Term` to
   probe: a private `KindRef<'a>(&'a TermKind)` (`Hash` + `Equivalent<Term>`,
   plus a self-consistent `Ord`) looks up by borrowed kind; alloc only on a
   miss. (`TermKind::compute_fp` is now a method.)
2. **TODO** — `Hash for Term` still recurses the kind (O(size)). This is the
   *dominant* cost: with (1) alone, interning a heavy theorem is still **~20–30×
   slower** (fourierdlem103 `--only-cons` 23,951 ms vs `--only` 742 ms),
   because every probe hashes a huge term. Fix: a cheap O(1) lookup key.

**Two ways to get the cheap O(1) probe:**
- **(2a) Cache a wide content hash** (u64, Merkle from children — the 16-bit cmp
  fingerprint is too narrow for a millions-entry map) and hash it in O(1). Grows
  `TermInner` 8 bytes (the fp fit in spare padding; a u64 hash will not). Keeps
  the `IndexSet` + `KindRef` (`Equivalent`) alloc-free probe.
- **(2b, PREFERRED — future direction) Ordered interner (`BTreeSet<Term>`),
  probed alloc-free via a `#[repr(transparent)]` `KindRef` + safe ref-cast.**
  `Term::cmp` already has the O(1) fingerprint fast-path, so an *ordered* set
  probes in O(log n) cheap comparisons — **no hashing, no cached u64, no
  `TermInner` growth**. The probe-alloc-free obstacle (std `BTreeSet`/`Map` only
  probe via `Borrow<Q>`, and a probe key must order *identically* to the stored
  `Term`, i.e. by the cached fingerprint) is solvable: make
  `KindRef` `#[repr(transparent)]` over `TermKind` and use a safe reference-cast
  crate (e.g. `ref-cast`) to obtain `&KindRef` from `&TermKind`, then
  `impl Borrow<KindRef> for Term { fn borrow(&self) -> &KindRef {
  KindRef::ref_cast(self.kind()) } }` with `KindRef: Ord` = fingerprint-then-
  structural (already implemented). Now `set.get(KindRef::ref_cast(kind))`
  probes the `BTreeSet<Term>` alloc-free, in O(log n) O(1)-compares — the best
  of both (alloc-free **and** no hashing **and** no `TermInner` growth). The
  current `KindRef<'a>(&'a TermKind)` (a reference wrapper for the `IndexSet`
  `Equivalent` probe) would become this transparent-newtype form.

**Recommendation:** **(2b)** is now the target — alloc-free + no-hash + no
growth, std `BTreeSet`. (2a) (cached u64 hash on `IndexSet`) is the fallback if
the `repr(transparent)`/ref-cast route hits a snag. Either way, route the replay
through a persistent ordered interner → collapse the 45–118× rebuild ratio
toward ~1× (alloc + its `type_of_in`/`drop` shadow is ~50% of a heavy derive).
Last fallback: a **term arena** attacks the same ~50% from the allocation side.

## Settled findings (do not re-litigate)

- **A faster global allocator (mimalloc/jemalloc) does NOT help** — tested on
  the full corpus incl. the heavy tail (~349 s vs ~350 s). The ~6×
  single→24-worker blowup is memory-**bandwidth/volume** contention, not
  malloc-lock contention. Lever = reduce allocation _volume_, not the allocator.
- **Interning during replay (`HashCons`) makes single derives ~3× slower** with
  the current O(size) `Hash for Term`. Use the cached fingerprint for fast
  `cmp`/`eq` instead.
- **`bj-1`** type connective-replay conclusion mismatches are _importer_
  correctness issues, not perf — verify reproduction without your change before
  blaming perf work. (As of the last full import: 0 failures.)
