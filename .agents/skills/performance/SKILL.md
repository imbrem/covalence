---
name: performance
description: How to profile and optimize covalence — flamegraphs, callgrind/cachegrind, and the scaling-first methodology for finding super-linear work
disable-model-invocation: true
---

# Performance work in covalence

The bottleneck is almost never where a flat profile first suggests. Work
**scaling-first**: confirm the algorithm is the right complexity *before*
shaving constants.

## The golden rule: a log-normal time distribution means hidden super-linearity

If per-item times (e.g. per-theorem import times — see the `slowest` / `p99`
fields from `profile:import`) look **log-normal / heavy-tailed**, there is still
**super-linear-per-item work**. A correct, linear(-ithmic) pipeline produces a
tight distribution. Do not declare a heavy tail "fundamental" until you've
checked the scaling.

**How to find it:**
1. Pick a *family* of items of increasing size (e.g. `yonedalem1` …
   `yonedainv`, or sort theorems by proof length).
2. Measure **work-per-unit-size** — `time / size`, and counts like
   `allocs / size`, not just total time. If per-unit cost *grows* with size →
   super-linear. (Plot it; ≈O(size^1.x) shows up immediately.)
3. **Instrument the suspected driver** (a thread-safe `AtomicU64` counter bumped
   in the hot function, read via a temp `pub fn …_stats()` + a temp re-export,
   printed from the bench). Compare the count's growth vs. size. The function
   whose *count-per-size grows* is the culprit — not necessarily the one with
   the highest flat self-%.
4. Rule out red herrings by counting: the highest flat-% function often just
   *rides along* (e.g. `type_of_in` rose because something else rebuilt terms it
   then had to re-type). Find what *drives* the count.
5. Fix the super-linearity (usually: **cache/memoize a result that's rebuilt per
   item**, or **skip unchanged subtrees** via a cached summary). Re-measure the
   per-unit cost — it should flatten.
6. **Strip all instrumentation** before committing; validate the TCB with
   `cargo test -p covalence-core` and (for the importer) a full `set.mm` import
   with **0 failures**.

Each fix tends to *unmask the next* super-linearity, so re-check the
distribution after every win.

## Tools (all auto-download set.mm to a temp cache if missing)

| command | what | when |
|---|---|---|
| `bun run profile:flame [limit] [workers] [freq]` | **flamegraph** of the whole set.mm import (`perf record` → SVG at `/tmp/cov-import-flame.svg`) + top-self summary on stderr + JSON | "where does import time go across the corpus?" |
| `bun run profile:theorem [label] [reps]` (`CACHE=1`) | **in-depth single-theorem** profile under callgrind; `CACHE=1` adds cachegrind D1/LL cache-miss simulation (callgrind = cachegrind + call graph) | drill into one slow proof's hot spots / cache behaviour |
| `bun run profile:import [limit]` | import timing, throughput, **per-theorem distribution** (median/p99/slowest), `perf stat` counters (IPC, cache), peak RSS | check the distribution; spot the slowest theorems |
| `bun run profile:init` | the `init/` kernel-bootstrap profile | kernel/defs bootstrap perf |
| `bun run bench:acl2` | deterministic ACL2 admission/proof families; stable JSON, correctness-first score, scaling exponents | baseline or gate ACL2 optimization/autoresearch |

Shared helper `scripts/_setmm.mjs` resolves set.mm: explicit arg → `$COV_SET_MM`
→ download to `${TMPDIR}/covalence-set.mm` (cached). `buildBench()` builds the
`mm_import_bench` example.

The bench binary (`crates/kernel/hol/traits/examples/mm_import_bench.rs`) modes:
`<mm> [limit] [workers]` (full parallel import) and `--only <label> [reps]`
(single theorem on one thread, persistent `ClauseCache` like the real import;
`--only-cons` routes through a `HashCons` to test interning).

## ACL2 autoresearch gate

`bun run bench:acl2` builds a release-only measurement driver, excludes build
and fixed session-bootstrap time, and measures increasing admission and
certificate-proof workloads. It emits `covalence.acl2-performance.v1` JSON with
raw nanosecond samples, median/p95/max, cost per work unit, log-log scaling
exponents, correctness counts, and a lexicographic score. The score orders
correct samples first, scaling second, and speed third; use the explicit
components rather than comparing the packed number across workload revisions.

Save a baseline and gate a candidate on the same quiet machine:

```sh
bun run bench:acl2 -- --out /tmp/acl2-main.json --reps 9
bun run autoresearch:acl2 -- --baseline /tmp/acl2-main.json \
  --max-slowdown 1.10 --max-exponent-regression 0.10 --timeout-ms 120000
```

Exit zero means all cases remained correct and neither regression threshold was
crossed. `--system-counters` adds peak RSS and perf counters when available,
falling back to an ordinary timed run when host permissions reject them.
Machine identity is recorded because wall time is not portable. An autoresearch
loop should retain a mutation only after this gate passes and the score improves;
profile the retained candidate before optimizing a flat hotspot.

## perf / valgrind notes for this codebase

- Always `--call-graph=dwarf` (`-g`): Rust release lacks frame pointers.
- `Term::cmp`/`type_of_in` are **recursive**, so perf's caller attribution
  collapses into the recursion — use the **count-instrumentation** method above
  to find callers, not the perf caller graph.
- callgrind is ~20–40× slower; a 138 s theorem ≈ 1 h. Run in the background and
  use `reps=0` (profiles just the one warmup derive).
- The allocator shows as `_int_malloc` / `_int_free_chunk` / `malloc_consolidate`
  / `cfree` / `drop_in_place` / `Arc::drop_slow` — sum these for "allocation %".

## Settled findings (don't re-litigate)

- **A faster allocator (mimalloc/jemalloc) does NOT help the import** — tested on
  the full corpus incl. the heavy tail (~349 s vs ~350 s). The ~6× single→24-
  worker blowup is memory-**bandwidth/volume** contention, not malloc-lock
  contention. The lever is *reducing allocation volume*, not the allocator.
- **Interning during replay (`HashCons`) makes single derives ~3× slower** — the
  `Hash`/structural cost of hashing huge terms outweighs the sharing. Use a
  cheap cached discriminator (the 16-bit term fingerprint) for fast `cmp`/`eq`
  instead.

See **metamath-performance** for the import pipeline specifics and the history
of fixes (packrat parser, term fingerprint, `$e` open-form cache, …).
