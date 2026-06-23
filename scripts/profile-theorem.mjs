#!/usr/bin/env bun
/**
 * Profile the derivation of a SINGLE Metamath theorem **in depth** under
 * callgrind, to find the hot spots of a specific slow proof (e.g. set.mm's
 * `mulsass`). With `CACHE=1` it adds full cache simulation — the same D1/LL
 * cache-miss data cachegrind produces, *plus* call-graph attribution (callgrind
 * is cachegrind + a call graph), so it is the in-depth per-theorem profiler.
 *
 * It builds the `mm_import_bench` example (release) and runs its `--only
 * <label> <reps>` mode under valgrind/callgrind, then annotates the result:
 * total instructions, the top self-cost functions, and the top inclusive
 * functions (filtered to covalence + allocator). Final JSON goes to stdout;
 * everything else to stderr.
 *
 * set.mm is auto-downloaded to a temp cache if not found (see `_setmm.mjs`).
 *
 * Usage:
 *   bun scripts/profile-theorem.mjs [label] [reps] [set_mm_path]
 *   bun run profile:theorem                          # via package.json
 *     label        theorem to derive          [default mulsass]
 *     reps         extra timed derivations     [default 0 ⇒ just the 1 warmup
 *                  derive is profiled — fewest instructions for callgrind]
 *     set_mm_path  explicit set.mm (else $COV_SET_MM, else download)
 *
 *   CACHE=1  → add cache simulation (cachegrind-style D1/LL miss counts).
 *             Slower; off by default.
 *
 * NOTE: callgrind runs ~20–40× slower than native. A theorem that takes 138 s
 * natively will take ~1 h here — run it in the background.
 */

import { spawnSync, which } from "bun";
import { existsSync } from "node:fs";
import { ensureSetMm, buildBench } from "./_setmm.mjs";

const LABEL = process.argv[2] ?? "mulsass";
const REPS = process.argv[3] ?? "0";
const CACHE = process.env.CACHE === "1";
const log = (...a) => console.error("[profile-theorem]", ...a);

for (const tool of ["valgrind", "callgrind_annotate"]) {
  if (!which(tool)) {
    log(`required tool not found: ${tool}`);
    process.exit(1);
  }
}

const SET_MM = await ensureSetMm(process.argv[4]);
const bin = buildBench();

// 2. Run the single-theorem derivation under callgrind.
const out = `/tmp/cov-theorem.${LABEL}.callgrind`;
const cmd = [
  "valgrind",
  "--tool=callgrind",
  `--callgrind-out-file=${out}`,
  `--cache-sim=${CACHE ? "yes" : "no"}`,
  "--branch-sim=no",
  bin,
  SET_MM,
  "--only",
  LABEL,
  REPS,
];
log(`profiling ${LABEL} (reps=${REPS}, cache-sim=${CACHE})… this is SLOW (~20-40x).`);
log(cmd.join(" "));
const run = spawnSync(cmd, { stdout: "pipe", stderr: "inherit" });
if (!existsSync(out)) {
  log("callgrind produced no output");
  process.exit(run.exitCode ?? 1);
}

// 3. Annotate.
const irefs = spawnSync(["grep", "-m1", "summary:", out]).stdout.toString().trim();
const total = Number(irefs.split(/\s+/)[1] ?? 0); // `summary: <Ir> [<cache cols>]`
const annotate = (inclusive) =>
  spawnSync([
    "callgrind_annotate",
    `--inclusive=${inclusive ? "yes" : "no"}`,
    "--threshold=90",
    out,
  ]).stdout.toString();

// Parse the "Ir  file:function" table into {ir, pct, fn} rows.
function topFns(text, n) {
  const rows = [];
  for (const line of text.split("\n")) {
    const m = line.match(/^\s*([\d,]+)\s*\(\s*([\d.]+)%\)\s+(.*)$/);
    if (!m) continue;
    const fn = m[3].replace(/\s*\[.*$/, "").replace(/^\?{3}:/, "");
    rows.push({ ir: Number(m[1].replace(/,/g, "")), pct: Number(m[2]), fn });
    if (rows.length >= n) break;
  }
  return rows;
}

const self = topFns(annotate(false), 20);
const incl = topFns(annotate(true), 20).filter((r) => /covalence|beta_nf|subst|type_of|alloc/.test(r.fn));

log("=== top self-cost ===");
for (const r of self.slice(0, 12)) log(`  ${r.pct.toFixed(2).padStart(6)}%  ${r.fn}`);

const commit = spawnSync(["git", "rev-parse", "--short", "HEAD"]).stdout.toString().trim() || null;
console.log(
  JSON.stringify(
    {
      schema: "covalence.profile-theorem/1",
      commit,
      label: LABEL,
      reps: Number(REPS),
      cache_sim: CACHE,
      total_ir: total,
      callgrind_out: out,
      top_self: self,
      top_inclusive: incl,
    },
    null,
    2,
  ),
);
