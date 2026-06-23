#!/usr/bin/env bun
/**
 * Import all of set.mm under `perf record` and produce a **flamegraph** of the
 * Metamath → HOL import, plus a textual top-functions summary. The flamegraph
 * is the go-to artifact for finding where import time goes across the whole
 * corpus (vs. `profile:theorem`, which drills into one theorem).
 *
 * set.mm is auto-downloaded to a temp cache if not found (see `_setmm.mjs`).
 *
 * Usage:
 *   bun run profile:flame [limit] [workers] [freq] [set_mm_path]
 *   bun scripts/flamegraph-import.mjs [limit] [workers] [freq] [set_mm_path]
 *     limit    theorems to import (0 = all)            [default 0]
 *     workers  import worker threads (0 = auto)        [default 0]
 *     freq     perf sampling frequency (Hz)            [default 199]
 *     set_mm_path  explicit set.mm (else $COV_SET_MM, else download)
 *
 * Output:
 *   /tmp/cov-import.perf        raw perf.data
 *   /tmp/cov-import-flame.svg   the flamegraph (open in a browser)
 *   stdout: JSON { svg, total_samples, top_self: [...] }
 *
 * NOTE: a full import is ~2 min; perf adds overhead and a multi-hundred-MB
 * perf.data. Lower `freq` (e.g. 99) or set a `limit` for quicker turnaround.
 * The first 5000 theorems are tiny — for the heavy tail use limit 0 (all).
 */
import { spawnSync, which } from "bun";
import { existsSync } from "node:fs";
import { ensureSetMm, buildBench } from "./_setmm.mjs";

const LIMIT = process.argv[2] ?? "0";
const WORKERS = process.argv[3] ?? "0";
const FREQ = process.argv[4] ?? "199";
const SET_MM_ARG = process.argv[5];
const log = (...a) => console.error("[flame-import]", ...a);

for (const tool of ["perf", "stackcollapse-perf.pl", "flamegraph.pl"]) {
  if (!which(tool)) {
    log(`required tool not found: ${tool}`);
    process.exit(1);
  }
}

const setmm = await ensureSetMm(SET_MM_ARG);
const bin = buildBench();

const perfData = "/tmp/cov-import.perf";
const svg = "/tmp/cov-import-flame.svg";

// 1. Record. dwarf call-graphs so Rust release frames unwind without frame ptrs.
log(`perf record (freq=${FREQ}Hz) importing ${LIMIT === "0" ? "ALL" : LIMIT} theorems…`);
const rec = spawnSync(
  [
    "perf", "record", "-F", FREQ, "-g", "--call-graph=dwarf",
    "-o", perfData, "--", bin, setmm, LIMIT, WORKERS,
  ],
  { stdout: "inherit", stderr: "inherit" },
);
if (!existsSync(perfData)) {
  log("perf produced no data");
  process.exit(rec.exitCode ?? 1);
}

// 2. Collapse stacks → flamegraph SVG.
log("collapsing stacks → flamegraph…");
const script = spawnSync(["perf", "script", "-i", perfData], { maxBuffer: 1 << 30 });
const folded = spawnSync(["stackcollapse-perf.pl"], {
  stdin: script.stdout,
  maxBuffer: 1 << 30,
}).stdout;
spawnSync(["flamegraph.pl", "--title", "set.mm import", "--width", "1600"], {
  stdin: folded,
  stdout: Bun.file(svg),
});
log(`wrote ${svg}`);

// 3. Textual top-self summary (so agents get signal without opening the SVG).
const report = spawnSync(
  ["perf", "report", "-i", perfData, "--stdio", "--no-children", "--percent-limit", "0.5"],
  { maxBuffer: 1 << 30 },
).stdout.toString();
const top = [];
for (const line of report.split("\n")) {
  const m = line.match(/^\s*([\d.]+)%\s+\S+\s+\S+\s+\[\.\]\s+(.*)$/);
  if (m) top.push({ pct: Number(m[1]), fn: m[2].trim() });
  if (top.length >= 25) break;
}
const totalSamples = (folded.toString().match(/ (\d+)$/gm) ?? []).reduce(
  (a, s) => a + Number(s.trim()),
  0,
);

log("=== top self-cost ===");
for (const r of top.slice(0, 15)) log(`  ${r.pct.toFixed(2).padStart(6)}%  ${r.fn.slice(0, 90)}`);

const commit = spawnSync(["git", "rev-parse", "--short", "HEAD"]).stdout.toString().trim() || null;
console.log(
  JSON.stringify(
    { schema: "covalence.flamegraph-import/1", commit, limit: Number(LIMIT), freq: Number(FREQ), svg, perf_data: perfData, total_samples: totalSamples, top_self: top },
    null,
    2,
  ),
);
