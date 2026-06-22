#!/usr/bin/env bun
/**
 * Benchmark the Metamath → HOL import and emit a single machine-readable JSON
 * object to stdout: for each database (hol.mm, and a prefix of set.mm) the parse
 * time, parallel-import time, throughput, ok/failed counts, the per-theorem
 * timing distribution (median / p99 / slowest), plus hardware counters
 * (`perf stat`) and peak memory (GNU `time -v`).
 *
 * Usage:
 *   bun scripts/profile-import.mjs [set_limit] [set_mm_path]
 *   bun run profile:import                         # via package.json
 *     set_limit    theorems of set.mm to import (0 = ALL the whole thing)  [default 5000]
 *     set_mm_path  path to set.mm                  [default $COV_SET_MM, else skip set.mm]
 *
 * Everything except the final JSON goes to stderr, so it pipes into `jq`:
 *   bun run profile:import 0 ~/set.mm | jq '.runs[] | {db, import_ms, throughput_per_s}'
 *
 * `perf` and GNU `time` are optional — if missing, those fields degrade to null.
 */

import { spawnSync, which } from "bun";
import { existsSync, readFileSync } from "node:fs";

const SET_LIMIT = process.argv[2] ?? "5000"; // "0" = whole set.mm
const SET_MM = process.argv[3] ?? process.env.COV_SET_MM ?? "";
const HOL_MM = "crates/covalence-metamath/tests/fixtures/hol.mm";
const log = (...a) => console.error("[profile-import]", ...a);

// ---------------------------------------------------------------------------
// 1. Build the import-bench example (release) — the profiled run is the run.
// ---------------------------------------------------------------------------
log("building example mm_import_bench (release)…");
const build = spawnSync(
  ["cargo", "build", "-p", "covalence-hol", "--example", "mm_import_bench", "--release"],
  { stdout: "inherit", stderr: "inherit" },
);
if (build.exitCode !== 0) {
  log("build failed");
  process.exit(build.exitCode ?? 1);
}
const targetDir =
  spawnSync(["cargo", "metadata", "--format-version=1", "--no-deps"]).stdout.toString().match(
    /"target_directory":"([^"]+)"/,
  )?.[1] ?? "target";
const bin = `${targetDir}/release/examples/mm_import_bench`;
if (!existsSync(bin)) {
  log(`bench binary not found: ${bin}`);
  process.exit(1);
}

const perf = which("perf");
const gtime = which("time"); // GNU time (NOT the bash builtin)

// ---------------------------------------------------------------------------
// Run one import under perf stat + GNU time -v, merging the bench JSON with the
// counters and peak RSS.
//   perf stat -j -o … -- time -v -o … -- <bin> <mm> [limit] [workers]
// ---------------------------------------------------------------------------
function runOne(db, mmPath, limit) {
  const perfOut = `/tmp/profile-import.${db}.perf.json`;
  const timeOut = `/tmp/profile-import.${db}.time.txt`;
  const inner = [bin, mmPath, String(limit), "0"]; // workers 0 = auto
  let cmd = inner;
  if (gtime) cmd = [gtime, "-v", "-o", timeOut, ...cmd];
  if (perf) cmd = [perf, "stat", "-j", "-o", perfOut, "--", ...cmd];

  log(`importing ${db} (limit ${limit})…`);
  const run = spawnSync(cmd, { stdout: "pipe", stderr: "pipe" });
  process.stderr.write(run.stderr.toString()); // keep [import-bench] lines visible

  // The bench prints one JSON object on stdout.
  let result = {};
  try {
    result = JSON.parse(run.stdout.toString().trim().split("\n").pop() ?? "{}");
  } catch {
    log(`${db}: could not parse bench JSON`);
  }

  // perf stat counters (newline-delimited JSON, one per event).
  const counters = {};
  if (perf && existsSync(perfOut)) {
    for (const line of readFileSync(perfOut, "utf8").split("\n")) {
      const s = line.trim();
      if (!s.startsWith("{")) continue;
      let o;
      try {
        o = JSON.parse(s);
      } catch {
        continue;
      }
      const event = o.event ?? o["event-name"];
      const raw = o["counter-value"] ?? o["counter_value"];
      if (event && raw !== undefined && raw !== "<not counted>" && raw !== "<not supported>") {
        const v = Number(raw);
        if (Number.isFinite(v)) counters[String(event).replace(/:.*/, "")] = v;
      }
    }
  }

  // GNU time -v peak RSS + cpu.
  let max_rss_kb = null;
  let user_s = null;
  let sys_s = null;
  if (gtime && existsSync(timeOut)) {
    const text = readFileSync(timeOut, "utf8");
    const grab = (re) => {
      const m = text.match(re);
      return m ? Number(m[1]) : null;
    };
    max_rss_kb = grab(/Maximum resident set size \(kbytes\):\s*(\d+)/);
    user_s = grab(/User time \(seconds\):\s*([\d.]+)/);
    sys_s = grab(/System time \(seconds\):\s*([\d.]+)/);
  }

  const cyc = counters["cpu-cycles"] ?? counters.cycles;
  const ipc = counters.instructions && cyc ? Number((counters.instructions / cyc).toFixed(3)) : null;

  return {
    db,
    exit_code: run.exitCode,
    ...result,
    max_rss_kb,
    cpu: { user_s, sys_s },
    counters,
    ipc,
  };
}

// ---------------------------------------------------------------------------
// 2. Run hol.mm (always) + set.mm (if a path is available).
// ---------------------------------------------------------------------------
const runs = [];
if (existsSync(HOL_MM)) runs.push(runOne("hol.mm", HOL_MM, 0));
else log(`hol.mm fixture missing at ${HOL_MM} — skipping`);

if (SET_MM && existsSync(SET_MM)) {
  runs.push(runOne("set.mm", SET_MM, Number(SET_LIMIT)));
} else {
  log("set.mm not provided (pass a path or set $COV_SET_MM) — skipping");
}

// ---------------------------------------------------------------------------
// 3. Emit the combined JSON.
// ---------------------------------------------------------------------------
const commit = spawnSync(["git", "rev-parse", "--short", "HEAD"]).stdout.toString().trim() || null;
console.log(
  JSON.stringify(
    {
      schema: "covalence.profile-import/1",
      commit,
      timestamp: new Date().toISOString(),
      set_limit: Number(SET_LIMIT),
      runs,
    },
    null,
    2,
  ),
);
