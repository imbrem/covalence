#!/usr/bin/env bun
/**
 * Profile the `covalence-hol` init test suite and emit a single machine-readable
 * JSON object to stdout: hardware performance counters (`perf stat`), peak
 * memory (GNU `time -v`), per-`.cov`-file evaluation timings and a ranked
 * per-`cached_thm!` breakdown (`COV_PROFILE`), and the libtest pass/fail summary.
 *
 * Usage:
 *   bun scripts/profile-init.mjs [test-filter]    # default filter: "init"
 *   bun run profile:init                           # via package.json
 *
 * Everything except the final JSON goes to stderr, so the result pipes cleanly
 * into `jq` or a regression tracker:
 *   bun run profile:init | jq '{wall_s, max_rss_kb, ipc: .derived.ipc}'
 *
 * Requires `perf` (counters) and GNU `time` (peak RSS); either missing degrades
 * gracefully — the corresponding fields become null/empty.
 */

import { spawnSync, which } from "bun";
import { readFileSync, readdirSync, statSync } from "node:fs";
import { join } from "node:path";

const FILTER = process.argv[2] ?? "init";
const log = (...a) => console.error("[profile-init]", ...a);

// ---------------------------------------------------------------------------
// 1. Build the lib test binary (so the profiled run is the run, not the build).
// ---------------------------------------------------------------------------
log("building covalence-hol lib test binary…");
const build = spawnSync(["cargo", "test", "-p", "covalence-hol", "--lib", "--no-run"], {
  stdout: "inherit",
  stderr: "inherit",
});
if (build.exitCode !== 0) {
  log("build failed");
  process.exit(build.exitCode ?? 1);
}
// Locate the freshly-built lib test binary: the newest executable named
// `covalence_hol-<hash>` (no extension) under `target/debug/deps`. Robust to
// the build being already up to date (cargo then prints no artifact path).
const depsDir =
  (spawnSync(["cargo", "metadata", "--format-version=1", "--no-deps"]).stdout.toString().match(
    /"target_directory":"([^"]+)"/,
  )?.[1] ?? "target") + "/debug/deps";
let bin = "";
let bestMtime = -1;
try {
  for (const name of readdirSync(depsDir)) {
    if (!/^covalence_hol-[0-9a-f]+$/.test(name)) continue; // skip .d/.rlib/.rmeta
    const p = join(depsDir, name);
    const st = statSync(p);
    if (st.isFile() && st.mode & 0o111 && st.mtimeMs > bestMtime) {
      bestMtime = st.mtimeMs;
      bin = p;
    }
  }
} catch (e) { log(`scanning ${depsDir} failed: ${e}`); }
if (!bin) { log(`could not find lib test binary under ${depsDir}`); process.exit(1); }
log(`test binary: ${bin}`);

// ---------------------------------------------------------------------------
// 2. Run it under `perf stat` + GNU `time -v`, with COV_PROFILE on.
//    Nesting: perf stat -- time -v -- <bin> <filter> --nocapture
// ---------------------------------------------------------------------------
const perf = which("perf");
const gtime = which("time"); // GNU time binary (NOT the bash builtin)
const perfOut = "/tmp/profile-init.perf.json";
const timeOut = "/tmp/profile-init.time.txt";

// Single-threaded so the per-`.cov` and counter attribution is deterministic.
const inner = [bin, FILTER, "--nocapture", "--test-threads=1"];
let cmd = inner;
if (gtime) cmd = [gtime, "-v", "-o", timeOut, ...cmd];
if (perf) cmd = [perf, "stat", "-j", "-o", perfOut, "--", ...cmd];

log(`running: ${cmd.join(" ")}`);
const t0 = performance.now();
const run = spawnSync(cmd, {
  env: { ...process.env, COV_PROFILE: "1" },
  stdout: "pipe",
  stderr: "pipe",
});
const wallS = (performance.now() - t0) / 1000;

const runStdout = run.stdout.toString();
const runStderr = run.stderr.toString();
process.stderr.write(runStderr); // keep the run visible/debuggable

// ---------------------------------------------------------------------------
// 3. Parse the three outputs.
// ---------------------------------------------------------------------------

// 3a. perf stat JSON (newline-delimited objects, one per counter event).
const counters = {};
if (perf) {
  try {
    for (const line of readFileSync(perfOut, "utf8").split("\n")) {
      const s = line.trim();
      if (!s.startsWith("{")) continue;
      let o;
      try { o = JSON.parse(s); } catch { continue; }
      const event = o.event ?? o["event-name"];
      const raw = o["counter-value"] ?? o["counter_value"];
      if (event && raw !== undefined && raw !== "<not counted>" && raw !== "<not supported>") {
        const v = Number(raw);
        if (Number.isFinite(v)) counters[String(event).replace(/:.*/, "")] = v;
      }
    }
  } catch { log("perf counters: parse failed"); }
}

// 3b. GNU time -v (peak memory + cpu time).
const time = {};
if (gtime) {
  try {
    const text = readFileSync(timeOut, "utf8");
    const grab = (re) => { const m = text.match(re); return m ? Number(m[1]) : undefined; };
    const rss = grab(/Maximum resident set size \(kbytes\):\s*(\d+)/);
    if (rss !== undefined) time.max_rss_kb = rss;
    const usr = grab(/User time \(seconds\):\s*([\d.]+)/);
    if (usr !== undefined) time.user_s = usr;
    const sys = grab(/System time \(seconds\):\s*([\d.]+)/);
    if (sys !== undefined) time.sys_s = sys;
    const faults = grab(/Minor \(reclaiming a frame\) page faults:\s*(\d+)/);
    if (faults !== undefined) time.minor_page_faults = faults;
  } catch { log("GNU time -v: no output"); }
}

// 3c. COV_PROFILE timings (`[cov-profile] <label>: <Duration>`), normalised to
// ms. Two label kinds share this stream: `cov:<file>` (a `.cov` replay) and a
// bare `<name>` (one `cached_thm!` build). We split them into `cov_files` and a
// ranked `theorems` list — the latter is the per-theorem breakdown that points
// at the next hotspot. Note: timings are *inclusive* (a parent build's time
// covers any nested `cached_thm!` it triggers on first use), so the numbers do
// not partition the total — read them as "wall time to build this, warts and
// all", and subtract a child from its parent when attributing.
const covMs = (s, u) =>
  u === "ns" ? Number(s) / 1e6
  : u === "µs" ? Number(s) / 1000
  : u === "ms" ? Number(s)
  : Number(s) * 1000; // "s"
const cov_files = [];
const theorems = [];
for (const line of runStderr.split("\n")) {
  const m = line.match(/\[cov-profile\] (\S.*?): ([\d.]+)(ns|µs|ms|s)\b/);
  if (!m) continue;
  const ms = Number(covMs(m[2], m[3]).toFixed(3));
  if (m[1].startsWith("cov:")) cov_files.push({ file: m[1].slice(4), ms });
  else theorems.push({ name: m[1], ms });
}
cov_files.sort((a, b) => b.ms - a.ms);
theorems.sort((a, b) => b.ms - a.ms);
// Bound the output: the long tail of sub-millisecond builds is noise.
const TOP_THEOREMS = 40;
const theorems_top = theorems.slice(0, TOP_THEOREMS);
const theorems_total_ms = Number(theorems.reduce((s, t) => s + t.ms, 0).toFixed(3));

// 3d. libtest summary.
let tests = {};
const summary = runStdout.match(
  /test result: \w+\. (\d+) passed; (\d+) failed; (\d+) ignored; \d+ measured; (\d+) filtered out/,
);
if (summary) {
  tests = {
    passed: Number(summary[1]),
    failed: Number(summary[2]),
    ignored: Number(summary[3]),
    filtered_out: Number(summary[4]),
  };
}

// 3e. git commit for provenance.
const commit = spawnSync(["git", "rev-parse", "--short", "HEAD"]).stdout.toString().trim() || null;

// ---------------------------------------------------------------------------
// 4. Emit one machine-readable JSON object on stdout.
// ---------------------------------------------------------------------------
const out = {
  schema: "covalence.profile-init/1",
  commit,
  timestamp: new Date().toISOString(),
  filter: FILTER,
  exit_code: run.exitCode,
  wall_s: Number(wallS.toFixed(3)),
  max_rss_kb: time.max_rss_kb ?? null,
  cpu: { user_s: time.user_s ?? null, sys_s: time.sys_s ?? null, minor_page_faults: time.minor_page_faults ?? null },
  counters, // perf stat: instructions, cycles, cache-misses, branches, …
  derived: {
    // instructions per cycle (perf names the event `cpu-cycles`).
    ipc: counters.instructions && (counters["cpu-cycles"] ?? counters.cycles)
      ? Number((counters.instructions / (counters["cpu-cycles"] ?? counters.cycles)).toFixed(3))
      : null,
  },
  tests,
  cov_files,
  // Per-`cached_thm!` build times (inclusive of nested builds), ranked. The
  // `count`/`total_ms` reflect every timed theorem; `theorems` is the top slice.
  theorems_count: theorems.length,
  theorems_total_ms,
  theorems: theorems_top,
};
console.log(JSON.stringify(out, null, 2));
process.exit(run.exitCode ?? 0);
