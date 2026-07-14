#!/usr/bin/env bun
/**
 * Benchmark **downloading + checking set.mm** with the pure Metamath engine
 * (`covalence-metamath`: parse + RPN-verify every proof; no HOL). set.mm is
 * pinned to a fixed revision and cached (see `_setmm.mjs`), so numbers are
 * comparable across runs; the first run pays the download once.
 *
 * Usage:
 *   bun run bench:setmm [reps] [set_mm_path]        # timing JSON on stdout
 *   bun run bench:setmm --flame [reps] [set_mm_path]  # + perf flamegraph
 *
 *     reps         parse+verify repetitions, fastest reported  [default 1]
 *     set_mm_path  explicit .mm file (else $COV_SET_MM, else pinned download)
 *
 * Output (stdout is a single JSON object; everything else on stderr):
 *   { path, bytes, download_ms, parse_ms, verify_ms, total_ms, proofs,
 *     proofs_per_s, ..., flamegraph? }
 *
 * `--flame` wraps the bench in `perf record --call-graph=dwarf` and renders
 * /tmp/cov-mm-verify-flame.svg (needs perf + stackcollapse-perf.pl +
 * flamegraph.pl on PATH). For the HOL *import* pipeline use `profile:import` /
 * `profile:flame` instead — this bench is the raw Metamath checker.
 */
import { spawnSync, which } from "bun";
import { existsSync } from "node:fs";
import { buildExample, ensureSetMm } from "./_setmm.mjs";

const log = (...a) => console.error("[bench-setmm]", ...a);

const argv = process.argv.slice(2);
const flame = argv.includes("--flame");
const rest = argv.filter((a) => a !== "--flame");
const REPS = rest[0] ?? "1";
const SET_MM_ARG = rest[1];

// 1. Locate set.mm (pinned download, cached) — timed, since "download" is part
//    of what this command benchmarks (cache hit ⇒ ~0 ms).
const t0 = performance.now();
const setmm = await ensureSetMm(SET_MM_ARG);
const downloadMs = performance.now() - t0;

// 2. Build + run the pure verify bench.
const bin = buildExample("covalence-metamath", "mm_verify_bench");

let result = {};
if (!flame) {
  const run = spawnSync([bin, setmm, REPS], { stdout: "pipe", stderr: "inherit" });
  if (run.exitCode !== 0) process.exit(run.exitCode ?? 1);
  result = JSON.parse(run.stdout.toString().trim().split("\n").pop() ?? "{}");
} else {
  for (const tool of ["perf", "stackcollapse-perf.pl", "flamegraph.pl"]) {
    if (!which(tool)) {
      log(`--flame requires ${tool} on PATH`);
      process.exit(1);
    }
  }
  const perfData = "/tmp/cov-mm-verify.perf";
  const svg = "/tmp/cov-mm-verify-flame.svg";
  log("perf record (dwarf call graphs)…");
  const rec = spawnSync(
    ["perf", "record", "-F", "997", "-g", "--call-graph=dwarf", "-o", perfData, "--", bin, setmm, REPS],
    { stdout: "pipe", stderr: "inherit" },
  );
  if (rec.exitCode !== 0) process.exit(rec.exitCode ?? 1);
  result = JSON.parse(rec.stdout.toString().trim().split("\n").pop() ?? "{}");

  log("rendering flamegraph…");
  const script = spawnSync(["perf", "script", "-i", perfData], { stdout: "pipe" });
  const collapsed = spawnSync(["stackcollapse-perf.pl"], { stdin: script.stdout, stdout: "pipe" });
  const graph = spawnSync(
    ["flamegraph.pl", "--title", "set.mm parse+verify (covalence-metamath)", "--width", "1600"],
    { stdin: collapsed.stdout, stdout: "pipe" },
  );
  await Bun.write(svg, graph.stdout);
  if (!existsSync(svg)) {
    log("flamegraph rendering failed");
    process.exit(1);
  }
  log(`flamegraph: ${svg}`);
  result.flamegraph = svg;
}

result.download_ms = Math.round(downloadMs * 10) / 10;
console.log(JSON.stringify(result, null, 2));
