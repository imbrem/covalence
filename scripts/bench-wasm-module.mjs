#!/usr/bin/env bun
/**
 * Benchmark **whole-module kernel recognition** — the workload behind the
 * `cfg_grammar.rs` T5/T5b integration tests (prove ⊢ Derives_E Bmodule ⌜27
 * real module bytes⌝ through the kernel), in release mode. The set.mm-style
 * companion for the WASM grammar leg: use it to drive the module-proof
 * runtime down the way `bench:setmm` drove the Metamath checker.
 *
 * Usage:
 *   bun run bench:wasm-module [reps]                 # timing JSON on stdout
 *   bun run bench:wasm-module --whole-spec [reps]    # + the T5b whole-spec env
 *   bun run bench:wasm-module --flame [reps]         # + perf flamegraph
 *
 *     reps  prove repetitions, fastest reported  [default 3]
 *
 * Output (stdout is a single JSON object; everything else on stderr):
 *   { bytes, env_clauses, env_ms, prove_ms, refuse_ms,
 *     whole_env_clauses?, whole_env_ms?, whole_prove_ms?, flamegraph? }
 *
 * `--flame` wraps the bench in `perf record --call-graph=dwarf` and renders
 * /tmp/cov-wasm-module-flame.svg (needs perf + stackcollapse-perf.pl +
 * flamegraph.pl on PATH).
 */
import { spawnSync, which } from "bun";
import { existsSync } from "node:fs";
import { buildExample } from "./_setmm.mjs";

const log = (...a) => console.error("[bench-wasm-module]", ...a);

const argv = process.argv.slice(2);
const flame = argv.includes("--flame");
const wholeSpec = argv.includes("--whole-spec");
const rest = argv.filter((a) => !a.startsWith("--"));
const REPS = rest[0] ?? "3";

const bin = buildExample("covalence-init", "wasm_module_bench");
const args = [bin, REPS, ...(wholeSpec ? ["--whole-spec"] : [])];

let result = {};
if (!flame) {
  const run = spawnSync(args, { stdout: "pipe", stderr: "inherit" });
  if (run.exitCode !== 0) process.exit(run.exitCode ?? 1);
  result = JSON.parse(run.stdout.toString().trim());
} else {
  for (const tool of ["perf", "stackcollapse-perf.pl", "flamegraph.pl"]) {
    if (!which(tool)) {
      log(`--flame requires ${tool} on PATH`);
      process.exit(1);
    }
  }
  const perfData = "/tmp/cov-wasm-module.perf";
  const svg = "/tmp/cov-wasm-module-flame.svg";
  log("perf record (dwarf call graphs)…");
  const rec = spawnSync(
    ["perf", "record", "-F", "997", "-g", "--call-graph=dwarf", "-o", perfData, "--", ...args],
    { stdout: "pipe", stderr: "inherit" },
  );
  if (rec.exitCode !== 0) process.exit(rec.exitCode ?? 1);
  result = JSON.parse(rec.stdout.toString().trim());

  log("rendering flamegraph…");
  const script = spawnSync(["perf", "script", "-i", perfData], { stdout: "pipe" });
  const collapsed = spawnSync(["stackcollapse-perf.pl"], { stdin: script.stdout, stdout: "pipe" });
  const graph = spawnSync(
    ["flamegraph.pl", "--title", "whole-module kernel recognition (Bmodule)", "--width", "1600"],
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

console.log(JSON.stringify(result, null, 2));
