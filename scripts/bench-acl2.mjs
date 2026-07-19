#!/usr/bin/env bun
/**
 * ACL2 performance, scaling, and autoresearch scoring harness.
 *
 * `--baseline FILE` turns this into a regression gate suitable for an
 * external mutate/run/retain loop. Correctness dominates scaling, which
 * dominates speed.
 */

import { spawnSync, which } from "bun";
import { readFileSync } from "node:fs";
import { hostname, platform, release, arch, cpus } from "node:os";
import { buildExample } from "./_setmm.mjs";

const argv = process.argv.slice(2);
const opt = (name, fallback) => {
  const index = argv.indexOf(name);
  return index >= 0 && index + 1 < argv.length ? argv[index + 1] : fallback;
};
const flag = (name) => argv.includes(name);
function numberOption(name, fallback, integer, allowZero) {
  const value = Number(opt(name, fallback));
  if (!Number.isFinite(value) || (allowZero ? value < 0 : value <= 0) || (integer && !Number.isInteger(value))) {
    throw new Error(`${name} has an invalid value`);
  }
  return value;
}
const reps = numberOption("--reps", "5", true, false);
const warmup = numberOption("--warmup", "1", true, true);
const timeoutMs = numberOption("--timeout-ms", "300000", true, false);
const baselinePath = opt("--baseline", null);
const outputPath = opt("--out", null);
const maxSlowdown = numberOption("--max-slowdown", "1.15", false, false);
const maxExponentRegression = numberOption("--max-exponent-regression", "0.15", false, true);
const systemCounters = flag("--system-counters");
const log = (...values) => console.error("[bench-acl2]", ...values);
const round = (value, digits = 6) => {
  const scale = 10 ** digits;
  return Math.round(value * scale) / scale;
};
const quantile = (sorted, q) =>
  sorted[Math.min(sorted.length - 1, Math.max(0, Math.ceil(q * sorted.length) - 1))];
const stats = (samples) => {
  const sorted = [...samples].sort((a, b) => a - b);
  return {
    median_ms: round(quantile(sorted, 0.5) / 1e6),
    p95_ms: round(quantile(sorted, 0.95) / 1e6),
    max_ms: round(sorted.at(-1) / 1e6),
  };
};
function exponent(points) {
  const xy = points
    .filter((point) => point.size > 0 && point.median_ms > 0)
    .map((point) => [Math.log(point.size), Math.log(point.median_ms)]);
  if (xy.length < 2) return null;
  const mx = xy.reduce((sum, [x]) => sum + x, 0) / xy.length;
  const my = xy.reduce((sum, [, y]) => sum + y, 0) / xy.length;
  const numerator = xy.reduce((sum, [x, y]) => sum + (x - mx) * (y - my), 0);
  const denominator = xy.reduce((sum, [x]) => sum + (x - mx) ** 2, 0);
  return denominator === 0 ? null : round(numerator / denominator);
}

if (flag("--self-test")) {
  const summary = stats([5_000_000, 1_000_000, 3_000_000, 2_000_000, 4_000_000]);
  if (summary.median_ms !== 3 || summary.p95_ms !== 5 || summary.max_ms !== 5) {
    throw new Error(`statistics self-test failed: ${JSON.stringify(summary)}`);
  }
  const linear = exponent([
    { size: 1, median_ms: 2 },
    { size: 2, median_ms: 4 },
    { size: 4, median_ms: 8 },
    { size: 8, median_ms: 16 },
  ]);
  if (Math.abs(linear - 1) > 1e-6) throw new Error(`exponent self-test failed: ${linear}`);
  console.log("acl2 benchmark scoring self-test passed");
  process.exit(0);
}

const bin = buildExample("covalence-lisp", "acl2_perf_bench", ["--features", "hol"]);
const invocation = [bin, String(reps), String(warmup)];
let command = invocation;
const counterSources = [];
const timeBin = systemCounters ? which("time") : null;
const perfBin = systemCounters ? which("perf") : null;
if (timeBin) {
  command = [timeBin, "-v", ...command];
  counterSources.push("gnu-time-v");
}
if (perfBin) {
  command = [perfBin, "stat", "-x", ",", "-e", "cycles,instructions,cache-misses,task-clock", "--", ...command];
  counterSources.push("perf-stat");
}
log(`running ${reps} repetition(s), ${warmup} warmup(s), timeout ${timeoutMs} ms`);
let run = spawnSync(command, { stdout: "pipe", stderr: "pipe", timeout: timeoutMs });
let counterError = null;
if (run.exitCode !== 0 && counterSources.length > 0) {
  counterError = run.stderr.toString().trim().split("\n").at(-1) ?? "counter wrapper failed";
  log(`optional counters unavailable (${counterError}); retrying without counters`);
  run = spawnSync(invocation, { stdout: "pipe", stderr: "pipe", timeout: timeoutMs });
}
if (run.exitCode !== 0) {
  process.stderr.write(run.stderr);
  log(run.signalCode ? `benchmark terminated by ${run.signalCode}` : `exit ${run.exitCode}`);
  process.exit(2);
}

const lines = run.stdout.toString().trim().split("\n");
if (lines.shift() !== "acl2-perf-v1") {
  log("benchmark driver returned an unknown protocol");
  process.exit(2);
}
const groups = new Map();
for (const line of lines) {
  const [family, sizeRaw, bytesRaw, repetitionRaw, elapsedRaw, correctRaw] = line.split("\t");
  const key = `${family}:${sizeRaw}`;
  const group = groups.get(key) ?? {
    family,
    size: Number(sizeRaw),
    source_bytes: Number(bytesRaw),
    samples_ns: [],
    correct: 0,
    failures: 0,
  };
  if (Number(repetitionRaw) !== group.samples_ns.length) throw new Error(`bad repetition in ${key}`);
  group.samples_ns.push(Number(elapsedRaw));
  if (correctRaw === "1") group.correct += 1;
  else group.failures += 1;
  groups.set(key, group);
}

const cases = [...groups.values()]
  .sort((a, b) => a.family.localeCompare(b.family) || a.size - b.size)
  .map((group) => {
    const timing = stats(group.samples_ns);
    return {
      family: group.family,
      size: group.size,
      source_bytes: group.source_bytes,
      work_units: group.size,
      samples: group.samples_ns.length,
      correct: group.correct,
      failures: group.failures,
      timing,
      normalized_median_ms_per_unit: round(timing.median_ms / group.size),
      samples_ns: group.samples_ns,
    };
  });
const families = [...new Set(cases.map((item) => item.family))].map((family) => {
  const points = cases.filter((item) => item.family === family);
  return {
    family,
    cases: points.length,
    scaling_exponent: exponent(points.map((item) => ({
      size: item.work_units,
      median_ms: item.timing.median_ms,
    }))),
    largest_normalized_median_ms_per_unit: points.at(-1).normalized_median_ms_per_unit,
  };
});
const correct = cases.reduce((sum, item) => sum + item.correct, 0);
const failures = cases.reduce((sum, item) => sum + item.failures, 0);
const total = correct + failures;
const worstExponent = Math.max(...families.map((item) => item.scaling_exponent ?? 99));
const largestCost = families.reduce(
  (sum, item) => sum + item.largest_normalized_median_ms_per_unit,
  0,
);
const scalingQuality = 1 / (1 + Math.max(0, worstExponent - 1));
const speedQuality = 1 / (1 + largestCost);
const score = {
  ordering: ["correct_samples", "scaling_quality", "speed_quality"],
  correct_samples: correct,
  scaling_quality: round(scalingQuality),
  speed_quality: round(speedQuality),
  total: round(correct * 1e12 + scalingQuality * 1e6 + speedQuality * 1e3, 3),
};

let system = null;
if (systemCounters) {
  const stderr = run.stderr.toString();
  const rss = stderr.match(/Maximum resident set size \(kbytes\):\s*(\d+)/)?.[1];
  const counter = (name) => {
    const raw = stderr.match(new RegExp(`^([0-9]+(?:\\.[0-9]+)?),,${name},`, "m"))?.[1];
    return raw ? Number(raw) : null;
  };
  system = {
    requested: true,
    sources: counterError ? [] : counterSources,
    unavailable_reason: counterError,
    max_rss_kb: rss ? Number(rss) : null,
    cycles: counter("cycles"),
    instructions: counter("instructions"),
    cache_misses: counter("cache-misses"),
    task_clock_ms: counter("task-clock"),
  };
}
const gitCommit = spawnSync(["git", "rev-parse", "HEAD"]).stdout.toString().trim() || null;
const document = {
  schema: "covalence.acl2-performance.v1",
  generated_by: "scripts/bench-acl2.mjs",
  git_commit: gitCommit,
  profile: "release",
  repetitions: reps,
  warmup,
  timeout_ms: timeoutMs,
  machine: {
    hostname: hostname(),
    platform: platform(),
    release: release(),
    architecture: arch(),
    logical_cpus: cpus().length,
    cpu_model: cpus()[0]?.model ?? null,
  },
  correctness: { correct, failures, total },
  families,
  cases,
  system,
  score,
};

let accepted = failures === 0;
if (baselinePath) {
  const baseline = JSON.parse(readFileSync(baselinePath, "utf8"));
  const baselineCases = new Map(baseline.cases.map((item) => [`${item.family}:${item.size}`, item]));
  const ratios = cases
    .map((item) => {
      const old = baselineCases.get(`${item.family}:${item.size}`);
      return old ? item.timing.median_ms / old.timing.median_ms : null;
    })
    .filter((ratio) => Number.isFinite(ratio));
  const baselineExponent = Math.max(...baseline.families.map((item) => item.scaling_exponent ?? 99));
  const slowdown = ratios.length ? Math.max(...ratios) : Infinity;
  const exponentRegression = worstExponent - baselineExponent;
  const reasons = [];
  if (baseline.correctness.failures !== 0) reasons.push("baseline-is-not-correct");
  if (failures !== 0) reasons.push("candidate-correctness-failure");
  if (baseline.correctness.total !== total) reasons.push("workload-shape-changed");
  if (slowdown > maxSlowdown) reasons.push("median-slowdown");
  if (exponentRegression > maxExponentRegression) reasons.push("scaling-exponent");
  document.comparison = {
    baseline: baselinePath,
    max_case_median_slowdown: round(slowdown),
    worst_scaling_exponent_regression: round(exponentRegression),
    thresholds: { max_slowdown: maxSlowdown, max_exponent_regression: maxExponentRegression },
    accepted: reasons.length === 0,
    reasons,
  };
  accepted &&= document.comparison.accepted;
}

const json = `${JSON.stringify(document, null, 2)}\n`;
if (outputPath) {
  await Bun.write(outputPath, json);
  log(`wrote ${outputPath}`);
} else {
  process.stdout.write(json);
}
for (const family of families) {
  log(`${family.family}: exponent=${family.scaling_exponent} largest=${family.largest_normalized_median_ms_per_unit} ms/unit`);
}
log(`correct=${correct}/${total} score=${score.total} accepted=${accepted}`);
process.exit(accepted ? 0 : 1);
