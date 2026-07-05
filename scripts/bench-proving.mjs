#!/usr/bin/env bun
/**
 * Proving-performance benchmark harness (pre-S10 baseline).
 *
 * S10 of the toHOL purge (notes/vibes/pure-hol-and-build-plan.md) flips the
 * reification target from kernel literal numerals (`TermKind::Nat`/`Succ`/`Int`/
 * `Blob`) to defined constant forms. The de-facto acceptance test for that flip
 * is *proving-by-computation performance*: the utf8/utf16/regex/string `.cov`
 * suites and the nat/int/rat/real Rust proving tests in `covalence-init` all
 * discharge their goals by evaluating literal arithmetic, so a slower reified
 * numeral form shows up here first. This harness times those suites and pins the
 * wall-clock baseline so S10 can measure regression against it.
 *
 * It is pure infra: no kernel change, and — being a script, not a `#[test]` — it
 * never runs under `cargo test`. Run it explicitly:
 *
 *   bun scripts/bench-proving.mjs                 # release, 5 reps + 1 warmup
 *   bun scripts/bench-proving.mjs --debug         # debug profile instead
 *   bun scripts/bench-proving.mjs --reps 9        # more samples
 *   bun scripts/bench-proving.mjs --stdout        # print JSON, don't write file
 *   bun scripts/bench-proving.mjs --filter rat    # only suites whose name ~ rat
 *
 * Method: each suite is run as a `--test-threads=1` filter over a pre-built test
 * binary (so the timed run is the run, not the build), `reps` times after
 * `warmup` discarded runs. We record every sample plus min/median/mean/max in
 * milliseconds. Compare S10 against the baseline with `min` (least OS noise):
 * a suite regresses if its post-flip `min` exceeds the baseline `min` by more
 * than noise. Numbers are hardware-dependent — the comparison is ratio-based on
 * the SAME machine (re-run the harness on the S10 tree, diff the JSONs).
 */

import { spawnSync } from "bun";
import { readdirSync, statSync, writeFileSync, mkdirSync } from "node:fs";
import { join, dirname } from "node:path";

// ---------------------------------------------------------------------------
// CLI
// ---------------------------------------------------------------------------
const argv = process.argv.slice(2);
const flag = (name) => argv.includes(name);
const opt = (name, dflt) => {
  const i = argv.indexOf(name);
  return i >= 0 && i + 1 < argv.length ? argv[i + 1] : dflt;
};
const RELEASE = !flag("--debug");
const REPS = Number(opt("--reps", "5"));
const WARMUP = Number(opt("--warmup", "1"));
const TO_STDOUT = flag("--stdout");
const NAME_FILTER = opt("--filter", null);
const OUT = "docs/deps/proving-baseline.json";
const log = (...a) => console.error("[bench-proving]", ...a);

// ---------------------------------------------------------------------------
// The suites. Each is one `covalence-init` test-filter that proves by
// computation. `bin` selects which test binary the filter runs against:
//   "lib"   → the unit tests (src/lib.rs)
//   "regex" → the tests/regex_matching.rs integration binary
// `filter` is a libtest substring filter (prefix of the module path); "" means
// the whole binary.
// ---------------------------------------------------------------------------
const SUITES = [
  // utf8/utf16/string .cov + Rust encode-by-computation proving.
  { name: "utf8", bin: "lib", filter: "init::utf8", note: "UTF-8 encode/decode by computation (utf8.cov + Rust)" },
  { name: "utf16", bin: "lib", filter: "init::utf16", note: "UTF-16 encode by computation" },
  { name: "string", bin: "lib", filter: "init::string", note: "string/bytes newtype seam (light; prelude floor)" },
  // regex: derivation matching by computation (init::regex + the desugar/compile
  // grammar layer + the integration corpus that agrees with the Rust oracle).
  { name: "regex-init", bin: "lib", filter: "init::regex", note: "regex.cov derivative-matching, oracle agreement" },
  { name: "regex-grammar", bin: "lib", filter: "grammar::regex", note: "regex desugar/compile to a byte language" },
  { name: "regex-corpus", bin: "regex", filter: "", note: "regex_matching integration: oracle corpus + timing regexes" },
  // nat/int heavy computation (the numeral form S10 flips).
  { name: "nat", bin: "lib", filter: "init::nat::", note: "nat arithmetic proving" },
  { name: "nat-div", bin: "lib", filter: "init::nat_div", note: "nat division/mod by computation" },
  { name: "int", bin: "lib", filter: "init::int::", note: "int (quotient) arithmetic proving" },
  { name: "rat", bin: "lib", filter: "init::rat", note: "rat arithmetic proving (heaviest numeral suite)" },
  { name: "real", bin: "lib", filter: "init::real", note: "real/analysis proving over int/rat" },
];

// ---------------------------------------------------------------------------
// Build + locate the test binaries.
// ---------------------------------------------------------------------------
const profile = RELEASE ? "release" : "debug";
const buildArgs = ["cargo", "test", "-p", "covalence-init", "--no-run"];
if (RELEASE) buildArgs.push("--release");
log(`building covalence-init test binaries (${profile})…`);
const build = spawnSync(buildArgs, { stdout: "inherit", stderr: "inherit" });
if (build.exitCode !== 0) {
  log("build failed");
  process.exit(build.exitCode ?? 1);
}

const targetDir =
  spawnSync(["cargo", "metadata", "--format-version=1", "--no-deps"])
    .stdout.toString()
    .match(/"target_directory":"([^"]+)"/)?.[1] ?? "target";
const depsDir = join(targetDir, profile, "deps");

// Newest executable matching a name regex (skip .d/.rlib/.rmeta/.pdb).
function newestBinary(re) {
  let best = "";
  let bestMtime = -1;
  for (const name of readdirSync(depsDir)) {
    if (!re.test(name)) continue;
    const p = join(depsDir, name);
    const st = statSync(p);
    if (st.isFile() && st.mode & 0o111 && st.mtimeMs > bestMtime) {
      bestMtime = st.mtimeMs;
      best = p;
    }
  }
  return best;
}
const BINS = {
  lib: newestBinary(/^covalence_init-[0-9a-f]+$/),
  regex: newestBinary(/^regex_matching-[0-9a-f]+$/),
};
for (const [k, v] of Object.entries(BINS)) {
  if (!v) {
    log(`could not find the ${k} test binary under ${depsDir}`);
    process.exit(1);
  }
  log(`${k} binary: ${v}`);
}

// ---------------------------------------------------------------------------
// Time one suite.
// ---------------------------------------------------------------------------
function countTests(bin, filter) {
  const args = filter ? [filter, "--list"] : ["--list"];
  const out = spawnSync([bin, ...args]).stdout.toString();
  return (out.match(/: test$/gm) ?? []).length;
}
function runOnce(bin, filter) {
  const args = filter ? [filter, "--test-threads=1"] : ["--test-threads=1"];
  const t0 = performance.now();
  const r = spawnSync([bin, ...args], { stdout: "ignore", stderr: "ignore" });
  const ms = performance.now() - t0;
  if (r.exitCode !== 0) {
    log(`suite failed: ${bin} ${args.join(" ")} (exit ${r.exitCode})`);
    process.exit(1);
  }
  return ms;
}
const stats = (xs) => {
  const s = [...xs].sort((a, b) => a - b);
  const median = s.length % 2 ? s[(s.length - 1) / 2] : (s[s.length / 2 - 1] + s[s.length / 2]) / 2;
  const round = (x) => Math.round(x * 100) / 100;
  return {
    min: round(s[0]),
    median: round(median),
    mean: round(s.reduce((a, b) => a + b, 0) / s.length),
    max: round(s[s.length - 1]),
  };
};

// ---------------------------------------------------------------------------
// Run.
// ---------------------------------------------------------------------------
const chosen = NAME_FILTER ? SUITES.filter((s) => s.name.includes(NAME_FILTER)) : SUITES;
log(`profile=${profile} reps=${REPS} warmup=${WARMUP} suites=${chosen.length}`);
const results = [];
for (const suite of chosen) {
  const bin = BINS[suite.bin];
  const tests = countTests(bin, suite.filter);
  for (let i = 0; i < WARMUP; i++) runOnce(bin, suite.filter);
  const samples = [];
  for (let i = 0; i < REPS; i++) samples.push(Math.round(runOnce(bin, suite.filter) * 100) / 100);
  const st = stats(samples);
  results.push({ name: suite.name, bin: suite.bin, filter: suite.filter, note: suite.note, tests, ms: st, samples });
  log(`${suite.name.padEnd(14)} ${tests.toString().padStart(3)}t  min ${st.min.toFixed(1).padStart(8)}  median ${st.median.toFixed(1).padStart(8)}  ms`);
}

// ---------------------------------------------------------------------------
// Emit.
// ---------------------------------------------------------------------------
const gitCommit =
  spawnSync(["git", "rev-parse", "--short", "HEAD"]).stdout.toString().trim() || null;
const doc = {
  generatedBy: "scripts/bench-proving.mjs",
  note:
    "Pre-S10 proving-performance baseline (toHOL purge). Wall-clock ms per " +
    "covalence-init compute-heavy proving suite. Compare S10 against `min` on " +
    "the SAME machine (numbers are hardware-dependent; the check is ratio-based).",
  gitCommit,
  profile,
  reps: REPS,
  warmup: WARMUP,
  suites: results,
};
const json = JSON.stringify(doc, null, 2) + "\n";
if (TO_STDOUT) {
  process.stdout.write(json);
} else {
  mkdirSync(dirname(OUT), { recursive: true });
  writeFileSync(OUT, json);
  log(`wrote ${OUT}`);
}
