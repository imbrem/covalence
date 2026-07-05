#!/usr/bin/env bun
// Purge ratchet for the toHOL purge (notes/vibes/pure-hol-and-build-plan.md).
// Counts every call site of the deprecated kernel surfaces (observer rules,
// reduce_prim / unfold_term_spec, the TermKind literal family, the literal
// Term constructors, has_no_obs, and the .cov script reduce/delta forms),
// per crate, and pins the counts in a golden file:
//
//   docs/deps/purge-ratchet.json
//
// THE RATCHET RULE: counts may only DECREASE. The only exemption is
// transitional purge machinery, and it MUST be recorded in the golden's
// `exceptions` ledger in the same commit —
// covalence-core counts itself; the endgame drives every count to 0.
//
// Usage:
//   bun scripts/purge-ratchet.mjs           regenerate the golden (refuses to
//                                            write if any count would INCREASE)
//   bun scripts/purge-ratchet.mjs --check   fail (exit 1) if the golden is
//                                            stale or any count increased
//                                            (used in CI + the pre-commit hook)
//
// Counting is done with ripgrep over crates/ (respects .gitignore, so target/
// is skipped); files map to crates via the workspace manifest paths.

import { execFileSync } from "node:child_process";
import { existsSync, readFileSync, writeFileSync, mkdirSync } from "node:fs";
import { resolve, sep } from "node:path";

const CHECK = process.argv.includes("--check");
const OUT = "docs/deps/purge-ratchet.json";

// ---------------------------------------------------------------------------
// The ratcheted patterns. `glob` scopes the search; regexes are rg syntax.
// ---------------------------------------------------------------------------
const PATTERNS = [
  { name: "obs-rules", glob: "*.rs", re: String.raw`\.obs_eq\(|\.obs_true\(|\.obs_imp\(` },
  { name: "reduce_prim", glob: "*.rs", re: String.raw`reduce_prim` },
  { name: "unfold_term_spec", glob: "*.rs", re: String.raw`unfold_term_spec` },
  { name: "termkind-literals", glob: "*.rs", re: String.raw`TermKind::(Obs|Int|Blob|SmallInt|Nat|Succ)` },
  { name: "tycon-obs", glob: "*.rs", re: String.raw`TyConObs` },
  { name: "term-literal-ctors", glob: "*.rs", re: String.raw`Term::(int_lit|blob|nat_lit)` },
  { name: "has_no_obs", glob: "*.rs", re: String.raw`has_no_obs` },
  { name: "cov-script-reduce", glob: "*.cov", re: String.raw`(reduce-prim|reduce |delta)` },
];

// ---------------------------------------------------------------------------
// Map files to workspace crates (deepest manifest dir wins, so nested crates
// like covalence-pure-trusted inside crates/kernel/base/ resolve correctly).
// ---------------------------------------------------------------------------
const md = JSON.parse(
  execFileSync("cargo", ["metadata", "--format-version", "1", "--no-deps"], {
    maxBuffer: 1 << 30,
  }).toString(),
);
const crateDirs = md.packages
  .map((p) => [resolve(p.manifest_path, ".."), p.name])
  .sort((a, b) => b[0].length - a[0].length); // deepest first
const root = resolve(".");
function crateOf(file) {
  const abs = resolve(root, file);
  for (const [dir, name] of crateDirs) {
    if (abs === dir || abs.startsWith(dir + sep)) return name;
  }
  return "?";
}

// ---------------------------------------------------------------------------
// Count matches per (pattern, crate) with ripgrep.
// ---------------------------------------------------------------------------
function rgCountMatches(re, glob) {
  let out;
  try {
    out = execFileSync(
      "rg",
      ["--count-matches", "--no-messages", "-g", glob, "-e", re, "crates"],
      { maxBuffer: 1 << 30 },
    ).toString();
  } catch (e) {
    if (e.status === 1) return {}; // rg exit 1 = no matches
    throw e;
  }
  const perCrate = {};
  for (const line of out.split("\n")) {
    if (!line) continue;
    const i = line.lastIndexOf(":");
    const file = line.slice(0, i);
    const n = Number(line.slice(i + 1));
    const crate = crateOf(file);
    perCrate[crate] = (perCrate[crate] ?? 0) + n;
  }
  return perCrate;
}

const counts = {};
const totals = {};
for (const { name, glob, re } of PATTERNS) {
  const perCrate = rgCountMatches(re, glob);
  counts[name] = Object.fromEntries(
    Object.entries(perCrate).sort(([a], [b]) => a.localeCompare(b)),
  );
  totals[name] = Object.values(perCrate).reduce((a, b) => a + b, 0);
}

const priorGolden = existsSync(OUT) ? JSON.parse(readFileSync(OUT, "utf8")) : null;
const exceptions = priorGolden?.exceptions ?? [];

const artifact =
  JSON.stringify(
    {
      generatedBy: "scripts/purge-ratchet.mjs",
      note: "toHOL-purge ratchet: per-crate call-site counts of deprecated kernel surfaces. Counts may only DECREASE (regen via `bun run deps`); no crate is exempt. An increase fails CI and refuses regeneration — remove the new call site instead.",
      patterns: Object.fromEntries(PATTERNS.map((p) => [p.name, { glob: p.glob, regex: p.re }])),
      counts,
      totals,
      // Increase-exception LEDGER: an increase is permitted ONLY when the same
      // commit appends an entry here ({ commit, pattern, crate, delta, reason,
      // diesWith }). Hand-editing the golden without a ledger entry is a
      // process violation — reviewers diff this file. Entries are carried
      // forward verbatim on regeneration and removed when their call sites die.
      exceptions,
    },
    null,
    2,
  ) + "\n";

// ---------------------------------------------------------------------------
// Ratchet comparison against the golden.
// ---------------------------------------------------------------------------
const golden = priorGolden;
function increases() {
  if (!golden) return [];
  const out = [];
  for (const { name } of PATTERNS) {
    const cur = counts[name] ?? {};
    const old = golden.counts?.[name] ?? {};
    for (const [crate, n] of Object.entries(cur)) {
      const o = old[crate] ?? 0;
      if (n > o) out.push(`  ${name} in ${crate}: ${o} -> ${n}`);
    }
  }
  return out;
}

const inc = increases();
if (inc.length) {
  console.error(
    "purge-ratchet: RATCHET VIOLATION — deprecated call-site counts increased:",
  );
  for (const line of inc) console.error(line);
  console.error(
    "purge-ratchet: remove the new call sites, or (rare, transitional-machinery only)",
  );
  console.error(
    "purge-ratchet: hand-bump the golden WITH a new `exceptions` ledger entry in the same commit.",
  );
  process.exit(1);
}

if (CHECK) {
  if (!golden || readFileSync(OUT, "utf8") !== artifact) {
    console.error(`purge-ratchet: ${OUT} is stale — run \`bun run deps\``);
    process.exit(1);
  }
  console.error("purge-ratchet: up to date");
  process.exit(0);
}

mkdirSync("docs/deps", { recursive: true });
writeFileSync(OUT, artifact);
console.error(`purge-ratchet: wrote ${OUT}`);
