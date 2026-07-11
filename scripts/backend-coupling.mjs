#!/usr/bin/env bun
// Backend-coupling inventory — measure how tightly each crate is wired to the
// CONCRETE HOL backend (`covalence_core::Term` / `TermKind`), so the
// decoupling work (the `covalence-hol-api` trait surface, TRACK A) has a moving
// target to shrink.
//
// The claim being tracked: consumers that build terms/theorems through the
// `Hol` / `Nat` traits (crates/kernel/hol/api) never mention `TermKind::` and
// only mention `Term::` through the trait impl. A "swap the backend" change
// then only has to rewrite the impl, not every consumer. This script counts
// the remaining direct-backend sites per crate (src only, tests excluded) so
// that number can be watched down.
//
// The IMPL crates are expected to stay high: covalence-core IS the backend;
// covalence-init / covalence-hol-eval are where the trait impl + the theorem
// catalogue live. What matters is CONSUMER crates (app/, server/, proof/,
// lang/) trending toward zero.
//
// Usage:
//   bun scripts/backend-coupling.mjs           print the table
//   bun scripts/backend-coupling.mjs --json     also write docs/deps/backend-coupling.json

import { execSync } from "node:child_process";
import { existsSync, writeFileSync } from "node:fs";

const WRITE_JSON = process.argv.includes("--json");

// Count matches of a regex across `crates/**/src/**.rs`, grouped by crate
// (the path segment up to `/src/`). Tests and examples under src are rare;
// integration tests live under `/tests/` which `/src/` already excludes.
function countByCrate(pattern) {
  let out;
  try {
    out = execSync(
      `grep -rn --include=*.rs -- '${pattern}' crates`,
      { encoding: "utf8", maxBuffer: 64 * 1024 * 1024, shell: "/bin/bash" },
    );
  } catch (e) {
    // grep exits 1 when there are no matches.
    out = e.stdout ? e.stdout.toString() : "";
  }
  const counts = {};
  for (const line of out.split("\n")) {
    if (!line.includes("/src/")) continue;
    const m = line.match(/^crates\/(.+?)\/src\//);
    if (!m) continue;
    counts[m[1]] = (counts[m[1]] || 0) + 1;
  }
  return counts;
}

const termKind = countByCrate("TermKind::");
const term = countByCrate("\\bTerm::");

const crates = [...new Set([...Object.keys(termKind), ...Object.keys(term)])].sort();

const rows = crates.map((c) => ({
  crate: c,
  termKind: termKind[c] || 0,
  term: term[c] || 0,
}));
rows.sort((a, b) => b.term - a.term);

const isImpl = (c) =>
  c === "kernel/hol/core" ||
  c === "kernel/hol/init" ||
  c === "kernel/hol/eval" ||
  c === "kernel/hol/api";

const pad = (s, n) => String(s).padEnd(n);
console.log(pad("crate", 24), pad("TermKind::", 12), pad("Term::", 10), "role");
console.log("-".repeat(60));
for (const r of rows) {
  console.log(
    pad(r.crate, 24),
    pad(r.termKind, 12),
    pad(r.term, 10),
    isImpl(r.crate) ? "backend/impl" : "consumer",
  );
}

const consumerTermKind = rows
  .filter((r) => !isImpl(r.crate))
  .reduce((a, r) => a + r.termKind, 0);
const consumerTerm = rows
  .filter((r) => !isImpl(r.crate))
  .reduce((a, r) => a + r.term, 0);
console.log("-".repeat(60));
console.log(
  `consumer totals: TermKind:: = ${consumerTermKind}, Term:: = ${consumerTerm}`,
);
console.log("(watch these trend toward zero as consumers migrate to the traits)");

if (WRITE_JSON) {
  writeFileSync(
    "docs/deps/backend-coupling.json",
    JSON.stringify({ generatedAt: new Date().toISOString(), rows }, null, 2) + "\n",
  );
  console.log("\nwrote docs/deps/backend-coupling.json");
}
