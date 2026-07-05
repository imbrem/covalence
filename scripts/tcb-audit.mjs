#!/usr/bin/env bun
// TCB audit surface — measure the *auditability* of the trusted base, not LoC.
//
// The trusted computing base is what a soundness reviewer must read and believe.
// We track it for four cumulative configurations (the CoreHol ⊂ CoreEval tower
// plus the WASM oracle tier):
//
//   base            the closed-world base kernel (mint gate, Language/admits, Op/Expr)
//   base+HOL        + the minimal HOL kernel (terms, types, the rules, define/typedef)
//   base+HOL+eval   + the eval axioms (native CanonRules + the cert families + defs/)
//   base+HOL+wasm   + the WASM-oracle float ops
//
// For each we LIST the trust-bearing constructs — `unsafe`, the `Thm::new` mint
// sites, the admitted-rule manifest, the public API surface, the term/type
// leaves, the `defs::` coupling — plus a tests-excluded source-line figure as ONE
// signal among many. Goal: watch these SHRINK as `defs/` leaves core (see
// notes/vibes/handoff/defs-out-of-core.md).
//
// Usage:
//   bun scripts/tcb-audit.mjs            print the report
//   bun scripts/tcb-audit.mjs --json     also write docs/deps/tcb-audit.json
//
// PRELIMINARY + MEANT TO BE UPDATED. The CONFIGS reflect the post-E2 split:
// the cert/toHOL rules + the defs/ term catalogue live in covalence-hol-eval
// (the CoreEval tier); what remains under core/src/defs/ is the D3 residue
// (type handles the literal LEAVES need — u8_ty..int_ty, connective builders),
// which dies with the literal leaves. Add metrics as new trust constructs
// appear.

import { execSync } from "node:child_process";
import { existsSync, readFileSync, readdirSync, statSync, writeFileSync } from "node:fs";
import { join } from "node:path";

const WRITE_JSON = process.argv.includes("--json");

// ---------------------------------------------------------------------------
// Configurations. Each is a set of source ROOTS (dirs or files) plus EXCLUDES
// (path substrings). `+HOL` EXCLUDES only core's defs/ residue (the D3
// transitional type handles, dying with the literal leaves) — the cert
// families + the term catalogue physically moved to the CoreEval tier
// (crates/kernel/hol/eval), so the gap between `base+HOL` and `base+HOL+eval`
// is now a *declared* trust boundary, not an exclude-glob fiction.
// ---------------------------------------------------------------------------
const BASE = "crates/kernel/base/trusted/src";
const CORE = "crates/kernel/hol/core/src";
const EVAL = "crates/kernel/base/eval/src";
const HOLEVAL = "crates/kernel/hol/eval/src";

const CONFIGS = [
  {
    name: "base",
    roots: [BASE],
    exclude: [],
  },
  {
    // REALITY: everything compiled into covalence-core is CoreLang trust
    // surface — including the D3 defs/ residue (literal typing, spec
    // machinery, connectives), load-bearing for Thm<CoreLang> until the
    // literal leaves die. (Audit fix: excluding it overstated the tier gap.)
    name: "base+HOL",
    roots: [BASE, CORE],
    exclude: [],
  },
  {
    // ASPIRATION: minimal HOL once the D3 residue dies with the literal
    // leaves. Gap vs base+HOL = the remaining in-core defs debt.
    name: "base+HOL (target)",
    roots: [BASE, CORE],
    exclude: [`${CORE}/defs/`],
  },
  {
    name: "base+HOL+eval",
    // The CoreEval tier: the eval axioms = the native CanonRules
    // (base/eval) + the cert/toHOL rules, their dispatch, and the defs/
    // catalogue they key on (hol/eval) + the D3 residue in core.
    roots: [BASE, CORE, EVAL, HOLEVAL],
    exclude: [],
  },
  {
    name: "base+HOL+wasm",
    // The WASM-oracle tier = minimal HOL + the float ops (base/eval
    // float.rs + the hol/eval float defs/registry). CAVEAT: the F2b
    // `FloatCert` rule + dispatch (hol/eval rules.rs/certs.rs) landed but
    // share their files with the other eval cert families, so file
    // granularity cannot include just the float slice — the full float
    // trust surface is this config PLUS the float sections of those two
    // files (read them under `base+HOL+eval`).
    roots: [BASE, CORE, `${EVAL}/float.rs`, `${HOLEVAL}/defs/floats.rs`],
    exclude: [`${CORE}/defs/`],
  },
  {
    name: "base+HOL+eval+wasm",
    // Everything trusted: the full cumulative tower (top tier).
    roots: [BASE, CORE, EVAL, HOLEVAL],
    exclude: [],
  },
];

// ---------------------------------------------------------------------------
// File gathering. A .rs file counts unless it is a test file. Within kept files
// we strip `#[cfg(test)]`-guarded blocks (mod/fn) by brace matching, so inline
// test modules do not inflate the trust surface. "tests don't count."
// ---------------------------------------------------------------------------
const isTestFile = (p) =>
  p.endsWith("/tests.rs") ||
  p.endsWith("_tests.rs") ||
  p.includes("/tests/") ||
  p.endsWith("/hol_light_tests.rs");

function walk(root) {
  if (!existsSync(root)) return [];
  if (statSync(root).isFile()) return root.endsWith(".rs") ? [root] : [];
  const out = [];
  for (const e of readdirSync(root)) {
    const p = join(root, e);
    if (statSync(p).isDirectory()) out.push(...walk(p));
    else if (p.endsWith(".rs")) out.push(p);
  }
  return out;
}

function filesFor(cfg) {
  const seen = new Set();
  for (const r of cfg.roots) for (const f of walk(r)) seen.add(f);
  return [...seen]
    .filter((f) => !isTestFile(f))
    .filter((f) => !cfg.exclude.some((x) => f.includes(x)))
    .sort();
}

// Strip `#[cfg(test)] mod {...}` / `#[cfg(test)] fn ...{...}` blocks by brace match.
function stripTestBlocks(src) {
  let out = "";
  let i = 0;
  while (i < src.length) {
    const at = src.indexOf("#[cfg(test)]", i);
    if (at === -1) {
      out += src.slice(i);
      break;
    }
    out += src.slice(i, at);
    // find the first `{` after the attribute, then match braces
    const brace = src.indexOf("{", at);
    if (brace === -1) {
      i = at + 12;
      continue;
    }
    let depth = 0;
    let j = brace;
    for (; j < src.length; j++) {
      if (src[j] === "{") depth++;
      else if (src[j] === "}") {
        depth--;
        if (depth === 0) {
          j++;
          break;
        }
      }
    }
    i = j;
  }
  return out;
}

// ---------------------------------------------------------------------------
// Metrics.
// ---------------------------------------------------------------------------
// Strip a naive line comment (everything from `//` to EOL). Good enough to keep
// doc/comment mentions of `unsafe`/`defs::` out of the CODE-construct metrics.
const stripLineComment = (ln) => {
  const i = ln.indexOf("//");
  return i === -1 ? ln : ln.slice(0, i);
};

// Grep CODE lines (comments stripped) for a construct; returns "path:line: text".
function grepList(bodies, re) {
  const hits = [];
  for (const { path, text } of bodies) {
    text.split("\n").forEach((ln, k) => {
      const code = stripLineComment(ln);
      if (re.test(code)) hits.push(`${path}:${k + 1}: ${ln.trim().slice(0, 100)}`);
    });
  }
  return hits;
}

function countPub(bodies) {
  const kinds = { fn: 0, struct: 0, enum: 0, trait: 0, macro: 0 };
  for (const { text } of bodies) {
    for (const m of text.matchAll(/^\s*pub(?:\(crate\))?\s+(fn|struct|enum|trait)\s/gm)) kinds[m[1]]++;
    for (const _ of text.matchAll(/^\s*macro_rules!\s/gm)) kinds.macro++;
  }
  return kinds;
}

function nonTestLoc(bodies) {
  let n = 0;
  for (const { text } of bodies) {
    for (const ln of text.split("\n")) {
      const t = ln.trim();
      if (t && !t.startsWith("//")) n++; // non-blank, non-line-comment
    }
  }
  return n;
}

// Admitted-rule manifests (each rule = one trust obligation). Attributed:
// core-manifest → the CoreLang HOL rules; eval-manifest → the CoreEval
// cert/toHOL rules; builtins → the native CanonRules.
function manifestCount(path) {
  if (!existsSync(path)) return null;
  return readFileSync(path, "utf8").split("\n").filter((l) => l.trim() && !l.startsWith("#")).length;
}

// TermKind / TypeKind leaf variants (each leaf = a trust-relevant case).
function enumVariants(file, enumName) {
  if (!existsSync(file)) return null;
  const src = readFileSync(file, "utf8");
  const m = src.match(new RegExp(`enum ${enumName}\\s*\\{([\\s\\S]*?)\\n\\}`));
  if (!m) return null;
  return (m[1].match(/^\s*[A-Z][A-Za-z0-9]*\s*[\(\{,]/gm) || []).length;
}

// External (non-workspace) dependency closure of a crate — trusted third-party code.
// CAVEAT (future refinement): this counts BUILD-time deps too (proc-macro2/quote/
// syn/unicode-ident come in via derive macros and are not runtime TCB). Split
// build vs normal+run deps to get the true runtime-trusted set.
let META = null;
function externalDeps(rootCrate) {
  if (!META) META = JSON.parse(execSync("cargo metadata --format-version 1", { maxBuffer: 1 << 30 }).toString());
  const ws = new Set(META.workspace_members);
  const byId = new Map(META.packages.map((p) => [p.id, p]));
  const wsNames = new Set(META.packages.filter((p) => ws.has(p.id)).map((p) => p.name));
  const idByName = new Map(META.packages.filter((p) => ws.has(p.id)).map((p) => [p.name, p.id]));
  const resolve = new Map((META.resolve?.nodes ?? []).map((n) => [n.id, n]));
  const rootId = idByName.get(rootCrate);
  if (!rootId) return null;
  const out = new Set();
  const stack = [rootId];
  while (stack.length) {
    const id = stack.pop();
    if (out.has(id)) continue;
    out.add(id);
    for (const d of resolve.get(id)?.deps ?? []) {
      if (d.dep_kinds.some((k) => k.kind === null || k.kind === "normal")) stack.push(d.pkg);
    }
  }
  return [...out].map((id) => byId.get(id).name).filter((n) => !wsNames.has(n)).sort();
}

// ---------------------------------------------------------------------------
// Run.
// ---------------------------------------------------------------------------
const report = {};
for (const cfg of CONFIGS) {
  const files = filesFor(cfg);
  const bodies = files.map((path) => ({ path, text: stripTestBlocks(readFileSync(path, "utf8")) }));

  const unsafeHits = grepList(bodies, /\bunsafe\s+(fn|impl|trait|extern|\{)/);
  const mintSites = grepList(bodies, /Thm::new\s*\(/);
  const defsCoupling = grepList(bodies, /\bdefs::/);
  const pub = countPub(bodies);

  report[cfg.name] = {
    files: files.length,
    nonTestLoc: nonTestLoc(bodies),
    unsafe: unsafeHits.length,
    unsafeLocations: unsafeHits,
    mintSites: mintSites.length,
    mintSiteLocations: mintSites,
    publicSurface: pub,
    publicSurfaceTotal: pub.fn + pub.struct + pub.enum + pub.trait + pub.macro,
    defsCoupling: defsCoupling.length,
    defsCouplingLocations: defsCoupling.length <= 60 ? defsCoupling : [`${defsCoupling.length} refs (list suppressed >60)`],
  };
}

// leaves + admitted rules + external deps (config-independent lookups, attached where meaningful)
const termLeaves = enumVariants(`${CORE}/term/term.rs`, "TermKind");
const typeLeaves = enumVariants(`${CORE}/ty/ty.rs`, "TypeKind");
const coreRules = manifestCount("docs/deps/core-manifest.txt");
const evalRules = manifestCount("docs/deps/eval-manifest.txt");
const builtinRules = manifestCount("docs/deps/builtins-manifest.txt");
const baseExt = externalDeps("covalence-pure-trusted");
const coreExt = externalDeps("covalence-core");
const evalExt = externalDeps("covalence-hol-eval");

const globals = {
  termKindVariants: termLeaves,
  typeKindVariants: typeLeaves,
  admittedRules: {
    coreManifest: coreRules,
    evalManifest: evalRules,
    builtinsManifest: builtinRules,
  },
  externalDeps: {
    base: baseExt ? { count: baseExt.length, crates: baseExt } : null,
    "base+HOL(core closure)": coreExt ? { count: coreExt.length, crates: coreExt } : null,
    "base+HOL+eval(hol-eval closure)": evalExt ? { count: evalExt.length, crates: evalExt } : null,
  },
};

// ---------------------------------------------------------------------------
// Print.
// ---------------------------------------------------------------------------
const pad = (s, n) => String(s).padEnd(n);
console.log("\nTCB AUDIT SURFACE  (tests excluded; lower = more auditable)\n");
console.log(pad("config", 16), pad("files", 6), pad("src-lines", 10), pad("unsafe", 7), pad("mint-sites", 11), pad("pub-api", 8), "defs:: coupling");
console.log("-".repeat(78));
for (const cfg of CONFIGS) {
  const r = report[cfg.name];
  console.log(
    pad(cfg.name, 16), pad(r.files, 6), pad(r.nonTestLoc, 10),
    pad(r.unsafe, 7), pad(r.mintSites, 11), pad(r.publicSurfaceTotal, 8), r.defsCoupling,
  );
}
console.log("\nLeaves:  TermKind variants =", termLeaves, " TypeKind variants =", typeLeaves);
console.log(
  "Admitted rules:  CoreLang(core-manifest) =", coreRules,
  " CoreEval(eval-manifest) =", evalRules,
  " Builtins =", builtinRules,
);
console.log(
  "External deps in TCB:  base =", baseExt?.length,
  " core-closure =", coreExt?.length,
  " hol-eval-closure =", evalExt?.length,
);
if (baseExt) console.log("  base:", baseExt.join(", "));

// The headline for the defs-out goal (E2: the catalogue + certs are now a
// DECLARED tier in hol/eval; what keeps base+HOL above its floor is the D3
// residue's couplings + the literal leaves):
const hol = report["base+HOL"], evl = report["base+HOL+eval"];
console.log(
  `\nTier gap: base+HOL src-lines ${hol.nonTestLoc} vs base+HOL+eval ${evl.nonTestLoc}` +
  `  (Δ ${evl.nonTestLoc - hol.nonTestLoc} lines of eval-tier trust a Thm<CoreLang> consumer never depends on)`,
);

if (report["base+HOL+eval"].unsafe > 0) console.log(`\n⚠ unsafe in TCB: ${report["base+HOL+eval"].unsafe} — must be 0`);

if (WRITE_JSON) {
  writeFileSync("docs/deps/tcb-audit.json", JSON.stringify({ generatedBy: "scripts/tcb-audit.mjs", configs: report, globals }, null, 2) + "\n");
  console.log("\nwrote docs/deps/tcb-audit.json");
}
console.log();
