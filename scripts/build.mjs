#!/usr/bin/env bun
// The covalence build-graph orchestrator.
//
// Covalence builds a *chain* of artifacts across three toolchains, and the
// links matter: the native `cov` binary embeds the web bundle (rust-embed,
// crates/server/core/src/static_files.rs), the web bundle imports the
// web-kernel WASM, and the web-kernel WASM is compiled from `crates/kernel/web`
// (+ wasm-bindgen + wasm-opt). Historically each `bun run build:*` script drove
// one link by hand, so building the server did NOT rebuild its WASM
// prerequisites — `bun run serve` even built the native binary *before* the
// web-kernel wasm, embedding a stale site.
//
// This orchestrator makes every target correct-by-construction: it models the
// dependency DAG explicitly, builds a target's upstreams first (topologically),
// and skips work that is already up to date (staleness by mtime / content
// hash). cargo remains the source of truth for Rust staleness — cargo-backed
// nodes always invoke cargo (fast when fresh) and let it decide; only the
// non-cargo post-processing (wasm-bindgen, wasm-opt, vite) is staleness-gated.
//
// Usage:
//   bun scripts/build.mjs <target> [<target> ...] [--force] [--list]
//   bun scripts/build.mjs --list          # show the graph
//   bun scripts/build.mjs all             # everything (native debug + wasm)
//
// Targets map 1:1 to the `bun run build:*` scripts in package.json.

import { spawnSync } from "node:child_process";
import { statSync, existsSync, mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { createHash } from "node:crypto";
import { fileURLToPath } from "node:url";
import { dirname, join } from "node:path";

const repoRoot = join(dirname(fileURLToPath(import.meta.url)), "..");
const cacheDir = join(repoRoot, "target", ".cov-build");

// ---------------------------------------------------------------------------
// small helpers
// ---------------------------------------------------------------------------

/** Where a tool comes from, for a clear "not built / not installed" error. */
const TOOL_HINTS = {
  cargo: "install Rust (https://rustup.rs) or enter the nix devshell (`nix develop` / direnv)",
  bun: "install Bun (https://bun.sh) or enter the nix devshell",
  "wasm-opt": "install binaryen (provides wasm-opt), or enter the nix devshell",
};

function have(bin) {
  return spawnSync(bin, ["--version"], { stdio: "ignore" }).status === 0 ||
    // some tools (wasm-opt) exit nonzero on --version but exist on PATH:
    spawnSync("sh", ["-c", `command -v ${bin}`], { stdio: "ignore" }).status === 0;
}

function requireTools(tools) {
  const missing = (tools ?? []).filter((t) => !have(t));
  if (missing.length) {
    const lines = missing.map((t) => `  - ${t}: ${TOOL_HINTS[t] ?? "not found on PATH"}`);
    throw new Error(`missing required tool(s):\n${lines.join("\n")}`);
  }
}

/** Run a command, inheriting stdio; throw on failure. */
function run(cmd, args, opts = {}) {
  const pretty = [cmd, ...args].join(" ");
  console.error(`  $ ${pretty}`);
  const r = spawnSync(cmd, args, { stdio: "inherit", cwd: repoRoot, ...opts });
  if (r.error) throw new Error(`failed to spawn \`${pretty}\`: ${r.error.message}`);
  if (r.status !== 0) throw new Error(`\`${pretty}\` exited with code ${r.status}`);
}

function mtime(path) {
  try {
    return statSync(join(repoRoot, path)).mtimeMs;
  } catch {
    return null; // missing
  }
}

/** Newest mtime among a set of glob patterns (relative to repoRoot). */
function newestInput(globs) {
  let newest = 0;
  for (const pattern of globs ?? []) {
    const glob = new Bun.Glob(pattern);
    for (const rel of glob.scanSync({ cwd: repoRoot, onlyFiles: true, dot: false })) {
      const m = mtime(rel);
      if (m != null && m > newest) newest = m;
    }
  }
  return newest;
}

/** Oldest mtime among declared outputs; null if any is missing (=> must build). */
function outputAge(outputs) {
  let oldest = Infinity;
  for (const out of outputs ?? []) {
    const m = mtime(out);
    if (m == null) return null;
    if (m < oldest) oldest = m;
  }
  return oldest === Infinity ? null : oldest;
}

function sha256File(absPath) {
  return createHash("sha256").update(readFileSync(absPath)).digest("hex");
}

function readCache(key) {
  const f = join(cacheDir, key);
  return existsSync(f) ? readFileSync(f, "utf8").trim() : null;
}
function writeCache(key, value) {
  mkdirSync(cacheDir, { recursive: true });
  writeFileSync(join(cacheDir, key), value);
}

// ---------------------------------------------------------------------------
// artifact graph
// ---------------------------------------------------------------------------
//
// Each node: { deps, tools, outputs, inputs, always, run }
//   deps    — upstream node names (built first)
//   tools   — binaries that must exist (checked before run, clear error if not)
//   outputs — representative output files (staleness: oldest of these)
//   inputs  — source globs (staleness: newest of these + upstream outputs)
//   always  — invoke `run` every time (for cargo/vite nodes that self-check);
//             staleness fields are then only used to skip *downstream* work
//   run     — build step; may itself hash-gate expensive sub-steps

const WEB_KERNEL_WASM = "apps/covalence-web/src/lib/kernel/covalence_web_kernel_bg.wasm";
const CARGO_WEB_KERNEL = "target/wasm32-unknown-unknown/release/covalence_web_kernel.wasm";

const GRAPH = {
  // covalence-web-kernel → wasm32-unknown-unknown → wasm-bindgen → wasm-opt.
  // cargo owns the .wasm freshness (always invoked); the bindgen+opt post-step
  // is gated on the content hash of cargo's output so we don't re-run the slow
  // wasm-opt pass when the kernel didn't change.
  "web-kernel": {
    tools: ["cargo", "bun", "wasm-opt"],
    outputs: [WEB_KERNEL_WASM],
    always: true, // cargo owns the .wasm freshness; the post-step is hash-gated below
    run() {
      run("cargo", ["build", "-p", "covalence-web-kernel", "--target", "wasm32-unknown-unknown", "--release"]);
      const src = join(repoRoot, CARGO_WEB_KERNEL);
      if (!existsSync(src)) throw new Error(`expected cargo output ${CARGO_WEB_KERNEL} not found`);
      const hash = sha256File(src);
      if (hash === readCache("web-kernel.hash") && existsSync(join(repoRoot, WEB_KERNEL_WASM))) {
        console.error("  (web-kernel wasm unchanged — skipping wasm-bindgen + wasm-opt)");
        return;
      }
      const outDir = "apps/covalence-web/src/lib/kernel";
      run("bun", ["scripts/wasm-bindgen.mjs", CARGO_WEB_KERNEL, "--out-dir", outDir, "--target", "web", "--omit-default-module-path"]);
      run("wasm-opt", ["-Oz", "--enable-reference-types", "--enable-bulk-memory", "--enable-nontrapping-float-to-int", "-o", WEB_KERNEL_WASM, WEB_KERNEL_WASM]);
      writeCache("web-kernel.hash", hash);
    },
  },

  // The SvelteKit browser bundle (adapter-static). Embedded into `cov` by
  // rust-embed. Staleness-gated: re-run vite only when the web-kernel wasm or a
  // web/package source is newer than the last bundle.
  web: {
    deps: ["web-kernel"],
    tools: ["bun"],
    outputs: ["apps/covalence-web/build/index.html"],
    inputs: [
      WEB_KERNEL_WASM,
      "apps/covalence-web/src/**",
      "apps/covalence-web/static/**",
      "apps/covalence-web/*.{js,ts,json}",
      "packages/*/src/**",
      "packages/*/package.json",
    ],
    run() {
      run("bun", ["run", "--filter", "covalence-web", "build"]);
    },
  },

  // The native `cov` binary (debug). Embeds apps/covalence-web/build via
  // rust-embed, so `web` is a hard dependency. cargo-owned: always invoked
  // (rust-embed emits rerun-if-changed for the embed folder, so a fresh bundle
  // triggers a relink; cargo is a no-op when nothing changed).
  native: {
    deps: ["web"],
    tools: ["cargo"],
    outputs: ["target/debug/cov"],
    always: true,
    run() {
      run("cargo", ["build", "-p", "covalence"]);
    },
  },

  "native-release": {
    deps: ["web"],
    tools: ["cargo"],
    outputs: ["target/release/cov"],
    always: true,
    run() {
      run("cargo", ["build", "-p", "covalence", "--release"]);
    },
  },

  // The VS Code extension WASM bundle (wasm32-wasip1-threads guest + esbuild).
  // Self-contained under the extension package; delegate to its own build.
  vscode: {
    tools: ["bun", "cargo"],
    always: true,
    run() {
      run("bun", ["run", "--filter", "covalence-vscode", "build"]);
    },
  },
};

// Virtual aggregate targets (lists of real nodes).
const AGGREGATES = {
  all: ["native", "vscode"], // `bun run build`: debug native (pulls web/web-kernel) + vscode wasm
  "all-release": ["native-release", "vscode"], // `bun run release`
};

// ---------------------------------------------------------------------------
// driver
// ---------------------------------------------------------------------------

// Whether a node must run. `always` nodes (cargo/vite) always invoke their tool
// and let it self-check. Otherwise a node is stale iff an output is missing or
// any source/upstream-output is newer than the oldest output. Downstream
// propagation rides on output *mtime*: an always-node that produces no new
// artifact (e.g. cargo no-op, hash-unchanged wasm) leaves mtimes untouched, so
// it does not force dependents to rebuild.
function needsBuild(node) {
  if (node.always) return true;
  const outAge = outputAge(node.outputs);
  if (outAge == null) return true; // an output is missing
  const depOutputs = (node.deps ?? []).flatMap((d) => GRAPH[d].outputs ?? []);
  return newestInput([...(node.inputs ?? []), ...depOutputs]) > outAge;
}

function buildNode(name, force, visiting, done, built) {
  if (done.has(name)) return;
  const node = GRAPH[name];
  if (!node) throw new Error(`unknown target: ${name}`);
  if (visiting.has(name)) throw new Error(`dependency cycle through ${name}`);
  visiting.add(name);
  for (const dep of node.deps ?? []) buildNode(dep, force, visiting, done, built);
  visiting.delete(name);

  if (force || needsBuild(node)) {
    console.error(`▶ ${name}`);
    requireTools(node.tools);
    node.run();
    built.add(name);
  } else {
    console.error(`✓ ${name} (up to date)`);
  }
  done.add(name);
}

function resolveTargets(args) {
  const out = [];
  for (const a of args) {
    if (AGGREGATES[a]) out.push(...AGGREGATES[a]);
    else out.push(a);
  }
  return out.length ? out : ["all"];
}

function printGraph() {
  console.error("covalence build graph:\n");
  for (const [name, node] of Object.entries(GRAPH)) {
    const deps = (node.deps ?? []).join(", ") || "—";
    console.error(`  ${name.padEnd(16)} deps: ${deps}`);
  }
  console.error("\naggregates:");
  for (const [name, list] of Object.entries(AGGREGATES)) {
    console.error(`  ${name.padEnd(16)} = ${list.join(", ")}`);
  }
}

function main() {
  const args = process.argv.slice(2);
  if (args.includes("--list") || args.includes("--help")) {
    printGraph();
    return;
  }
  const force = args.includes("--force");
  const targets = resolveTargets(args.filter((a) => !a.startsWith("--")));
  const done = new Set();
  const built = new Set();
  for (const t of targets) buildNode(t, force, new Set(), done, built);
  if (built.size === 0) console.error("nothing to do — all targets up to date.");
}

try {
  main();
} catch (e) {
  console.error(`\nbuild failed: ${e.message}`);
  process.exit(1);
}
