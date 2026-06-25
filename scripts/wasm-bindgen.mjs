#!/usr/bin/env bun
// Version-matched `wasm-bindgen` wrapper.
//
// The bindgen schema is version-locked: the CLI must match the `wasm-bindgen`
// crate in Cargo.lock *exactly*, or `build:web-kernel` fails with a schema
// mismatch. Relying on a bare `wasm-bindgen` from PATH is fragile — e.g. under
// Nix a store-provided CLI can shadow a matching one in ~/.cargo/bin, so PATH
// order, not the lockfile, decides the version.
//
// This wrapper resolves the right binary by *content*: it scans every
// wasm-bindgen on PATH (plus ~/.cargo/bin) and runs the one whose --version
// matches Cargo.lock, by absolute path — immune to shadowing. Only if none
// matches does it install the pinned version. Then it execs that binary with
// the forwarded arguments.
import { spawnSync } from "node:child_process";
import { readFileSync, existsSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { dirname, join } from "node:path";
import { homedir } from "node:os";

const repoRoot = join(dirname(fileURLToPath(import.meta.url)), "..");

function lockedVersion() {
  const lock = readFileSync(join(repoRoot, "Cargo.lock"), "utf8");
  for (const block of lock.split("[[package]]")) {
    if (/^\s*name = "wasm-bindgen"\s*$/m.test(block)) {
      const m = block.match(/^\s*version = "([^"]+)"\s*$/m);
      if (m) return m[1];
    }
  }
  throw new Error("could not find wasm-bindgen version in Cargo.lock");
}

function versionOf(bin) {
  const r = spawnSync(bin, ["--version"], { encoding: "utf8" });
  if (r.status !== 0 || !r.stdout) return null;
  const m = r.stdout.match(/wasm-bindgen\s+([0-9.]+)/);
  return m ? m[1] : null;
}

function candidates() {
  const seen = new Set();
  const out = [];
  const push = (p) => {
    if (p && !seen.has(p) && existsSync(p)) {
      seen.add(p);
      out.push(p);
    }
  };
  const w = spawnSync("which", ["-a", "wasm-bindgen"], { encoding: "utf8" });
  if (w.status === 0 && w.stdout) {
    for (const line of w.stdout.split("\n")) push(line.trim());
  }
  push(join(homedir(), ".cargo", "bin", "wasm-bindgen"));
  return out;
}

function findMatching(want) {
  for (const bin of candidates()) {
    if (versionOf(bin) === want) return bin;
  }
  return null;
}

const want = lockedVersion();
let bin = findMatching(want);

if (!bin) {
  console.log(
    `[wasm-bindgen] no CLI matching Cargo.lock (${want}) found on PATH — installing…`,
  );
  const hasBinstall =
    spawnSync("cargo", ["binstall", "-V"], { stdio: "ignore" }).status === 0;
  const cmd = hasBinstall
    ? ["binstall", "-y", "--force", `wasm-bindgen-cli@${want}`]
    : ["install", "-f", "wasm-bindgen-cli", "--version", want, "--locked"];
  const r = spawnSync("cargo", cmd, { stdio: "inherit" });
  if (r.status !== 0) {
    console.error(
      `[wasm-bindgen] failed to install wasm-bindgen-cli ${want}. Install manually:\n` +
        `    cargo install -f wasm-bindgen-cli --version ${want}`,
    );
    process.exit(r.status ?? 1);
  }
  // Use the freshly installed binary by absolute path (PATH may be shadowed).
  bin = findMatching(want) ?? join(homedir(), ".cargo", "bin", "wasm-bindgen");
  if (versionOf(bin) !== want) {
    console.error(`[wasm-bindgen] installed CLI is not ${want}; aborting.`);
    process.exit(1);
  }
}

const run = spawnSync(bin, process.argv.slice(2), { stdio: "inherit" });
process.exit(run.status ?? 1);
