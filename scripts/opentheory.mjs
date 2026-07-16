#!/usr/bin/env bun
/**
 * Download (and cache) a large collection of OpenTheory packages and verify
 * them all on the native HOL kernel, reporting timing — a correctness AND
 * performance benchmark, mirroring the set.mm import bench.
 *
 * Usage:
 *   bun scripts/opentheory.mjs [pkg...]        # fetch from the OpenTheory repo
 *   bun scripts/opentheory.mjs --offline [pkg...]   # use the vendored assets
 *
 * Default package set: `base` — the std umbrella that transitively pulls the
 * whole standard library.
 *
 * Cache dir: $COV_OPENTHEORY_CACHE, else ${TMPDIR}/covalence-opentheory
 * (populated once; the layout is FileResolver-compatible for later offline use).
 */
import { existsSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { spawnSync } from "node:child_process";

const REPO = "https://opentheory.gilith.com/opentheory/packages";
const REPO_ROOT = join(import.meta.dir, "..");
const OFFLINE_DIRS = [
  join(REPO_ROOT, "assets/opentheory/gilith/std"),
  join(REPO_ROOT, "assets/opentheory/gilith"),
];
const log = (...a) => console.error("[opentheory]", ...a);

/** Build the release `cov` binary (with the `hol` feature) and return its path. */
function buildCov() {
  log("building cov (release, --features hol)…");
  const build = spawnSync(
    "cargo",
    ["build", "-p", "covalence", "--bin", "cov", "--features", "hol", "--release"],
    { stdio: "inherit" },
  );
  if (build.status !== 0) process.exit(build.status ?? 1);
  const meta = spawnSync("cargo", ["metadata", "--format-version=1", "--no-deps"])
    .stdout.toString()
    .match(/"target_directory":"([^"]+)"/)?.[1];
  const bin = `${meta ?? join(REPO_ROOT, "target")}/release/cov`;
  if (!existsSync(bin)) {
    log(`cov binary not found: ${bin}`);
    process.exit(1);
  }
  return bin;
}

function main() {
  const argv = process.argv.slice(2);
  const offline = argv.includes("--offline");
  const packages = argv.filter((a) => !a.startsWith("--"));
  if (packages.length === 0) packages.push("base");

  const cov = buildCov();

  const args = ["hol", "pkg", "--keep-going", "--stats"];
  if (offline) {
    for (const d of OFFLINE_DIRS) args.push("--dir", d);
    log(`offline: verifying [${packages.join(", ")}] against vendored assets`);
  } else {
    const cache = process.env.COV_OPENTHEORY_CACHE || join(tmpdir(), "covalence-opentheory");
    args.push("--repo", REPO, "--cache", cache);
    log(`online: verifying [${packages.join(", ")}] (repo ${REPO}, cache ${cache})`);
  }
  args.push(...packages);

  const started = Date.now();
  const run = spawnSync(cov, args, { stdio: "inherit" });
  const elapsed = ((Date.now() - started) / 1000).toFixed(1);

  if (run.status === 2) {
    log(
      "cov exited 2 — the `hol pkg` subcommand may be unavailable (build without the `hol` feature?)",
    );
    process.exit(2);
  }
  log(`done in ${elapsed}s (exit ${run.status ?? 0})`);
  process.exit(run.status ?? 0);
}

main();
