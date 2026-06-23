#!/usr/bin/env bun
/**
 * Shared helper: locate (or download) a `set.mm` to profile against.
 *
 * Resolution order:
 *   1. an explicit path argument, if given and present;
 *   2. `$COV_SET_MM`, if set and present;
 *   3. a cached download at `${TMPDIR}/covalence-set.mm` (downloaded once).
 *
 * set.mm is ~50 MB; the download is cached so repeated profiling runs reuse it.
 */
import { existsSync, statSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

const SET_MM_URL = "https://raw.githubusercontent.com/metamath/set.mm/develop/set.mm";
const log = (...a) => console.error("[setmm]", ...a);

/** Return a usable path to set.mm, downloading to a temp cache if necessary. */
export async function ensureSetMm(explicit) {
  for (const cand of [explicit, process.env.COV_SET_MM]) {
    if (cand && existsSync(cand)) return cand;
  }
  const cache = join(tmpdir(), "covalence-set.mm");
  // Treat a suspiciously small cache file as incomplete and re-fetch.
  if (existsSync(cache) && statSync(cache).size > 10_000_000) {
    log(`using cached ${cache} (${(statSync(cache).size / 1e6).toFixed(1)} MB)`);
    return cache;
  }
  log(`downloading set.mm → ${cache} …`);
  const res = await fetch(SET_MM_URL);
  if (!res.ok) {
    log(`download failed: HTTP ${res.status} from ${SET_MM_URL}`);
    process.exit(1);
  }
  await Bun.write(cache, res);
  log(`downloaded ${(statSync(cache).size / 1e6).toFixed(1)} MB`);
  return cache;
}

/** Build the `mm_import_bench` example (release) and return its binary path. */
export function buildBench() {
  const { spawnSync } = require("bun");
  log("building mm_import_bench (release)…");
  const build = spawnSync(
    ["cargo", "build", "-p", "covalence-hol", "--example", "mm_import_bench", "--release"],
    { stdout: "inherit", stderr: "inherit" },
  );
  if (build.exitCode !== 0) process.exit(build.exitCode ?? 1);
  const meta = spawnSync(["cargo", "metadata", "--format-version=1", "--no-deps"])
    .stdout.toString()
    .match(/"target_directory":"([^"]+)"/)?.[1];
  const bin = `${meta ?? "target"}/release/examples/mm_import_bench`;
  if (!existsSync(bin)) {
    log(`bench binary not found: ${bin}`);
    process.exit(1);
  }
  return bin;
}
