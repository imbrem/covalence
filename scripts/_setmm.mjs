#!/usr/bin/env bun
/**
 * Shared helper: locate (or download) a **pinned** `set.mm` / `iset.mm` to
 * benchmark and profile against.
 *
 * The download is pinned to a fixed commit of metamath/set.mm (`SET_MM_REV`)
 * so benchmark numbers are comparable across runs and machines — the `develop`
 * branch moves daily. Bump the pin deliberately (and note it in
 * `crates/kernel/hol/init/PERF.md` if import numbers shift).
 *
 * Resolution order:
 *   1. an explicit path argument, if given and present;
 *   2. `$COV_SET_MM` (resp. `$COV_ISET_MM`), if set and present;
 *   3. a per-revision cache at `${TMPDIR}/covalence-<file>-<rev12>` (downloaded
 *      once; a re-pin lands in a fresh cache file automatically).
 *
 * set.mm is ~50 MB, iset.mm ~12 MB; both cache to the same scheme.
 */
import { existsSync, statSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

/** The pinned metamath/set.mm revision (develop @ 2026-07-13). */
export const SET_MM_REV = "bcfef9892b6103ba9046bf683b4903d2ad081a41";

const log = (...a) => console.error("[setmm]", ...a);

/** Minimum plausible size per file — a smaller cache file is a truncated
 * download and gets re-fetched. */
const MIN_BYTES = { "set.mm": 10_000_000, "iset.mm": 2_000_000 };

/**
 * Return a usable path to `file` ("set.mm" or "iset.mm") at the pinned
 * revision, downloading to a temp cache if necessary. `explicit` / the
 * `$COV_SET_MM`-style env var override the pin (for testing local copies).
 */
export async function ensureMm(file, explicit) {
  const envVar = file === "iset.mm" ? "COV_ISET_MM" : "COV_SET_MM";
  for (const cand of [explicit, process.env[envVar]]) {
    if (cand && existsSync(cand)) {
      log(`using ${cand} (${envVar}/arg override — NOT the pinned revision)`);
      return cand;
    }
  }
  const cache = join(tmpdir(), `covalence-${file}-${SET_MM_REV.slice(0, 12)}`);
  if (existsSync(cache) && statSync(cache).size > (MIN_BYTES[file] ?? 1_000_000)) {
    log(
      `using cached ${cache} (${(statSync(cache).size / 1e6).toFixed(1)} MB, pinned ${SET_MM_REV.slice(0, 12)})`,
    );
    return cache;
  }
  const url = `https://raw.githubusercontent.com/metamath/set.mm/${SET_MM_REV}/${file}`;
  log(`downloading ${file} @ ${SET_MM_REV.slice(0, 12)} → ${cache} …`);
  const res = await fetch(url);
  if (!res.ok) {
    log(`download failed: HTTP ${res.status} from ${url}`);
    process.exit(1);
  }
  await Bun.write(cache, res);
  log(`downloaded ${(statSync(cache).size / 1e6).toFixed(1)} MB`);
  return cache;
}

/** Return a usable path to the pinned set.mm (see [`ensureMm`]). */
export async function ensureSetMm(explicit) {
  return ensureMm("set.mm", explicit);
}

/** Build a release example binary in `pkg` and return its path. */
export function buildExample(pkg, example) {
  const { spawnSync } = require("bun");
  log(`building ${example} (release)…`);
  const build = spawnSync(
    ["cargo", "build", "-p", pkg, "--example", example, "--release"],
    { stdout: "inherit", stderr: "inherit" },
  );
  if (build.exitCode !== 0) process.exit(build.exitCode ?? 1);
  const meta = spawnSync(["cargo", "metadata", "--format-version=1", "--no-deps"])
    .stdout.toString()
    .match(/"target_directory":"([^"]+)"/)?.[1];
  const bin = `${meta ?? "target"}/release/examples/${example}`;
  if (!existsSync(bin)) {
    log(`bench binary not found: ${bin}`);
    process.exit(1);
  }
  return bin;
}

/** Build the `mm_import_bench` example (release) and return its binary path. */
export function buildBench() {
  return buildExample("covalence-hol", "mm_import_bench");
}
