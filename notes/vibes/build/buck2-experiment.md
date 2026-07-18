+++
id = "N000J"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:claude"
at = "2026-07-15T23:08:56+01:00"
source = "legacy"
agent = "claude"
harness = "claude"
+++

# Buck2 experiment — evaluation & incremental path

> Status: **evaluation / aspirational.** cargo is and stays the source of truth.
> This note records why, and the concrete path to try Buck2 on a slice when we
> want the experience (for the eventual `cog`-as-build-system dogfooding).

## Why not a full migration (2026)

Researched against current sources. For a 62-crate Rust + WASM + PyO3 workspace
that already builds fine with cargo, a *full* Buck2 migration is poor ROI today:

- **First-party BUCK files are hand-authored.** Reindeer only buckifies
  *third-party* deps; there is no mature Cargo-workspace → BUCK generator for
  first-party crates. 62 interdependent crates = a lot of hand-written, hand-
  maintained `BUCK` files.
- **WASM is DIY.** No published Buck2 + wasm-bindgen / wasm-opt recipe exists.
  We'd re-encode `cargo rustc --target … + wasm-bindgen + wasm-opt` (including
  the `wasm32-wasip1-threads` thread flags and the rustc-emits-bulk-memory vs.
  wasm-opt version coupling) as custom rules — the most painful part, and a
  maintenance tax whenever the wasm toolchain moves.
- **PyO3/maturin has no Buck2 story.** Another hand-rolled `cdylib` +
  wheel-assembly genrule.
- **The concrete pain is cross-worktree caching, and Buck2 is the heavy answer.**
  Our actual friction is that separate git worktrees don't share Rust build
  artifacts. That's solved directly by **sccache** (now in the flake; object
  cache in `$SCCACHE_DIR` outside any checkout → fresh worktrees reuse compiled
  deps) — see [`flake.nix`](../../../flake.nix), `COV_CACHE` toggle. Buying Buck2
  *just* for this is a battleship for a pond.
- **What Buck2 actually gives "for free" — a dependency DAG with staleness — we
  now have** via [`scripts/build.mjs`](../../../scripts/build.mjs) (the
  cross-toolchain artifact graph: web-kernel wasm → web bundle → rust-embed'd
  `cov`). That was the real requirement.

**When Buck2 *would* pay off:** many-hour cold builds, a team needing shared
remote cache / remote execution (BuildBuddy, NativeLink, EngFlow…), or CI cost
dominated by rebuilds. At single-maintainer / 62-crate scale, not yet.

## Why keep the tooling around anyway

`next-stage.md` wants Buck2 *experience* on purpose: we eventually want to
dogfood **`cog` as our build system**, and want to reason about `cog`/Buck
compatibility. So the flake ships `buck2` + `reindeer` (+ `sccache`) and this
note records the incremental path — we can spike it on a leaf without disturbing
cargo.

## Incremental path (when we spike it)

1. **Third-party via reindeer** (low cost, high signal):
   - `mkdir -p buck/third-party/rust` with a vendored `Cargo.toml`.
   - `reindeer --third-party-dir buck/third-party/rust vendor`
   - `reindeer --third-party-dir buck/third-party/rust buckify`
   - Expect per-crate `fixups/<pkg>/fixups.toml` for build-script-bearing deps.
2. **One leaf first-party crate** (e.g. `crates/lib/hash` = `covalence-hash`, no
   wasm, few deps): hand-write a `BUCK` with `rust_library`, depend on the
   reindeer targets, `buck2 build //crates/lib/hash:covalence-hash`.
3. **Nix toolchain bridge:** Buck2 wants to manage its own toolchains, which
   fights the Nix-provided one. Use `tweag/buck2.nix`'s `nix_rust_toolchain`
   rule to feed the flake's rustc into Buck2 (`nix flake new --template
   github:tweag/buck2.nix` as a reference). Do **not** put WASM / maturin on
   Buck2's critical path during the spike.
4. **Stop and evaluate** before going wider. The bar to expand past a leaf is a
   concrete win cargo+sccache can't give us.

Keep all of this under a `buck/` dir and out of the cargo build path, so the
experiment never gates a normal `cargo build` / `bun run build`.

## Sources

reindeer manual; buck2 prelude `rust_library`/`rust_binary`; Tweag "Integrating
Nix and Buck2" + `tweag/buck2.nix`; sccache `SCCACHE_DIR`/worktree caveats;
howardjohn "Sharing Rust Build Cache". (URLs in the session research log.)
