# Build & test — known issues

Environment-specific build/test gotchas and how they're handled. These are
**not code bugs**; they're toolchain/sandbox mismatches. CI (newer stable
toolchain + full service/browser/Python setup) is the source of truth.

## 1. `libsqlite3-sys` needs a newer rustc than some local toolchains

`libsqlite3-sys ≥ 0.38` uses the unstable `cfg_select!` macro in its **build
script**, which only compiles on a rustc where `cfg_select` is stable. On older
stable toolchains (e.g. `1.94.1`, the project floor) the whole-workspace build
fails to even compile the sqlite chain:

```
error[E0658]: use of unstable library feature `cfg_select`
  --> .../libsqlite3-sys-0.38.x/build.rs
```

**Current handling:** `crates/covalence-sqlite/Cargo.toml` pins
`rusqlite = "0.39"`, which pulls `libsqlite3-sys 0.37.0` (pre-`cfg_select`) and
builds on `1.94.1`. `rusqlite 0.40` hard-requires `libsqlite3-sys ^0.38`, so a
lockfile-only pin is impossible — the pin has to be at the `rusqlite` minor.
covalence's sqlite usage is trivial and version-stable (`open`,
`pragma_update`, `busy_timeout`), so the downgrade is behaviour-neutral.

**Alternative (preferred long-term):** raise the toolchain floor (a
`rust-toolchain.toml` channel ≥ the rustc that stabilised `cfg_select`) and
restore `rusqlite = "0.40"`. Not done here because the dev sandbox only had
`1.94.1` installed, so it wouldn't unblock local builds anyway.

## 2. `bun test` is a heavyweight meta-runner; not fully green in a bare sandbox

`bun test` fans out to several suites (`tests/*.test.ts`):

- **`rust.test.ts`** spawns `cargo test` with a hard **300 s** timeout. A *cold*
  whole-workspace build exceeds that on a slow machine — the suite itself
  passes given time (`cargo test --workspace` → 153 `test result: ok`, 0 failed,
  on a warm target). Not a failure, a timeout.
- **`api.test.ts` / `e2e.test.ts` / `ui.test.ts`** need a running `cov serve`
  backend and/or a browser.
- **`python.test.ts`** needs a maturin-built Python extension.

In a bare container without that infrastructure these go red regardless of code.
**Run the relevant slice directly** when iterating, e.g.
`cargo test -p <crate>`, and rely on CI for the full matrix.

## 3. Outbound deps go through the agent proxy

Fresh `cargo`/`bun` fetches work via the configured `HTTPS_PROXY` + CA bundle.
A first build of a new crate may need network; if a fetch 403s, see
`/root/.ccr/README.md`. Offline (`--offline`) resolution of the *whole*
workspace fails when any transitive dep isn't cached yet.
