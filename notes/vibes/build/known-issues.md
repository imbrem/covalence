+++
id = "N000K"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:claude"
at = "2026-07-03T21:05:38+01:00"
source = "legacy"
agent = "claude"
harness = "claude"
+++

# Build & test — known issues

Environment/toolchain gotchas, not code bugs. CI (newer stable toolchain + full
service/browser/Python setup) is the source of truth.

## 1. `libsqlite3-sys` needs a newer rustc than some local toolchains

`libsqlite3-sys ≥ 0.38` uses the unstable `cfg_select!` macro in its build
script, which only compiles where `cfg_select` is stable. On the project floor
(`1.94.1`) the whole-workspace build fails to compile the sqlite chain
(`error[E0658]: use of unstable library feature cfg_select`).

**Handling:** `crates/lib/sqlite/Cargo.toml` pins `rusqlite = "0.39"`, which
pulls `libsqlite3-sys 0.37.0` (pre-`cfg_select`). `rusqlite 0.40` hard-requires
`libsqlite3-sys ^0.38`, so the pin must be at the `rusqlite` minor, not the
lockfile. Our sqlite usage is trivial and version-stable (`open`,
`pragma_update`, `busy_timeout`), so the downgrade is behaviour-neutral.

**Long-term:** raise the toolchain floor (a `rust-toolchain.toml` ≥ the rustc
that stabilised `cfg_select`) and restore `rusqlite = "0.40"`.

## 2. `bun test` is a heavyweight meta-runner

`bun test` fans out to several suites:

- `rust.test.ts` spawns `cargo test` with a 300 s timeout — a cold whole-
  workspace build exceeds it on a slow machine (passes given time, e.g.
  `cargo test --workspace` on a warm target). A timeout, not a failure.
- `api.test.ts` / `e2e.test.ts` / `ui.test.ts` need a running `cov serve`
  and/or a browser.
- `python.test.ts` needs a maturin-built Python extension.

In a bare container these go red regardless of code. Run the relevant slice
directly when iterating (`cargo test -p <crate>`); rely on CI for the full matrix.

## 3. Outbound deps go through the agent proxy

Fresh `cargo`/`bun` fetches work via the configured `HTTPS_PROXY` + CA bundle.
Offline (`--offline`) resolution of the whole workspace fails when any transitive
dep isn't cached yet.
