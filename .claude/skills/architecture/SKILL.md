---
user-invocable: false
description: Covalence repo layout, dependency graph, and key architectural rules
---

## Repo Layout

- `crates/covalence/` — Main binary crate (`cov` CLI)
  - `src/main.rs` — Entry point with clap derive; dispatches to `cov lsp`, `cov cog`, `cov serve`, `cov repl`
  - `src/highlight.rs` — S-expression syntax highlighting for the REPL
  - `src/lib.rs` — Shared constants (`VERSION`, `TARGET`)
  - `build.rs` — Sets `COV_TARGET` env var from the Cargo build target triple
- `crates/covalence-pure/` — **TCB**: Isabelle/Pure–shaped LF. `Term`/`Type`/`Thm`, 8 LF + 6 equality rules + `inst_tfree` + `define` + `obs_eq`. Locally-nameless, intrinsic typing, parametric-ε-sound observations. `DynObs` wraps any `Arc<dyn Any + Send + Sync>` compared by pointer identity. WIT package `cov:pure@0.1.0` exposes the API to wasm guests (host bindings in `covalence-wasm::pure`).
- `crates/covalence-pure-shell/` — non-TCB shell: handler-driven sexp serialisation (`ObsSerializer`/`ObsParser`), content hashing (`ObsHasher`), pretty-printing. Caller-supplied trait impls for each observer type.
- `crates/covalence-pure-test-guest/` — wasm32 cdylib using `wit_bindgen::generate!` against `cov:pure/api`; loaded by `crates/covalence-wasm/tests/pure_guest_integration.rs` for end-to-end WIT-driven proving. Template for future `cov:kernel`/`cov:hol-light` test guests.
- `crates/covalence-kernel/` — **HOL kernel (LEGACY, planned for rewrite).** Current contents: `arena.rs`, `egraph.rs`, `eprop.rs`, `hash.rs`, `id.rs`, `kernel.rs`, `primop.rs`, `prop.rs`, `reduce.rs`, `subst.rs`, `term.rs`, `ty.rs`, `uf.rs`. Migration plan in `docs/design/proposals/stacked-pure-hol/next-stages.md`: keep the crate name but empty it out and rebuild as an orchestration shell over `covalence-pure` + forthcoming `covalence-hol` + `covalence-store` + WASM evaluator + tree-store. The new direction never trusts BLAKE3 collision-freedom globally; cryptographic facts are user-asserted axioms conditional on `inStore` predicates.
  - The Sync/Async backend traits (`SyncBackend`, `AsyncBackend`, `BackendInfo`, `KernelError`) now live in `crates/covalence-shell/` (`pub use traits::{...}` in `src/lib.rs`). Update this section when the kernel is re-integrated with the shell.
- `crates/covalence-client/` — Remote backend implementations
  - `src/sync_client.rs` — `SyncHttpBackend` (ureq for TCP, raw HTTP/1.1 for Unix domain sockets)
  - `src/async_client.rs` — `AsyncHttpBackend` (hyper for TCP + UDS)
  - Features: `sync` (ureq), `async` (hyper)
- `crates/covalence-hash/` — Cryptographic hash types (`O256`, `IdentityHasher`), git hashing (feature-gated on `git`)
- `crates/covalence-store/` — Generic store traits (`StoreGet`, `StoreGetRef`, `StorePut`, `StorePutMut`) and implementations
  - `MemoryStore`/`SharedMemoryStore` (feature `memory`, default)
  - `SqliteStore` (feature `sqlite`, backed by `covalence-sqlite`)
- `crates/covalence-sqlite/` — Low-level SQLite blob store (rusqlite)
- `crates/covalence-sexp/` — S-expression parser/printer (`parse()`, `prettyprint()`, `offset_to_line_col()`)
- `crates/covalence-wasm/` — WASM/WAT gateway (see `wasm-guide` skill)
  - `src/validate.rs` — `compile_wat()` (WAT→WASM), `wasm_to_wat()` (WASM→WAT) — always available
  - `src/parse.rs` — `parse_module()`, `parse_component()` — binary inspection via wasmparser
  - `src/build.rs` — programmatic `ModuleBuilder` (~840 LoC)
  - `src/component.rs` — `encode_core_as_component`
  - `src/val.rs` — engine-agnostic `Val` / `ValType` (component-model values)
  - `src/engine.rs` — one-line `pub use wasmtime;` gated behind `runtime` feature (no higher-level abstraction yet)
  - `src/lib.rs` — `WasmError` enum
- `crates/covalence-lsp/` — Language server library (used by `cov lsp`)
  - `src/lib.rs` — LSP handlers for sexp files (`.smt`, `.smt2`, `.alethe`, `.cov`) and WAT files (`.wat`)
- `crates/covalence-git/` — Cogit VCS library (used by `cov cog`)
- `crates/covalence-serve/` — Web server library (used by `cov serve`)
  - `src/lib.rs` — `ServeConfig`, `ServeError`, `AppState` (holds `Kernel`), `run_serve()`
  - `src/api.rs` — REST API handlers (blobs, WAT, eval, decide, etc.)
  - `src/eval.rs` — `server_session()` — creates a REPL Session backed by a Kernel
  - `src/static_files.rs` — rust-embed static file serving with SPA fallback (feature `static`)
  - `build.rs` — Warns if `apps/covalence-web/build/` is missing (only when `static` feature enabled)
- `crates/covalence-proto/` — Service discovery + configuration
  - `src/discovery.rs` — Server registration/discovery via XDG runtime dir
  - `src/config.rs` — Default paths (XDG data dir)
  - `src/error.rs` — `DiscoveryError`
- `apps/covalence-web/` — SvelteKit web app (adapter-static, SPA mode)
  - `src/lib/api.ts` — API client; base URL configurable via `VITE_COV_API_BASE` env var
  - `src/routes/+page.svelte` — Landing page with API health monitor (polls `/api/health` every `HEALTH_POLL_MS`)
  - `build/` — Static output embedded into the Rust binary (gitignored)
- `packages/covalence-ui/` — Shared Svelte 5 component library (scaffold, for future use)
- `extensions/covalence-vscode/` — VSCode extension (desktop + web)
  - `src/extension.ts` — Extension activation, LSP startup, restart command
  - `src/server.ts` — LSP server creation: detects native `cov` binary, falls back to WASM
  - `scripts/build.ts` — Build script (cargo rustc → esbuild → copy wasm)
  - `syntaxes/` — TextMate grammars for SMT (`smt.tmLanguage.json`) and WAT (`wat.tmLanguage.json`)
  - `dist/` — Final bundles (gitignored)

## Dependency Graph

**Status: partially stale — needs a fresh audit.** The high-level shape (covalence-wasm base vs runtime feature; client/repl staying lightweight; serve using Kernel + traits) is still directionally right, but specific claims about which crate owns which trait have moved (see kernel/shell note above). Verify against `Cargo.toml` files before relying on the details below.

```
covalence-wasm (WASM gateway)
  ├─ base: compile_wat(), wasm_to_wat(), parse_module(), parse_component(), build::*, encode_core_as_component
  └─ [runtime]: re-exports wasmtime (no abstraction layer yet — direct wasmtime usage in consumers)

covalence-shell (backend traits — formerly in covalence-kernel)
  └─ SyncBackend, AsyncBackend, BackendInfo, KernelError

covalence-client (remote backend implementations) — depends on covalence-shell
  ├─ [sync]: SyncHttpBackend (ureq + raw UDS)
  └─ [async]: AsyncHttpBackend (hyper + UDS)

covalence-repl (Session + command evaluation)
  ├─ Uses Box<dyn SyncBackend> from covalence-shell
  ├─ Always depends on covalence-wasm (base) for WAT ops
  └─ [fetch]: ureq for store-url

covalence-proto (discovery + config only)
  └─ No client code — just registration, discovery, and default paths

covalence-serve (HTTP server) — depends on covalence-shell::KernelError
```

**Key rules (still applicable):**
- `SyncBackend` trait is dyn-compatible (for REPL's `Box<dyn SyncBackend>`)
- `AsyncBackend` trait uses native `async fn` (NOT dyn-compatible — used with concrete types)
- `covalence-repl` and `covalence-client` stay lightweight (no wasmtime)

## CLI (`cov`)

Uses clap derive for arg parsing, `color-eyre` for error reporting (native only), and `tracing` + `tracing-subscriber` for logging (default level: `info`, override with `RUST_LOG`).

Features (all default, all compile on WASM except native-only deps are target-gated):
- `lsp` — `cov lsp` subcommand
- `cogit` — `cov cog` subcommand
- `serve` — `cov serve` subcommand (prints error on WASM; axum/tokio deps are `cfg(not(wasm))`)
- `repl` — `cov repl` subcommand (interactive S-expression REPL with syntax highlighting)

## REPL (`cov repl`)

Interactive S-expression evaluator with a content-addressed blob store. Backend is selected at startup:
- `--connect URL` → `SyncHttpBackend` (remote)
- `--standalone` → `Kernel` (in-process)
- Default → auto-discovery (find running server) → fallback to `Kernel`

Storage: `--store` enables SQLite persistence, `--memory` (default) uses in-memory.

Commands:
- `(store "data")` — hash and store inline text as a blob
- `(store-url "url")` — fetch URL content and store as blob
- `(store-file "path")` — read file and store as blob
- `(read <hash>)` — print blob as UTF-8 text
- `(read-wat <hash>)` — decompile blob as WASM→WAT
- `(module ...)` — compile WAT module, store as blob
- `(component ...)` — compile WAT component, store as blob
- `(parse-module <hash>)` — inspect WASM module imports/exports
- `(parse-component <hash>)` — inspect WASM component imports/exports
- `(decide <hash>)` — decide if a proposition (WASM component) calls attest() on startup
- `(list)` — list all stored blob hashes
- `(status)` — show backend connection info
- `(help)` — show available commands
- `(arrow-stats <hash>)` — parse blob as Arrow IPC, print schema + row/batch counts (requires `covalence-repl/arrow`)
- `(parquet-stats <hash>)` — parse Parquet stats; dispatches on `is_tree(hash)` — a tree is scanned as a hive-partitioned dataset (`key=value/` dirs with `.parquet` leaves), a blob is parsed as a single file (requires `covalence-repl/parquet`)
