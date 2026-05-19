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
- `crates/covalence-kernel/` — Execution core: trait definitions + in-process engine
  - `src/traits.rs` — `SyncBackend`, `AsyncBackend`, `BackendInfo`, `KernelError`
  - `src/kernel.rs` — `Kernel` struct (BlobStore + WasmEngine), `BlobStore` enum; implements both traits
  - Features: `engine` (wasmtime + store), `sqlite` (SQLite-backed BlobStore)
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
- `crates/covalence-wasm/` — WASM/WAT gateway
  - `src/validate.rs` — `validate_wat()` (WAT→WASM), `wasm_to_wat()` (WASM→WAT) — always available
  - `src/parse.rs` — `parse_module()`, `parse_component()` — binary inspection via wasmparser
  - `src/engine.rs` — `WasmEngine`, proposition checking — gated behind `runtime` feature
  - `src/lib.rs` — `WasmError` enum, re-exports `wasmtime` under `runtime`
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

```
covalence-wasm (WASM gateway)
  ├─ base: validate_wat(), wasm_to_wat(), parse_module(), parse_component()
  └─ [runtime]: WasmEngine, PropResult, PropError (re-exports wasmtime)

covalence-kernel (execution core + trait definitions)
  ├─ [default]: SyncBackend, AsyncBackend, BackendInfo, KernelError (traits only, no heavy deps)
  └─ [engine]: Kernel, BlobStore (SharedMemoryStore + WasmEngine)
      └─ [sqlite]: BlobStore::Sqlite variant

covalence-client (remote backend implementations)
  ├─ [sync]: SyncHttpBackend (ureq + raw UDS)
  └─ [async]: AsyncHttpBackend (hyper + UDS)
      depends on covalence-kernel (default — traits only, no wasmtime)

covalence-repl (Session + command evaluation)
  ├─ Uses Box<dyn SyncBackend> from covalence-kernel
  ├─ Always depends on covalence-wasm (base) for WAT ops
  └─ [fetch]: ureq for store-url

covalence-proto (discovery + config only)
  └─ No client code — just registration, discovery, and default paths

covalence-serve (HTTP server)
  ├─ Creates a Kernel (with BlobStore from ServeConfig), uses it for all handlers
  └─ AppState holds Kernel (Clone is cheap — Arc internals)

covalence (binary)
  ├─ Standalone: Kernel → Box<dyn SyncBackend> for REPL
  └─ Connected: SyncHttpBackend → Box<dyn SyncBackend> for REPL
```

**Key rules:**
- `SyncBackend` trait is dyn-compatible (for REPL's `Box<dyn SyncBackend>`)
- `AsyncBackend` trait uses native `async fn` (NOT dyn-compatible — used with concrete types)
- Only `covalence-kernel[engine]` and `covalence-serve` pull in wasmtime
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
