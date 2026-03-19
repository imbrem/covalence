# Covalence

Theorem prover with Ion language tooling. Monorepo with Rust crates and a VSCode browser extension.

## Build & Run

```sh
bun install                # install JS dependencies
bun run build              # full build: cargo rustc (WASI WASM) + esbuild
bun run build:wasm         # WASM only
bun run dev                # start dev server on localhost:3000 (open in browser)
cargo check                # check Rust crates
cargo test                 # run Rust tests
```

## Prerequisites

- **Rust nightly** — required for `wasm32-wasip1-threads` thread support (stable Rust hardcodes `UNSUPPORTED_PLATFORM` for WASI thread spawning; nightly ≥1.96.0 removes this guard)
- **Rust targets**: `wasm32-wasip1-threads`, `wasm32-unknown-unknown`
- **Bun** — JS package manager and build script runner
- **wasm-pack**, **wasm-bindgen-cli**, **binaryen** (`wasm-opt`)

## Repo Layout

- `crates/covalence-ion/` — Ion parsing library (empty scaffold)
- `crates/covalence-lsp/` — Language server, compiles to both native binary and WASI WASM
  - `src/lib.rs` — Shared LSP handlers (`handle_request`, `handle_notification`, `server_capabilities`)
  - `src/main.rs` — Binary entry point using `lsp-server::Connection::stdio()`
- `extensions/covalence-vscode/` — VSCode extension (desktop + web)
  - `src/extension.ts` — Loads WASM via `@vscode/wasm-wasi`, creates `LanguageClient`
  - `scripts/build.ts` — Build script (cargo rustc → esbuild → copy wasm)
  - `dist/` — Final bundles (gitignored)

## Architecture

The Rust LSP binary compiles to `wasm32-wasip1-threads` via `cargo rustc`. It uses `lsp-server::Connection::stdio()` which spawns threads for reader/writer — this requires **nightly Rust** (see Prerequisites). The WASM binary runs inside a WASI process in the extension via `@vscode/wasm-wasi` and `@vscode/wasm-wasi-lsp`, which bridges WASI stdio to LSP `MessageTransports`.

```
VSCode ← LanguageClient ← @vscode/wasm-wasi-lsp ← WASI Process (Rust WASM) ← lsp-server
```

The same `src/extension.ts` serves both desktop and web bundles. esbuild aliases `vscode-languageclient/node` → `vscode-languageclient/browser` for the web build.

### WASM Memory

Memory is fixed at 160 pages (10 MB). This value must match in two places:
- `scripts/build.ts`: linker args `--initial-memory=10485760 --max-memory=10485760`
- `src/extension.ts`: `wasm.createProcess(... { initial: 160, maximum: 160, shared: true })`

## Conventions

- Rust edition 2024 (nightly), workspace resolver 2
- TypeScript: strict mode, ES2022 target, bundler module resolution
- Build tool: esbuild (CJS bundles for both desktop and web, with browser alias for web)
- Package manager: Bun (workspace root), with `"workspaces": ["extensions/*"]`
- WASM target: `wasm32-wasip1-threads` via `cargo rustc`
- LSP framework: `lsp-server` 0.7 + `lsp-types` 0.97 (rust-analyzer ecosystem)
- Extension runtime: `@vscode/wasm-wasi` + `@vscode/wasm-wasi-lsp` (requires `ms-vscode.wasm-wasi-core`)
