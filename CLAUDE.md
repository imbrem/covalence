# Covalence

Theorem prover with Ion language tooling. Monorepo with Rust crates and a VSCode browser extension.

## Build & Run

```sh
bun install                # install JS dependencies
bun run build              # full build: native (debug) + WASM + esbuild
bun run build:native       # native debug only (cargo build)
bun run build:wasm         # WASM + esbuild only
bun run release            # full release build: native (release) + WASM + esbuild
bun run release:native     # native release only (cargo build --release)
bun run code:browser       # build WASM + launch web VSCode (always WASM)
bun run code:desktop       # full build + launch desktop VSCode (native if available, else WASM)
cargo check                # check Rust crates
cargo test                 # run Rust tests
```

## Prerequisites

- **Rust stable ≥1.94.1** — `wasm32-wasip1-threads` thread support works on stable since 1.94.1 (nightly also works)
- **Rust targets**: `wasm32-wasip1-threads`, `wasm32-unknown-unknown`
- **Bun** — JS package manager and build script runner
- **wasm-pack**, **wasm-bindgen-cli**, **binaryen** (`wasm-opt`)

## Repo Layout

- `crates/covalence/` — Main binary crate (`cov` CLI)
  - `src/main.rs` — Entry point, dispatches to `cov lsp`, `cov cog`, etc.
  - `src/lib.rs` — Shared constants (`VERSION`, `TARGET`)
  - `build.rs` — Sets `COV_TARGET` env var from the Cargo build target triple
- `crates/covalence-ion/` — Ion parsing library
- `crates/covalence-lsp/` — Language server library (used by `cov lsp`)
  - `src/lib.rs` — LSP handlers, `LspConfig`, `run_lsp()`, `server_capabilities`
- `crates/covalence-git/` — Cogit VCS library (used by `cov cog`)
- `extensions/covalence-vscode/` — VSCode extension (desktop + web)
  - `src/extension.ts` — Extension activation, commands, binary Ion FSP
  - `src/server.ts` — LSP server creation: detects native `cov` binary, falls back to WASM
  - `scripts/build.ts` — Build script (cargo rustc → esbuild → copy wasm)
  - `dist/` — Final bundles (gitignored)

## Architecture

The extension supports two LSP transport modes, selected automatically by `src/server.ts`:

**Native mode** (Linux desktop, when `cov` is available):
```
VSCode ← LanguageClient ← stdio ← cov lsp (native binary)
```

**WASM mode** (browser, or native not available):
```
VSCode ← LanguageClient ← @vscode/wasm-wasi-lsp ← WASI Process (cov.wasm) ← lsp-server
```

Detection order: `covalence.server.path` setting → `cov` on PATH (Linux only) → WASM fallback.

The same `src/extension.ts` serves both desktop and web bundles. esbuild aliases `vscode-languageclient/node` → `vscode-languageclient/browser` for the web build.

The target triple is set at build time via `crates/covalence/build.rs` (`COV_TARGET` env var) and passed into `covalence_lsp::run_lsp()` via `LspConfig`. The LSP server reports it in `serverInfo.version` during the initialize handshake.

### WASM Memory

Memory is fixed at 32768 pages (2 GB). This value must match in two places:
- `scripts/build.ts`: linker args `--initial-memory=2147483648 --max-memory=2147483648`
- `src/server.ts`: `wasm.createProcess(... { initial: 32768, maximum: 32768, shared: true })`

Note: because this is shared memory (`SharedArrayBuffer`), the full 2 GB is reserved as virtual address space. On Linux, physical RAM is only committed for pages actually touched (overcommit). On Windows, the full size may count against the system commit charge.

## Pull Request Checklist

- Run `cargo fmt --all` before creating a PR to ensure consistent formatting.

## Conventions

- Rust edition 2024 (stable ≥1.94.1 or nightly), workspace resolver 2
- TypeScript: strict mode, ES2022 target, bundler module resolution
- Build tool: esbuild (CJS bundles for both desktop and web, with browser alias for web)
- Package manager: Bun (workspace root), with `"workspaces": ["extensions/*"]`
- WASM target: `wasm32-wasip1-threads` via `cargo rustc`
- LSP framework: `lsp-server` 0.7 + `lsp-types` 0.97 (rust-analyzer ecosystem)
- Extension runtime: `@vscode/wasm-wasi` + `@vscode/wasm-wasi-lsp` (requires `ms-vscode.wasm-wasi-core`)
