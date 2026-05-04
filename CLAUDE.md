# Covalence

Theorem prover with Ion language tooling. Monorepo with Rust crates, a VSCode browser extension, and a SvelteKit web app.

## Build & Run

```sh
bun install                # install JS dependencies
bun run build              # full build: native (debug) + WASM + esbuild
bun run build:native       # native debug only (cargo build)
bun run build:wasm         # WASM + esbuild only
bun run build:web          # build SvelteKit web app (adapter-static)
bun run build:serve        # build web app + native binary
bun run dev:web            # SvelteKit dev server (proxies /api to localhost:3100)
bun run release            # full release build: native (release) + WASM + esbuild
bun run release:native     # native release only (cargo build --release)
bun run code:browser       # build WASM + launch web VSCode (always WASM)
bun run code:desktop       # full build + launch desktop VSCode (native if available, else WASM)
cargo check                # check Rust crates
cargo test                 # run Rust tests
```

### Running the web server

```sh
bun run build:serve        # builds web app + native binary with serve
cov serve --open           # start server on :3100, open browser
cov serve --port 8080      # custom port
```

For frontend dev with hot reload, run `cov serve` and `bun run dev:web` in parallel — the Vite dev server proxies `/api` requests to `localhost:3100`.

## Prerequisites

- **Rust stable ≥1.94.1** — `wasm32-wasip1-threads` thread support works on stable since 1.94.1 (nightly also works)
- **Rust targets**: `wasm32-wasip1-threads`, `wasm32-unknown-unknown`
- **Bun** — JS package manager and build script runner
- **wasm-pack**, **wasm-bindgen-cli**, **binaryen** (`wasm-opt`)

## Repo Layout

- `crates/covalence/` — Main binary crate (`cov` CLI)
  - `src/main.rs` — Entry point with clap derive; dispatches to `cov lsp`, `cov cog`, `cov serve`
  - `src/lib.rs` — Shared constants (`VERSION`, `TARGET`)
  - `build.rs` — Sets `COV_TARGET` env var from the Cargo build target triple
- `crates/covalence-ion/` — Ion parsing library
- `crates/covalence-lsp/` — Language server library (used by `cov lsp`)
  - `src/lib.rs` — LSP handlers, `LspConfig`, `run_lsp()`, `run_diagnose()`, `server_capabilities`
- `crates/covalence-git/` — Cogit VCS library (used by `cov cog`)
- `crates/covalence-serve/` — Web server library (used by `cov serve`)
  - `src/lib.rs` — `ServeConfig`, `run_serve()` — axum server with embedded static files
  - `src/api.rs` — REST API handlers (`GET /api/info`)
  - `src/static_files.rs` — rust-embed static file serving with SPA fallback
  - `build.rs` — Warns if `apps/covalence-web/build/` is missing
- `apps/covalence-web/` — SvelteKit web app (adapter-static, SPA mode)
  - `src/lib/api.ts` — API client; base URL configurable via `VITE_COV_API_BASE` env var
  - `src/routes/+page.svelte` — Landing page (fetches `/api/info`)
  - `build/` — Static output embedded into the Rust binary (gitignored)
- `packages/covalence-ui/` — Shared Svelte 5 component library (scaffold, for future use)
- `extensions/covalence-vscode/` — VSCode extension (desktop + web)
  - `src/extension.ts` — Extension activation, commands, binary Ion FSP
  - `src/server.ts` — LSP server creation: detects native `cov` binary, falls back to WASM
  - `scripts/build.ts` — Build script (cargo rustc → esbuild → copy wasm)
  - `dist/` — Final bundles (gitignored)

## Architecture

### CLI (`cov`)

Uses clap derive for arg parsing, `color-eyre` for error reporting (native only), and `tracing` + `tracing-subscriber` for logging (default level: `info`, override with `RUST_LOG`).

Features (all default, all compile on WASM except `serve` deps are target-gated):
- `lsp` — `cov lsp` subcommand
- `cogit` — `cov cog` subcommand
- `serve` — `cov serve` subcommand (prints error on WASM; axum/tokio deps are `cfg(not(wasm))`)

### Web server (`cov serve`)

```
cov serve [--port PORT] [--open]
  → axum HTTP server on 127.0.0.1:PORT
  → serves embedded SvelteKit static files (rust-embed)
  → REST API: GET /api/info → { version, cog_version, target, cwd }
  → SPA fallback: unmatched routes serve index.html
```

The SvelteKit app uses `adapter-static` (pure SPA, `ssr = false`) so it compiles to plain HTML/JS/CSS that gets embedded into the Rust binary at compile time.

The frontend API base URL is configurable via `VITE_COV_API_BASE` (defaults to empty = same-origin). To host the static site separately (e.g. GitHub Pages) pointing at a remote backend:
```sh
VITE_COV_API_BASE=https://cov.example.com bun run build:web
```

### VSCode extension

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
- CLI: clap 4 (derive), color-eyre + eyre (native error handling), tracing (logging)
- Web server: axum 0.8, tower-http (cors, trace), rust-embed (static files)
- Frontend: SvelteKit + adapter-static (SPA), Svelte 5, Vite 6
- TypeScript: strict mode, ES2022 target, bundler module resolution
- Build tool: esbuild (CJS bundles for both desktop and web, with browser alias for web)
- Package manager: Bun (workspace root), with `"workspaces": ["extensions/*", "apps/*", "packages/*"]`
- WASM target: `wasm32-wasip1-threads` via `cargo rustc`
- LSP framework: `lsp-server` 0.7 + `lsp-types` 0.97 (rust-analyzer ecosystem)
- Extension runtime: `@vscode/wasm-wasi` + `@vscode/wasm-wasi-lsp` (requires `ms-vscode.wasm-wasi-core`)
