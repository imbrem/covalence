# Covalence

A theorem prover with language tooling for Ion.

## Structure

```
crates/
  covalence-ion/     Ion parsing library
  covalence-lsp/     Language server (compiles to native + WASM)
extensions/
  covalence-vscode/  VSCode extension (desktop + web)
```

## Prerequisites

- [Rust nightly](https://rustup.rs/) with `wasm32-wasip1-threads` target
- [Bun](https://bun.sh/)

> **Why nightly?** The LSP uses `lsp-server::Connection::stdio()` which spawns threads. Stable Rust hardcodes `UNSUPPORTED_PLATFORM` for WASI thread spawning; nightly ≥1.96.0 removes this guard.

## Setup

```sh
bun install
```

## Commands

From the repo root:

| Command | Description |
|---------|-------------|
| `bun run build` | Build WASM + bundle extension |
| `bun run build:wasm` | Build WASM module only |
| `bun run dev` | Start dev server on localhost:3000 |
| `cargo check` | Type-check the Rust workspace |
| `cargo test` | Run Rust tests |

## Development

### Building

```sh
bun run build
```

This compiles `covalence-lsp` to WASM (`wasm32-wasip1-threads`), bundles the extension with esbuild (desktop + web), and copies the `.wasm` binary to `dist/`.

### Debugging

**F5 in VSCode** — Use the "Run Extension (Web)" launch config. It builds automatically via the pre-launch task.

**CLI** — `bun run dev` starts a server on `http://localhost:3000`. Open it in your browser.

To verify the LSP works, open the command palette and run "Covalence: Hello World". Check the Output panel > "Covalence LSP" for logs.

### Architecture

The Rust LSP runs as a WASI process inside the extension:

```
VSCode ← LanguageClient ← @vscode/wasm-wasi-lsp ← WASI Process (Rust WASM) ← lsp-server
```

- **extension.ts** — Loads WASM, creates WASI process, wraps it in a `LanguageClient`
- **main.rs** — LSP binary using `lsp-server::Connection::stdio()`
- **lib.rs** — Shared request/notification handlers
