# Covalence

An experimental LCF-style theorem prover and VCS using WASM components.

## Structure

```
crates/
  covalence/           CLI binary (cov)
  covalence-hash/      BLAKE3 content hashing (O256)
  covalence-store/     Content-addressed blob store
  covalence-kernel/    Execution kernel (store + WASM engine)
  covalence-wasm/      WASM component loading, linking, proposition deciding
  covalence-repl/      S-expression REPL
  covalence-serve/     HTTP/WebSocket server (axum)
  covalence-client/    Remote kernel client
  covalence-lsp/       Language server
  covalence-sexp/      S-expression parser
  covalence-git/       Cogit VCS library
  covalence-proto/     Service discovery
  covalence-sqlite/    SQLite utilities
apps/
  covalence-web/       SvelteKit web app
extensions/
  covalence-vscode/    VSCode extension (desktop + web)
```

## Prerequisites

- [Rust stable ≥1.94.1](https://rustup.rs/) with `wasm32-wasip1-threads` and `wasm32-unknown-unknown` targets
- [Bun](https://bun.sh/)
- wasm-pack, wasm-bindgen-cli, binaryen (wasm-opt)

## Quick Start

```sh
bun install            # install JS dependencies
bun run build          # full build: native (debug) + WASM + esbuild
cargo test             # run Rust tests
cov repl               # interactive S-expression REPL
cov serve --open       # start server, open browser
```
