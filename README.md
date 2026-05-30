# Covalence

An experimental LCF-style theorem prover and VCS using WASM components.

## Structure

```
crates/
  covalence/           CLI binary (cov)
  covalence-hash/      BLAKE3 + SHA-256 + git hashing (O256)
  covalence-store/     Content-addressed blob store, tagged/object stores
  covalence-object/    Object serialization (Dir, Table, git tree format)
  covalence-kernel/    Execution kernel (store + WASM engine)
  covalence-wasm/      WASM loading, linking, ModuleBuilder, Val/ValType
  covalence-repl/      S-expression REPL
  covalence-serve/     HTTP/WebSocket server (axum)
  covalence-client/    Remote kernel client (sync + async)
  covalence-lsp/       Language server
  covalence-sexp/      S-expression parser (multi-dialect)
  covalence-smt/       SMT-LIB2 terms, theories, Alethe proofs
  covalence-sat/       SAT formulas, DIMACS, DRAT proofs
  covalence-types/     Shared types (Decision, etc.)
  covalence-parse/     Parser combinators (winnow), LEB128
  covalence-git/       Git object stores (loose, odb, LFS)
  covalence-sig/       EdDSA signatures (ed25519-dalek)
  covalence-rand/      Random number generation
  covalence-proto/     Service discovery
  covalence-sqlite/    SQLite wrapper (rusqlite)
  covalence-python/    Python bindings (PyO3)
apps/
  covalence-web/       SvelteKit web app
packages/
  covalence-client/    TypeScript client library
  covalence-ui/        Svelte UI components
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
