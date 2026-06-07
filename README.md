# Covalence

An experimental LCF-style theorem prover and VCS using WASM components.
Metatheory is the default mode; the kernel extends itself by proof
rather than by trust.

**Read first:** [`docs/VISION.md`](./docs/VISION.md) (10-min overview)
→ [`ARCHITECTURE.md`](./ARCHITECTURE.md) (full vision) →
[`AGENTS.md`](./AGENTS.md) (operational invariants).

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

## License

Covalence is offered to the public domain to the maximum extent legally
possible. You may use it under either:

- the [BSD Zero Clause License](./LICENSE) (`0BSD`), or
- the [CC0 1.0 Universal](./LICENSE-CC0) public-domain dedication (`CC0-1.0`).

SPDX expression: `0BSD OR CC0-1.0`.

Contributions are accepted under the same dual offering — see
[`CONTRIBUTING.md`](./CONTRIBUTING.md). Vendored third-party code keeps
its upstream license and is documented locally (e.g.
[`assets/spectec/README.md`](./assets/spectec/README.md)).
