# Covalence

Covalence is an experimental monorepo for content-addressed storage, proof and
logic tooling, WASM execution, and multiple user surfaces over that substrate.
The repository currently contains:

- a Rust CLI and local server,
- a browser UI and a VS Code extension,
- Python and TypeScript client libraries,
- several coexisting prover / logic lines (`covalence-kernel`,
  `covalence-pure`, `covalence-hol`),
- import and certificate tooling for OpenTheory, SMT/Alethe, SAT, egglog,
  Metamath, Lean exports, and SpecTec/WASM assets.

`covalence-pure` has not been removed. What was removed is an older shell-side
adapter path (`HolPrim`) in `covalence-shell`; the Pure and HOL crates remain
in the tree.

If you want the implementation map rather than the long-term philosophy, start
with [`docs/where-we-are.md`](./docs/where-we-are.md) and
[`docs/c4.md`](./docs/c4.md).

## Docs

- [`docs/README.md`](./docs/README.md) — documentation index
- [`docs/where-we-are.md`](./docs/where-we-are.md) — current codebase snapshot
- [`docs/c4.md`](./docs/c4.md) — runtime and repo architecture map
- [`docs/institution-map.md`](./docs/institution-map.md) — logic / proof-format /
  translation landscape
- [`ARCHITECTURE.md`](./ARCHITECTURE.md) — target architecture and invariants
- [`AGENTS.md`](./AGENTS.md) — implementation constraints for trusted-core work

## Repo Shape

- `crates/` — Rust workspace members
- `apps/covalence-web/` — SvelteKit browser UI
- `packages/` — TypeScript packages (`covalence-client`, `covalence-ui`,
  `covalence-wasm-js`)
- `extensions/covalence-vscode/` — VS Code extension for `.cov`, SMT-LIB,
  Alethe, and WAT
- `docs/` — current-state docs, design proposals, and historical notes
- `assets/`, `tests/`, `test-workbench/` — fixtures and integration scaffolding

## Prerequisites

- Rust stable with `wasm32-wasip1-threads` and `wasm32-unknown-unknown`
- [Bun](https://bun.sh/)
- `wasm-pack`, `wasm-bindgen-cli`, `binaryen`
- Python + `maturin` if you are building `crates/covalence-python`

## Build And Run

```sh
bun install
bun run build:serve
cargo test
cov repl
cov serve --open
```

Useful variants:

```sh
bun run build             # native cov + VS Code WASM extension assets
bun run build:web          # build the Svelte app only
bun run build:serve        # build web assets + native cov binary
bun run code:browser       # launch the VS Code web extension flow
bun run code:desktop       # launch the desktop VS Code extension flow
bun run build:python       # build/install the Python bindings with maturin
```

## Main Commands

The `cov` binary currently exposes these top-level commands:

- `cov repl` — local or remote content-store REPL
- `cov serve` — HTTP API + WebSocket REPL + optional static web UI
- `cov cog` — git/object-store tooling (`hash-blob`, `clone`, Linux `mount`)
- `cov hol check` — check OpenTheory article files against `covalence-hol`
- `cov lsp` — start the language server used by the editor tooling

## Frontend Development

For local web work:

```sh
cov serve --api
bun run dev:web
```

The Vite dev server serves the Svelte app and proxies `/api` to the local
backend. The built web app currently includes:

- a REPL page backed by the WebSocket API,
- an object viewer for blobs and trees,
- a `cov:graph` viewer page.

## Testing

There is no single top-level JS test command yet. Use the commands that match
the surface you changed:

- `cargo test`
- `bun run test:ui`
- `bun run test:wasm-js`
- `bun run test:python`

Contributions are accepted under the same dual offering. Vendored third-party
code keeps its upstream license and is documented locally where relevant.

## License

Covalence is offered to the public domain to the maximum extent legally
possible. You may use it under either:

- the [BSD Zero Clause License](./LICENSE) (`0BSD`), or
- the [CC0 1.0 Universal](./LICENSE-CC0) public-domain dedication (`CC0-1.0`).

SPDX expression: `0BSD OR CC0-1.0`.
