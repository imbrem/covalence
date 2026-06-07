# Covalence

An experimental LCF-style theorem prover and VCS using WASM components.
Metatheory is the default mode; the kernel extends itself by proof
rather than by trust.

**Read first:** [`docs/README.md`](./docs/README.md) for the docs map.

Recommended path:
[`docs/c4.md`](./docs/c4.md) (repo architecture map) →
[`docs/where-we-are.md`](./docs/where-we-are.md) (current status) →
[`docs/VISION.md`](./docs/VISION.md) (10-minute overview) →
[`ARCHITECTURE.md`](./ARCHITECTURE.md) (canonical philosophy) →
[`AGENTS.md`](./AGENTS.md) (implementation invariants).

For a current-code-oriented conceptual walkthrough of `covalence-pure`,
`covalence-hol`, and their Hehner / institution-theory interpretation, see
[`gentle-intro/README.md`](./gentle-intro/README.md).

## Repository Layout

- `crates/` — Rust workspace with CLI/server/editor surfaces, kernel and prover
  experiments, substrate crates, and wrapper crates
- `apps/covalence-web/` — SvelteKit browser UI
- `packages/` — shared TypeScript packages
- `extensions/covalence-vscode/` — VS Code extension
- `gentle-intro/` — beginner-oriented conceptual notes grounded in the current code
- `docs/` — current-state docs, proposal docs, and planning/history
- `assets/`, `tests/`, `test-workbench/` — fixtures, samples, and test scaffolding

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
