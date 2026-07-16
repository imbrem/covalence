# Covalence

An experimental LCF-style theorem prover and VCS using WASM components.
Metatheory is the default mode; the kernel extends itself by proof
rather than by trust.

Recommended reading path:
[`notes/vibes/vision/VISION.md`](./notes/vibes/vision/VISION.md) (10-minute overview) →
[`notes/vibes/kernel/kernel-design.md`](./notes/vibes/kernel/kernel-design.md) (the kernel TCB) →
[`notes/vibes/kernel/type-hierarchy.md`](./notes/vibes/kernel/type-hierarchy.md) (type catalogue) →
[`notes/vibes/vision/roadmap.md`](./notes/vibes/vision/roadmap.md) (what's next) →
[`CLAUDE.md`](./CLAUDE.md) (build commands & crate map).

## Repository Layout

- `crates/` — Rust workspace with CLI/server/editor surfaces, kernel and prover
  experiments, substrate crates, and wrapper crates
- `apps/covalence-web/` — SvelteKit browser UI
- `packages/` — shared TypeScript packages
- `extensions/covalence-vscode/` — VS Code extension
- `docs/` — true, synced documentation (incl. the generated dep graph / TCB closure)
- `notes/` — plans (`notes/plans/`) and design notes; `notes/vibes/` is the
  AI-generated corpus (see `notes/README.md` for the tiers + authorship policy)
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
