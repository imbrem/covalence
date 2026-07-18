# Covalence

An experimental LCF-style theorem prover and VCS using WASM components.
Metatheory is the default mode; the kernel extends itself by proof
rather than by trust.

Recommended reading path:
[`notes/vibes/vision/VISION.md`](./notes/vibes/vision/VISION.md) (10-minute overview) →
[`notes/vibes/kernel/kernel-design.md`](./notes/vibes/kernel/kernel-design.md) (the kernel TCB) →
[`notes/vibes/kernel/type-hierarchy.md`](./notes/vibes/kernel/type-hierarchy.md) (type catalogue) →
[`notes/vibes/vision/roadmap.md`](./notes/vibes/vision/roadmap.md) (what's next) →
[`notes/vibes/plans/workstreams-and-state-report.md`](./notes/vibes/plans/workstreams-and-state-report.md) (current state + parallel workstreams) →
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

## Finding Work

Open work is recorded beside the code with stable `TODO(cov:...)`,
`FIXME(cov:...)`, `SKELETON(cov:...)`, and `PERF(cov:...)` markers. The global
index is generated rather than maintained by hand:

```sh
bun run todos
bun run todos -- --list --severity severe
bun run todos -- --list --crate covalence-metamath
bun run todos -- --list --search "source spans"
bun run todos:check
```

The deterministic index is [`docs/todos/todos.json`](./docs/todos/todos.json);
the queryable cache is `target/covalence-todos.sqlite`. See the
[workstream plan](./notes/vibes/plans/workstreams-and-state-report.md) for the
current-state report, biggest holes, dependency DAG, and parallel execution
lanes.

## Prerequisites

- [Rust stable ≥1.94.1](https://rustup.rs/) with `wasm32-wasip1-threads` and `wasm32-unknown-unknown` targets
- [Bun](https://bun.sh/)
- wasm-pack, wasm-bindgen-cli, binaryen (wasm-opt)

## Quick Start

```sh
bun install            # install JS dependencies
bun run build          # full build: native (debug) + WASM + esbuild
cargo test             # run Rust tests
bun run todos          # regenerate the open-work index and SQLite database
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
