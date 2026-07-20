# Covalence

Experimental VCS and theorem prover. Monorepo with Rust crates, a VSCode browser extension, and a SvelteKit web app.

## Open work database (STRICT)

Every intentional placeholder—empty/stub modules, removed-pending-rewrite
subsystems, `NotImplemented` / `todo!()` / `unimplemented!()` stubs, and tests
disabled or deleted "for later"—must have a stable marker beside the responsible
code:

```rust
// TODO(cov:hol.script.source-spans, severe): Thread source spans through script errors.
// FIXME(cov:kernel.deep-check, severe): Enforce DeepCheck separately from dependency trust.
// PERF(cov:metamath.symbol-interning, major): Intern symbols for set.mm-scale imports.
```

Kinds are `TODO`, `FIXME`, `SKELETON`, and `PERF`; severity is `severe`, `major`,
or `minor`. IDs are unique lowercase dotted/dashed names and remain stable when
code moves. Use `FIXME` for incorrect, unsound, or adversarial-input-sensitive
behavior; `PERF` for measured inefficiency; `SKELETON` for an intentionally empty
implementation; otherwise use `TODO`.

Run `bun run todos` to rebuild the deterministic
`docs/todos/todos.json` index and cached `target/covalence-todos.sqlite`
database. Query with `bun run todos -- --list` and optional `--crate`,
`--severity`, `--kind`, or `--search` filters. Compare the worktree with a
commit using `bun run todos -- --diff <commit>`. CI runs
`bun run todos:check`.

Only open work belongs in markers. Delete a marker when its acceptance condition
is satisfied; never turn it into a changelog. Keep the marker terse, and put
design rationale/status history in `notes/vibes/` with a link where useful.

The portfolio-level current-state report, workstream ownership boundaries, and
dependency DAG live in
[`notes/vibes/plans/current-program.md`](./notes/vibes/plans/current-program.md).
The concise agent entry point is [`AGENTS.md`](./AGENTS.md).

## Build & Run

All `bun run build:*` / `serve` / `release` commands route through the build-graph
orchestrator ([`scripts/build.mjs`](./scripts/build.mjs)), which models the
cross-toolchain artifact DAG — **web-kernel WASM → web bundle → rust-embed'd
`cov` binary** — and builds a target's prerequisites first, skipping work that is
already up to date. So building the server automatically (re)builds its WASM
prerequisites; you never hand-order them. cargo stays the source of truth for
Rust staleness. Run `bun run build:graph` to print the DAG. Missing tools fail
with an install hint.

```sh
bun install                # install JS dependencies
bun run build              # full build: native (debug, pulls web ⇒ web-kernel) + VSCode WASM
bun run build:native       # native cov (auto-builds web bundle + web-kernel WASM first)
bun run build:wasm         # VSCode extension WASM + esbuild
bun run build:web          # SvelteKit web app (auto-builds web-kernel WASM first)
bun run build:web-kernel   # web-kernel WASM only (cargo → wasm-bindgen → wasm-opt)
bun run build:graph        # print the build dependency graph
bun run build:serve        # native cov with a fresh embedded web bundle
bun run dev:web            # SvelteKit dev server (proxies /api to localhost:3100)
bun run dev:serve          # reminder + dev:web (run cov serve --api in another terminal)
bun run release            # full release build: web + native (release) + WASM + esbuild
bun run release:native     # native release only (cargo build --release) — embeds last-built web bundle
bun run code:browser       # build WASM + launch web VSCode (always WASM)
bun run code:desktop       # full build + launch desktop VSCode (native if available, else WASM)
cargo check                # check Rust crates
cargo test                 # run Rust tests
bun run fmt                # cargo fmt --all (also runs on commit via .githooks/pre-commit)
bun run fmt:check          # cargo fmt --all --check (the CI fmt gate)
bun run deps               # regenerate docs/deps/ dep graph + TCB closure (runs on commit)
bun run deps:check         # fail if docs/deps/ is stale (the CI deps gate)
bun run todos              # regenerate/query the source-local open-work database
bun run todos:check        # fail if the checked-in TODO index is stale
bun test                   # run all tests (Rust + Python)
bun run test:python        # run Python tests only
bun run build:python       # build Python extension (maturin develop)
```

### Running the web server

```sh
bun run build:serve        # builds web app + native binary with serve
cov serve --open           # start server on :3100, open browser
cov serve --port 8080      # custom port
cov serve --api            # API only, no static frontend
cov serve --store          # SQLite persistence (XDG default path)
cov serve --store path.db  # SQLite at explicit path
```

For frontend dev with hot reload, run `cov serve --api` and `bun run dev:web` in parallel — the Vite dev server proxies `/api` requests to `localhost:3100`. Override the proxy target with `COV_API`:

```sh
COV_API=http://localhost:8080 bun run dev:web   # custom port
COV_API=https://cov.example.com bun run dev:web # remote backend
```

## Prerequisites

- **Rust stable ≥1.94.1** — `wasm32-wasip1-threads` thread support works on stable since 1.94.1 (nightly also works)
- **Rust targets**: `wasm32-wasip1-threads`, `wasm32-unknown-unknown`
- **Bun** — JS package manager and build script runner
- **wasm-pack**, **wasm-bindgen-cli**, **binaryen** (`wasm-opt`)

The [`flake.nix`](./flake.nix) devshell (`nix develop`, or direnv via `.envrc`)
provides all of the above plus `sccache`, `buck2`, `reindeer`, and the Python
toolchain. It shares a Rust build cache across git worktrees (sccache; toggle
with `COV_CACHE=off` for local incremental). An optional, reproducible dev
container built on the same flake lives in [`.devcontainer/`](./.devcontainer/README.md).

## Docs, Notes & Authorship (IMPORTANT)

Documentation is split by **trust and authorship**:

- **[`docs/`](./docs/README.md)** — *true* documentation only (what the codebase
  actually is, aggressively synced). Machine-generated artifacts live here
  (`docs/deps/` — the dep graph + TCB closure, `bun run deps`).
- **[`notes/`](./notes/README.md)** — the map. `notes/plans/` holds active plans
  ([`notes/plans/next-stage.md`](./notes/plans/next-stage.md) is the current
  one); structured topic notes (`ideas/`, `experiments/`, …) are *aspirational*.
- **[`notes/vibes/`](./notes/vibes/README.md)** — the AI-generated design corpus
  (index in its README). Read first: `vision/VISION.md` (the vision),
  `kernel-design.md` (the TCB — before touching `covalence-core`),
  `vision/neel-meeting-synthesis.md`, `kernel/substrate-rewrite.md` (the current
  rewrite direction).
  Sketches in `sketches/`.

**Authorship policy (current):** everything outside `notes/vibes/` — all of
`docs/` and the non-vibes `notes/` tiers — is **maintainer-authored, not
AI-generated** (until the vision is fully written out by hand). Agents: write
design notes/analysis into `notes/vibes/`; do not author or substantially
rewrite `docs/` or non-vibes `notes/` prose — flag gaps instead.
(Machine-generated artifacts like `docs/deps/` are exempt.)

## Skills (use them, keep them current)

Domain knowledge lives in skills under `.claude/skills/` so the right context
loads for the task at hand: **crate-map** (the per-crate catalogue),
**wasm-guide**, **vscode-extension**, **web-server**, **performance**,
**metamath-performance**. Consult the relevant skill before diving in.

**Maintain them.** When you learn something durable about a subsystem — a
gotcha, a workflow, where a thing lives — update the relevant skill (or add one)
in the same change, the way you keep source-local open-work markers current. Keep CLAUDE.md thin:
push reusable domain knowledge into skills, not here. And actively look for ways
to work more effectively — capture repeatable procedures as skills.

## Pull Request Checklist

- Run `bun test` to execute all tests (Rust + Python). The test runner handles venv activation automatically, including in git worktrees.

## Crates

`crates/` is hierarchical — `app/ ffi/ kernel/ lang/ lib/ proof/ server/ store/
vcs/` — but package names keep their `covalence-*` prefixes (e.g.
`covalence-pure` = `crates/kernel/base`, `covalence-core` =
`crates/kernel/hol/core`, the `cov` CLI = `crates/app/cov`). Layered roughly:
**wrappers** (one per external dep, mostly `crates/lib/`) →
**storage/content-addressing** (`crates/store/`, `crates/vcs/`) → **kernel/TCB**
(`covalence-pure(-trusted)` `crates/kernel/base` → `covalence-core`
`crates/kernel/hol/core` → thin `covalence-hol` `crates/kernel/hol/traits` +
`covalence-metamath` `crates/proof/metamath` → `covalence-init`
`crates/kernel/hol/init` → `covalence-kernel` `crates/kernel/core`) →
**proof-format frontends** (`crates/proof/`) → **app/systems** (`crates/app/`,
`crates/server/`, `crates/ffi/`).

The directory names describe responsibility, not a universal dependency
direction: `kernel/` contains low-level, stable capability APIs suitable for a
WIT boundary, while `lang/` contains high-level concrete language frontends
such as Scheme. Dependencies may cross between those trees in either direction
when the abstraction calls for it, but the Cargo package graph must remain
acyclic. If two packages need each other, extract the shared interface or IR
into a smaller package rather than coupling frontend policy into a kernel API.

**Dependency discipline:** all use of an external library goes through its wrapper
crate — never import the underlying dep directly.

The full per-crate catalogue (what each wraps/provides) lives in the
**crate-map** skill; the machine-tracked dependency graph + TCB closure is
`docs/deps/` (`bun run deps`). Read `notes/vibes/kernel/kernel-design.md` before
touching the TCB (`crates/kernel/base/trusted` + `crates/kernel/hol/core`).

## Conventions

- Rust edition 2024 (stable ≥1.94.1 or nightly), workspace resolver 2
- CLI: clap 4 (derive), color-eyre + eyre (native error handling), tracing (logging)
- Error types: `thiserror` for library crates, `eyre` at the binary boundary
- Web server: axum 0.8, tower-http (cors, trace), rust-embed (static files)
- Frontend: SvelteKit + adapter-static (SPA), Svelte 5, Vite 6
- TypeScript: strict mode, ES2022 target, bundler module resolution
- Build tool: esbuild (CJS bundles for both desktop and web, with browser alias for web)
- Package manager: Bun (workspace root), with `"workspaces": ["extensions/*", "apps/*", "packages/*"]`
- WASM target: `wasm32-wasip1-threads` via `cargo rustc`
- LSP framework: `lsp-server` 0.7 + `lsp-types` 0.97 (rust-analyzer ecosystem)
- Extension runtime: `@vscode/wasm-wasi` + `@vscode/wasm-wasi-lsp` (requires `ms-vscode.wasm-wasi-core`)
