# Covalence

Experimental VCS and theorem prover. Monorepo with Rust crates, a VSCode browser extension, and a SvelteKit web app.

## Skeletons (STRICT)

The **SKELETONS** registry records every intentional placeholder in the repo:
empty/stub modules, removed-pending-rewrite subsystems, `NotImplemented` /
`todo!()` / `unimplemented!()` stubs, and any test that is commented out,
`#[ignore]`d, or deleted "for later".

It is **split per crate** (the root [`SKELETONS.md`](./SKELETONS.md) is just an
index of the per-crate files):

- Each crate keeps its own **`crates/<crate>/SKELETONS.md`**.
- A large crate may split *further by module*: its `crates/<crate>/SKELETONS.md`
  becomes an index, and each module's skeletons live in a co-located
  **`crates/<crate>/src/<module>/SKELETONS.md`** (e.g.
  `crates/covalence-hol/src/init/SKELETONS.md`,
  `crates/covalence-hol/src/script/SKELETONS.md`).

**Whenever you leave a skeleton — stub an operation, gut a module, disable or
delete a test "for now", or drop in a placeholder — you MUST add a matching
entry to the SKELETONS file *nearest the code* (the module's file if one exists,
else the crate's) in the same change.** When you fill a skeleton in, delete its
entry. If you add the first skeleton to a crate/module that has no file yet,
create it and link it from the parent index. Never silently leave work
unfinished; record it where it is discoverable next to the code.

**Format (keep it short — these files are loaded into context, so they cost
tokens):**

- **Only open work.** Never describe *completed* work in a SKELETONS file — when
  a skeleton is filled, delete its entry (don't rewrite it to "done"). A
  SKELETONS file is a TODO list, not a changelog.
- **Severe at the top, minor at the bottom.** Order entries by impact: blocking
  gaps / missing core functionality first; nice-to-haves and polish last. A
  `## Severe` / `## Minor` split is fine when a file has many entries.
- **One terse line or two per entry.** Name the stub and what's missing. Push
  long rationale, design context, or status history into a separate Markdown doc
  (under `notes/`) and link it; don't inline it here.

## Build & Run

```sh
bun install                # install JS dependencies
bun run build              # full build: web (SvelteKit) + native (debug) + WASM + esbuild
bun run build:native       # native debug only (cargo build) — embeds last-built web bundle
bun run build:wasm         # WASM + esbuild only
bun run build:web          # build SvelteKit web app (adapter-static)
bun run build:serve        # build web app + native binary
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

## Reference Notes

Design notes and research live in **[`notes/`](./notes/)** — start at the
categorized index **[`notes/README.md`](./notes/README.md)**. Read first:
[`notes/VISION.md`](./notes/VISION.md) (the vision),
[`notes/kernel-design.md`](./notes/kernel-design.md) (the TCB — before touching
`covalence-core`), [`notes/roadmap.md`](./notes/roadmap.md) (what's next), and
[`notes/refactor-plan.md`](./notes/refactor-plan.md) (the in-flight three-layer
reorg). `notes/sketches/` holds forward-looking sketches + research notes.

## Skills (use them, keep them current)

Domain knowledge lives in skills under `.claude/skills/` so the right context
loads for the task at hand: **crate-map** (the per-crate catalogue),
**wasm-guide**, **vscode-extension**, **web-server**, **performance**,
**metamath-performance**. Consult the relevant skill before diving in.

**Maintain them.** When you learn something durable about a subsystem — a
gotcha, a workflow, where a thing lives — update the relevant skill (or add one)
in the same change, the way you keep `SKELETONS.md` current. Keep CLAUDE.md thin:
push reusable domain knowledge into skills, not here. And actively look for ways
to work more effectively — capture repeatable procedures as skills.

## Pull Request Checklist

- Run `bun test` to execute all tests (Rust + Python). The test runner handles venv activation automatically, including in git worktrees.

## Crates

The workspace is many `covalence-*` crates, layered roughly: **wrappers** (one
per external dep) → **storage/content-addressing** → **kernel/TCB**
(`covalence-pure` → `covalence-core` → thin `covalence-hol` + `covalence-metamath`
→ `covalence-init` → `covalence-kernel`) → **proof-format frontends** →
**app/systems**.

**Dependency discipline:** all use of an external library goes through its wrapper
crate — never import the underlying dep directly.

The full per-crate catalogue (what each wraps/provides) lives in the
**crate-map** skill; the dependency graph is `notes/crate-graph.md`. Read
`notes/kernel-design.md` before touching the TCB (`covalence-core`).

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
