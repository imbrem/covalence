# Where We Are

This is the current implementation snapshot for the repository as it exists in
the tree now. It is intentionally code-first: it describes what is present,
what is wired together, and where the repo still has parallel tracks or obvious
transition seams.

It does not try to settle the long-term architecture. For that, read
[`../ARCHITECTURE.md`](../ARCHITECTURE.md) and
[`design/README.md`](./design/README.md).

## TL;DR

The repo is no longer just a kernel experiment plus a few shells around it.
Today it is a broad monorepo with:

- a working CLI, HTTP server, REPL, LSP, browser UI, VS Code extension,
  Python bindings, and TypeScript clients,
- a content-addressed storage stack (`covalence-store`, `covalence-object`,
  `covalence-git`, `covalence-kv`, `covalence-fuse`, `covalence-wasm-store`),
- multiple coexisting logic / prover lines (`covalence-kernel`,
  `covalence-pure`, `covalence-hol`),
- bridge and certificate crates for OpenTheory, Alethe/SMT, SAT, egglog,
  Metamath, Lean export data, and SpecTec/WASM assets,
- a thin `covalence-shell::Kernel` used by the REPL and server as a store-first
  backend, plus a separate `Prover` trait used by theorem-oriented frontends.

The important current fact is coexistence: the repo already contains more than
one “core”, and different surfaces target different layers of that stack.

One easy point of confusion: `covalence-pure` was not purged. The thing that
was removed was the legacy `HolPrim` adapter path in `covalence-shell`. The
Pure crates are still present and active.

## User-Facing Surfaces

### CLI

The `cov` binary in [`../crates/covalence`](../crates/covalence) currently
exposes:

- `cov repl`
- `cov serve`
- `cov cog`
- `cov hol check`
- `cov lsp`

Feature-gating still exists, but the default native build enables the main
surfaces. `cov serve` and `cov repl` are native-only; the binary prints a clear
error on WASM targets.

### HTTP Server

[`../crates/covalence-serve`](../crates/covalence-serve) is an axum server with:

- `/api/info` and `/api/health`
- `/api/repl` WebSocket REPL
- blob endpoints under `/api/blobs`
- tagged-object endpoints under `/api/tagged`
- git/object-store endpoints under `/api/objects`
- `/api/eval` for stateless S-expression evaluation

The server listens on TCP and a Unix domain socket, and registers itself with
[`../crates/covalence-proto`](../crates/covalence-proto)'s discovery layer.

### Browser UI

[`../apps/covalence-web`](../apps/covalence-web) is a SvelteKit SPA that
currently includes:

- a REPL page backed by the WebSocket API,
- an object viewer for blobs and trees,
- a `cov:graph` viewer page.

It consumes the TypeScript packages in `packages/` rather than talking to the
Rust server directly.

### VS Code Extension

[`../extensions/covalence-vscode`](../extensions/covalence-vscode) provides:

- language support for `.smt`, `.smt2`, `.alethe`, `.cov`, and `.wat`,
- native-binary LSP when a `cov` path is configured,
- browser/WASM fallback via `@vscode/wasm-wasi` and
  `@vscode/wasm-wasi-lsp`.

### Python And TypeScript Libraries

- [`../crates/covalence-python`](../crates/covalence-python) exposes Python
  bindings for storage, graphs, signing, server/client helpers, WASM, and the
  Pure kernel family.
- [`../packages/covalence-client`](../packages/covalence-client) is a TS client
  for `cov serve`.
- [`../packages/covalence-ui`](../packages/covalence-ui) contains reusable
  Svelte viewers and the `cov:graph` UI.
- [`../packages/covalence-wasm-js`](../packages/covalence-wasm-js) is a JS host
  runtime for the `cov:wasm/runtime@0.1.0` direction, using native
  `WebAssembly.*` for modules and `jco` for components.

## The Current Runtime Split

Three layers matter operationally today.

### 1. Store And Object Substrate

These crates are concrete and broadly reusable now:

| Area | Crates | What they do now |
|---|---|---|
| Hashing and identities | `covalence-hash`, `covalence-types`, `covalence-rand`, `covalence-sig` | Content hashes, shared numeric/bit types, RNG, signatures |
| Parsing and syntax | `covalence-parse`, `covalence-sexp`, `covalence-json`, `covalence-grammar`, `covalence-forsp` | Parsers, S-expression dialects, Forsp evaluation |
| Blob / object storage | `covalence-store`, `covalence-sqlite`, `covalence-object`, `covalence-kv`, `covalence-git`, `covalence-fuse`, `covalence-wasm-store` | Content stores, git-compatible objects, directories/tables, KV backends, Linux FUSE mounting, WASM-packaged store helpers |
| WASM and format support | `covalence-wasm`, `covalence-wasm-spec`, `covalence-wasm-build-guest`, `covalence-graph`, `covalence-arrow`, `covalence-parquet`, `covalence-spectec` | WAT/WASM compile/parse/build, reference WASM components, graph bytes, Arrow/Parquet inspection, SpecTec ingestion |

This is the most concrete and consistently implemented part of the repo.

### 2. Shell / Service Layer

[`../crates/covalence-shell`](../crates/covalence-shell) is now the main seam
between storage-oriented surfaces and theorem-oriented surfaces.

It contains:

- `SyncBackend` / `AsyncBackend`
- a store-first in-memory `Kernel`
- the `Prover` trait used by theorem/proof importers

That split is important:

- the `Kernel` in `covalence-shell` is currently a thin backend around a blob
  store plus tree tracking,
- the theorem-prover abstraction lives beside it, not inside it.
- an older shell-side `HolPrim` adapter was removed, which is separate from
  the continued existence of `covalence-pure` and `covalence-hol`.

### 3. Logic / Prover Lines

The repo currently contains several parallel logic-related implementations:

| Crate | Current role |
|---|---|
| `covalence-kernel` | Arena/egraph/UF theorem kernel and the main backend for the current `Prover` implementations |
| `covalence-pure` | Small Pure-style logical framework with its own tests and shell crate |
| `covalence-pure-shell` | Hashing / S-expression shell around `covalence-pure` |
| `covalence-hol` | HOL Light-style kernel used directly by OpenTheory checking/import |

This is not just “old versus new”. These lines are all live in code and have
real consumers today.

If you were expecting `covalence-pure` to be gone, the likely source of that
impression is the `covalence-shell` cleanup that removed the old `HolPrim`
adapter once OpenTheory consumers moved to `PureHol` directly.

## Proof, Import, And Solver Crates

These crates form the current “logic zoo” around the kernels:

| Family | Crates | Current role |
|---|---|---|
| HOL / package transport | `covalence-opentheory` | Read and interpret OpenTheory articles against `covalence-hol` |
| SMT and proof ingest | `covalence-smt`, `covalence-alethe` | SMT-LIB terms/problems plus Alethe bridge/checking |
| SAT and certificates | `covalence-sat` | DIMACS, DRAT, LRAT, solver traits, proof parsing |
| Equality saturation | `covalence-egglog` | egglog AST/parse/lowering/bridge/proof ingestion |
| Other proof ecosystems | `covalence-metamath`, `covalence-lean` | Metamath verification and Lean export ingestion |
| Misc. theorem-adjacent | `covalence-llm` | OpenAI-backed WIT-facing LLM backend experiments |

The stable story here is not “one proof pipeline”; it is “many bridges into
shared backend traits and kernel-adjacent representations”.

## What The Main Surfaces Actually Target

Today the user-facing surfaces split into two broad camps.

### Store-first surfaces

These primarily use the `covalence-shell::Kernel` backend and the object/store
stack:

- `cov repl`
- `cov serve`
- `packages/covalence-client`
- `apps/covalence-web`
- parts of `covalence-python`
- `cov cog`

### Theorem/proof-first surfaces

These primarily care about prover traits or specific logic kernels:

- `cov hol check`
- `covalence-opentheory`
- `covalence-alethe`
- `covalence-egglog`
- `covalence-metamath`
- `covalence-lean`
- parts of `covalence-python`

That split is the clearest way to understand why several kernel lines coexist.

## Build And Test Reality

The checked-in commands currently line up like this:

### Root Bun scripts

- `bun run build` — native Rust binary plus VS Code WASM build
- `bun run build:web` — web app only
- `bun run build:serve` — web app plus native `cov` for embedded static serve
- `bun run code:browser` / `bun run code:desktop` — extension workflows
- `bun run build:python` — Python bindings via `maturin`

### Testing

- `cargo test`
- `bun run test:ui`
- `bun run test:wasm-js`
- `bun run test:python`

There is currently no single top-level JS “run everything” script.

## What Is Stable Vs Transitional

### Relatively stable

- the store/object/hash substrate
- the server, REPL, and TypeScript client surface
- the VS Code and web application scaffolding
- the existence of multiple logic/import families

### Clearly transitional

- which prover/kernel line becomes the long-term center
- how `covalence-kernel`, `covalence-pure`, and `covalence-hol` eventually
  relate
- how much of the current `Prover` surface stays identical through that change
- which proposal set from `docs/design/` becomes adopted architecture

## How To Read The Rest Of The Docs

- Use [`c4.md`](./c4.md) for the current component map.
- Use [`institution-map.md`](./institution-map.md) if your work crosses logic
  families or importers.
- Use [`design/README.md`](./design/README.md) for future-direction proposals.
- Use [`../ARCHITECTURE.md`](../ARCHITECTURE.md) and
  [`../AGENTS.md`](../AGENTS.md) as the target constraints, not as a literal
  description of every current crate boundary.
