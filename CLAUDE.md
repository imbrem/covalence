# Covalence

Experimental VCS and theorem prover. Monorepo with Rust crates, a VSCode browser extension, and a SvelteKit web app.

## Build & Run

```sh
bun install                # install JS dependencies
bun run build              # full build: native (debug) + WASM + esbuild
bun run build:native       # native debug only (cargo build)
bun run build:wasm         # WASM + esbuild only
bun run build:web          # build SvelteKit web app (adapter-static)
bun run build:serve        # build web app + native binary
bun run dev:web            # SvelteKit dev server (proxies /api to localhost:3100)
bun run dev:serve          # reminder + dev:web (run cov serve --api in another terminal)
bun run release            # full release build: native (release) + WASM + esbuild
bun run release:native     # native release only (cargo build --release)
bun run code:browser       # build WASM + launch web VSCode (always WASM)
bun run code:desktop       # full build + launch desktop VSCode (native if available, else WASM)
cargo check                # check Rust crates
cargo test                 # run Rust tests
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

## Reference Docs

Two design docs at the repo root drive everything above the build system:

- **[`ARCHITECTURE.md`](./ARCHITECTURE.md)** — canonical design and philosophy. The mirror principle, the three planes (logic / execution / content / format), the disjunct trick, the profunctor model, base-shift. Read this first if you're touching the kernel or the store.
- **[`AGENTS.md`](./AGENTS.md)** — the operational distillation: TCB boundary, kernel primitive list, "looks like a bug but is intended" guarantees, grep-target invariants, suggested build order. Read fully before writing kernel code.

Subsystem skills (auto-loaded when relevant):
- **architecture** — Repo layout, dependency graph, key rules, CLI features, REPL commands
- **wasm-guide** — covalence-wasm features, proposition deciding, WASM memory config
- **vscode-extension** — VSCode extension transport modes, LSP details
- **web-server** — Web server architecture, SvelteKit frontend, static embedding

## Pull Request Checklist

- Run `bun test` to execute all tests (Rust + Python). The test runner handles venv activation automatically, including in git worktrees.

## Wrapper Crates

Several `covalence-*` crates exist to wrap external dependencies. All usage of the underlying library should go through the wrapper crate, never import the dependency directly:

- **covalence-wasm** — wraps `wat`, `wasmparser`, `wasmprinter`, `wasm-encoder`, and optionally `wasmtime` (behind the `runtime` feature). Re-exports `wasmtime` via `covalence_wasm::engine::wasmtime`. Provides `ModuleBuilder` for programmatic WASM construction and `Val`/`ValType` component model types.
- **covalence-hash** — wraps `blake3`, `sha2`, and optionally `gix-hash` (default `git` feature). Provides the `O256` content-addressed hash type, `HashCtx` trait with multiple hashing contexts (BLAKE3, SHA-256, git), `ContentHash`/`ContentId` traits, and `CovRoot` for domain-separated hashing.
- **covalence-sqlite** — wraps `rusqlite`. Provides `open()` and `open_memory()` helpers with recommended SQLite pragmas (WAL mode, NORMAL sync, busy timeout).
- **covalence-git** — git-compatible object storage and hashing. Provides `hash_blob` utility, loose/odb object store backends, and Git LFS support. Depends on `covalence-hash` for hashing.
- **covalence-rand** — wraps `rand` (latest). All randomness usage should go through this crate.
- **covalence-sig** — wraps `ed25519-dalek` for EdDSA signatures. Also re-exports a pinned `rand_core` 0.6 as `dalek_rand_core` (exception to the `covalence-rand` rule, required for `ed25519-dalek` compatibility).
- **covalence-parse** — wraps `winnow` for parser combinators. Provides `leb128` module for unsigned LEB128 (varint) encoding/decoding.
- **covalence-sexp** — S-expression parser with event-based architecture and dialect support. Parametric `SExp<A>` type generic over atom type; default `SExpr = SExp<Atom>` where `Atom` is `Symbol(SmolStr)` or `Str { format: SmolStr, bytes: Bytes }`. Three layers: `SExpVisitor` (SAX-style events + dialect config), `SExpBuilder`/`TreeBuilder` (bottom-up tree construction), and `SExp` (concrete type). Unified string body parser: all strings produce `(format, bytes)` — bare `"..."` has format="" and any atom before `"` becomes a format prefix (e.g. `b"..."` → format="b", `json"..."` → format="json"). Quoted symbols `|...|` fold into `Atom::Symbol`. Three dialects: `CovalenceDialect` (default — `;;` line comments, `(; ;)` block comments, `|...|` quoted symbols), `SmtLibDialect` (`;` line comments, `|...|`), `WatDialect` (`;;`/`(; ;)` comments, no `|...|`). API: `parse()` (Covalence), `parse_smt()` (SMT-LIB), `parse_wat()` (WAT), `parse_with()` (generic). `SExp::map()`/`map_ref()` for atom type transformation.
- **covalence-types** — shared types used across the ecosystem. Provides `Decision` (three-valued sat/unknown/unsat), `Bits` (bit string of arbitrary length, packed-byte representation), and, behind the default `int` feature, `Nat`/`Int` arbitrary-precision integers (wrapping `num-bigint`, `num-traits`, `num-integer`), plus `Sign`, `NatConvertError`, `ParseError`. Subtraction on `Nat` saturates to zero; use `checked_sub` for the fallible path.
- **covalence-sat** — SAT formulas, DIMACS, DRAT proofs, solver traits. Depends on `covalence-types`, `covalence-parse`. Optional `wasm` feature adds `covalence-wasm`.
- **covalence-smt** — SMT-LIB2 terms, theories, Alethe proofs. Depends on `covalence-types`, `covalence-sat`, `covalence-sexp`.
- **covalence-arrow** — wraps `arrow` (re-exported). Provides `parse_ipc()` auto-detecting Arrow IPC *file* (`ARROW1` magic) vs *stream* format, returning `ArrowInfo` (schema + row/batch counts).
- **covalence-parquet** — wraps `parquet` (re-exported). Provides `parse_file()` for a single Parquet blob and `scan_hive()` for a hive-partitioned tree (`key=value/` directories with `.parquet` leaves). Hive scanning is decoupled from storage via the `HiveSource` trait.
- **covalence-spectec** — wraps the `cyruscook/spectec_parse` crates (`spectec_ast`, `spectec_ast_decode`, `spectec_ast_decode_derive`, `wasm_spec_ast`) for consuming [SpecTec] — the DSL the WebAssembly specification is written in. Re-exports as `covalence_spectec::{ast, decode, decode_derive, wasm}`. The `wasm` module exposes the WebAssembly 3.0 spec pre-dumped as a SpecTec AST via `wasm::get_wasm_spectec_ast() -> Vec<ast::SpecTecDef>`. Used as an **untrusted driver** to lower WebAssembly semantics into HOL; a native Rust `.watsup` parser is a possible later addition. [SpecTec]: https://github.com/Wasm-DSL/spectec
- **covalence-graph** — ordered, typed, payload-polymorphic graph data structure (`Graph<P>` / `GraphBuilder<P>`, `BytesGraph` alias for the WIT-bridged form). `cov:graph@0.1.0` WIT in `wit/graph.wit`. Intended as a symmetric *premonoidal* category: node insertion order is the initialization order, and equality is strict structural (insertion-order-preserving). Inputs are linear (each wired at most once); outputs fan out freely. Substrate for the WASM linker (payload = component hash) and future string-diagram / dataflow consumers.

## Core Crates

The following crates provide the main application functionality:

- **covalence-store** — content-addressed blob store. Provides `ContentStore` trait, `BlobStore`, `TaggedStore`/`TaggedBlobStore`, `ObjectStore`/`KeyedObjectStore`, `GitPrefixStore`, `SharedMemoryStore`, `KvStore`, and `SqliteStore` (behind the `sqlite` feature, depends on `covalence-sqlite`).
- **covalence-object** — object serialization. Provides `Dir`/`DirBuilder` (directory structures with mode, name, child), `Table`/`TableBuilder` (row-based tables with LEB128 encoding), and git tree format conversion.
- **covalence-pure** — Isabelle/Pure–shaped logical framework (the TCB; ~1200 LoC). Locally-nameless terms, intrinsic typing, 8 LF rules + 6 equality rules + `inst_tfree` + `define`. `Thm::obs_eq<O: ObsEq>` is the *only* computational rule, sound under a parametric ε-model regardless of user impls (so observation policies are not in the TCB). See `docs/design/proposals/stacked-pure-hol/`.
- **covalence-pure-shell** — non-TCB shell around `covalence-pure`: handler-driven sexp serialisation, content hashing (BLAKE3-keyed), pretty-printing.
- **covalence-kernel** — *planned for rewrite.* The current implementation (arena + egraph + UF HOL kernel) will be replaced by an orchestration shell wiring `covalence-pure` + `covalence-hol` (forthcoming) + `covalence-store` + WASM evaluator + tree-store. See `docs/design/proposals/stacked-pure-hol/next-stages.md` for the migration plan.
- **covalence-repl** — S-expression REPL with kernel integration.
- **covalence-serve** — HTTP/WebSocket server (axum 0.8) with REST API, REPL WebSocket, and optional static file embedding.
- **covalence-client** — remote kernel client (sync via ureq, async via hyper).
- **covalence-lsp** — language server using `lsp-server` 0.7 + `lsp-types` 0.97.
- **covalence-proto** — service discovery and configuration (Unix sockets, JSON descriptors).
- **covalence-python** — Python bindings via PyO3 0.28.
- **covalence** — CLI binary (`cov`) using clap 4 + color-eyre.

This ensures dependencies are centralized and can be extended with project-specific functionality without touching every consumer.

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
