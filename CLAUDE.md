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
  (under `docs/`) and link it; don't inline it here.

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

## Reference Docs

The docs were pared down to the **current design only** (the old
multi-design docs — `ARCHITECTURE.md`, `AGENTS.md`, the arena/egraph
prover docs, `docs/design/proposals/*`, the old `MVP_DESIGN.md` /
`plan.md` — were deleted; recover any of them from the
`backup/pre-hol-cleanup` branch if needed). The four canonical docs:

- **[`docs/VISION.md`](./docs/VISION.md)** — the system vision
  (metatheory-as-default, scoped truths, the mirror principle, stores
  - WASM oracles).
- **[`docs/type-hierarchy.md`](./docs/type-hierarchy.md)** — the
  design we are building: the equality hierarchy and the `defs/` type
  catalogue (nat/int/rat/real/bytes/list/stream/option/result, → f32/f64).
- **[`docs/kernel-design.md`](./docs/kernel-design.md)** — canonical
  reference for `covalence-core` (the kernel TCB): term/type
  representation, the inference-rule surface, the four non-computational
  primitive rules, the `defs/` catalogue. **Read first if touching the
  kernel.**
- **[`docs/roadmap.md`](./docs/roadmap.md)** — what's next: finalize
  the `defs/` operations, the `covalence-kernel` re-export façade, and
  wiring `covalence-core` proofs back through the shell.

Plus four **design sketches** for the (not-yet-built) authoring layer
_above_ the kernel — aspirational, clearly marked as such:

- **[`docs/frontend.md`](./docs/frontend.md)** — the frontend & UX vision
  (counterpart to VISION.md's kernel focus): the unified surface that
  tracks terms as interpreted across many logics, reasoning as
  handler-dispatched algebraic effects, and the source-lowers-to-many-targets
  authoring workflow.
- **[`docs/surface-syntax.md`](./docs/surface-syntax.md)** — high-level
  syntax for writing theories, definitions, and proofs that elaborate
  down to kernel objects (the long-term replacement for hand-written
  `defs/`/`init/` Rust); declarative meaning with pluggable computation.
- **[`docs/surface-compiler.md`](./docs/surface-compiler.md)** — unifies
  `surface/` + `script/` into one language: theories and their **many
  models across many logics** as first-class objects (a model = a logic's
  handler set + an interpretation), and the multi-stage compiler
  (parse → resolve → elaborate+dispatch → lower → check) with span-carrying
  diagnostics.
- **[`docs/observers.md`](./docs/observers.md)** — how untrusted code
  feeds facts into the kernel's HOL model without growing the TCB
  (observer substrate exists today: `Observer` + `ObsEq`/`ObsTrue`/`ObsImp`;
  the validator/precondition layer is proposed).
- **[`docs/metatheory.md`](./docs/metatheory.md)** — theories,
  derivations, and models as first-class objects inside HOL; soundness
  theorems, theory transport, and the metavariable-layering decisions
  (two layers + HOL Light now; schematic-FOL framework and HOL-ω later).

Subsystem skills (auto-loaded when relevant): **wasm-guide**,
**vscode-extension**, **web-server**.

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
- **covalence-arrow** — wraps `arrow` (re-exported). Provides `parse_ipc()` auto-detecting Arrow IPC _file_ (`ARROW1` magic) vs _stream_ format, returning `ArrowInfo` (schema + row/batch counts).
- **covalence-parquet** — wraps `parquet` (re-exported). Provides `parse_file()` for a single Parquet blob and `scan_hive()` for a hive-partitioned tree (`key=value/` directories with `.parquet` leaves). Hive scanning is decoupled from storage via the `HiveSource` trait.
- **covalence-spectec** — wraps the `cyruscook/spectec_parse` crates (`spectec_ast`, `spectec_ast_decode`, `spectec_ast_decode_derive`, `wasm_spec_ast`) for consuming [SpecTec] — the DSL the WebAssembly specification is written in. Re-exports as `covalence_spectec::{ast, decode, decode_derive, wasm}`. The `wasm` module exposes the WebAssembly 3.0 spec pre-dumped as a SpecTec AST via `wasm::get_wasm_spectec_ast() -> Vec<ast::SpecTecDef>`. Used as an **untrusted driver** to lower WebAssembly semantics into HOL; a native Rust `.watsup` parser is a possible later addition. [SpecTec]: https://github.com/Wasm-DSL/spectec
- **covalence-graph** — ordered, typed, payload-polymorphic graph data structure (`Graph<P>` / `GraphBuilder<P>`, `BytesGraph` alias for the WIT-bridged form), plus `LabelList` / `KindFlags` overlay blobs and a `StringDiagram` composite that references them. `cov:graph@0.1.0` WIT in `wit/graph.wit` splits into a topology-only `api` interface and a `string-diagram` interface for the overlay world. Intended as a symmetric _premonoidal_ category: node insertion order is the initialization order, and equality is strict structural (insertion-order-preserving). Inputs are linear (each wired at most once); outputs fan out freely. Per-node labels and `pure`/`ordered` classification are NOT part of the graph itself — they live in overlay blobs so the same topology can be presented differently by different consumers. A pure-Rust `render_svg` produces standalone SVG markup from a resolved diagram.

## Core Crates

The following crates provide the main application functionality:

- **covalence-store** — content-addressed blob store. Provides `ContentStore` trait, `BlobStore`, `TaggedStore`/`TaggedBlobStore`, `ObjectStore`/`KeyedObjectStore`, `GitPrefixStore`, `SharedMemoryStore`, `KvStore`, and `SqliteStore` (behind the `sqlite` feature, depends on `covalence-sqlite`).
- **covalence-object** — object serialization. Provides `Dir`/`DirBuilder` (directory structures with mode, name, child), `Table`/`TableBuilder` (row-based tables with LEB128 encoding), and git tree format conversion.
- **covalence-core** — **the TCB** (safe Rust). HOL-Light-style kernel with locally-nameless `Term`/`Type`. The only logical primitives are `=` (`TermKind::Eq`) and `ε` (`TermKind::Select`); `T`/`F` are `Bool` literals; every connective (`∧ ∨ ¬ ⟹ ⟺ ∀ ∃`) is an ordinary _defined constant_ in `defs/logic.rs`. Rules: HOL Light's 10 primitives + well-known derived rules provided as fast constructors with `Soundness:` docstrings (sym, cong_app/abs, imp_intro/elim, all_intro/elim, eta_conv, **and the connective rules** and_intro/and_elim/or_intro/or_elim/not_intro/not_elim); `define` + `new_type_definition` (conservative extension); `reduce_prim` + `unfold_term_spec` (accelerated reduction — sound by literal denotation); `Term::spec_abs`/`spec_rep` (carrier↔wrapper coercions for any derived `TypeSpec`, theorem-free). **Four non-computational primitive rules**: `Thm::nat_induct` (induction: base+step ⟹ `∀n. P n`), `Thm::false_elim` (ex falso), `Thm::unit_eq` (the `unit` singleton: `⊢ a = b` for `a, b : unit`), and `Thm::lem` (excluded middle `⊢ p ∨ ¬p` — the classicality axiom, derivable from ε the usual HOL way, exposed directly for now). The observer rules `obs_eq`/`obs_true`/`obs_imp` are sound under a parametric ε-model. The `defs/` catalogue holds the type/term definitions (`int := (nat × nat)/~` Grothendieck, `unit := { b : bool | b = T }`, `bytes := list u8`, the logic connectives, nat/int arithmetic, the `prod`/`coprod`/`option`/`result`/`list` constructors via abs/rep, …); literals (`TermKind::Int`, `Blob`) stay built-in for binary-data efficiency. Catalogue symbols use dotted names (`nat.add`, `coprod.case`, `option.some`, `unit.nil`). **Canonical reference: [`docs/kernel-design.md`](./docs/kernel-design.md).**
- **covalence-hol** — **the HOL "rewrite": a non-TCB shell over `covalence-core`.** (1) HOL term/type builder API (`HolLightCtx`, the `HolLightKernel`/`HolLightTerms`/`HolLightTypes` traits). (2) `proofs/` — pure proof tactics (`beta_nf`, `unfold_at_*`, rewriting) and the executable derivations that witness the soundness of the kernel's fast connective methods. (3) Content hashing (BLAKE3-keyed) and canonical S-expression syntax. _No postulates_ — the old `nat_axioms`/`int_axioms`/`init` (formerly `stdlib`) postulate catalogues and the gated Pure-era `bridge`/`peano`/`pure_hol` modules were deleted (recover from `backup/pre-hol-cleanup`).
- **covalence-kernel** — _legacy, pending rewire._ The current contents (arena + egraph + UF kernel) are superseded; the target is a thin **re-export façade** = `covalence-hol` + `covalence-store` + … (the whole TCB + content-addressing foundation) that `covalence-shell` sits on top of. See [`docs/roadmap.md`](./docs/roadmap.md). The whole app stack (`covalence-shell`, `repl`, `serve`, `client`, `alethe`, `egglog`, the `cov` CLI) currently rides on this legacy crate and migrates with it.
- **covalence-repl** — S-expression REPL with kernel integration.
- **covalence-serve** — HTTP/WebSocket server (axum 0.8) with REST API, REPL WebSocket, and optional static file embedding.
- **covalence-client** — remote kernel client (sync via ureq, async via hyper).
- **covalence-lsp** — language server using `lsp-server` 0.7 + `lsp-types` 0.97.
- **covalence-proto** — service discovery and configuration (Unix sockets, JSON descriptors).
- **covalence-python** — Python bindings via PyO3 0.28 for the content-addressing / store / WASM / SAT / graph surface. (The HOL kernel bindings — the `pure` module exposing `Type`/`Term`/`Thm` — were removed in the rewrite; they'll be reinstated on `covalence-hol`.)
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
