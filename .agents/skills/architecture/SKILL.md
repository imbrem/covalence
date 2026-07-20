---
name: architecture
description: Covalence repo layout, dependency graph, and key architectural rules
disable-model-invocation: true
---

## Repo Layout

- `crates/kernel/` — low-level, stable capability APIs and trusted
  implementations. APIs here should be shaped so they can become WIT-facing
  component boundaries; being under `kernel/` does not by itself mean being
  trusted.
- `crates/lang/` — high-level concrete language frontends and language-specific
  policy (for example Scheme). `kernel/` and `lang/` are responsibility
  boundaries, not a blanket dependency ordering: dependencies may point either
  way across them so long as the Cargo package graph stays acyclic. Extract a
  shared interface/IR package when an actual package cycle would otherwise
  arise.
- `crates/app/cov/` — Main binary crate (`cov` CLI)
  - `src/main.rs` — Entry point with clap derive; dispatches to `cov lsp`, `cov cog`, `cov serve`, `cov repl`
  - `src/highlight.rs` — S-expression syntax highlighting for the REPL
  - `src/lib.rs` — Shared constants (`VERSION`, `TARGET`)
  - `build.rs` — Sets `COV_TARGET` env var from the Cargo build target triple
- `crates/kernel/core/` — **HOL kernel** (experimental, planned for rewrite — see crate-level docs in `src/lib.rs`)
  - Files: `arena.rs`, `egraph.rs`, `eprop.rs`, `hash.rs`, `id.rs`, `kernel.rs`, `primop.rs`, `prop.rs`, `reduce.rs`, `subst.rs`, `term.rs`, `ty.rs`, `uf.rs`
  - Deps are minimal (`bytes`, `smol_str`, `covalence-hash`, `covalence-types`); does NOT depend on `covalence-wasm` or `wasmtime` in this branch.
  - The Sync/Async backend traits (`SyncBackend`, `AsyncBackend`, `BackendInfo`, `KernelError`) now live in `crates/kernel/shell/` (`pub use traits::{...}` in `src/lib.rs`). Update this section when the kernel is re-integrated with the shell.
- `crates/kernel/logic/` — dependency-free logic API vocabulary
  - `Logic` owns the associated kind/type/term/theorem/error carriers.
  - Capability traits split type operators, term binders, equality, quantifiers,
    and proof rules; `relation` provides typed `Arrow` values and basic
    relational algebra. Products, coproducts, tabulation, reflexive-transitive
    closure, and residuals are optional syntax capabilities with separate
    proof-law interfaces.
- `crates/kernel/data/numeric/` — numeric theories over the logic carriers
  - `nat` provides representation-independent natural-number syntax,
    arithmetic, order, supplied law bundles, and optional decision/normalization
    capabilities.
  - `int` gives mathematical integers the same capability-sized syntax,
    arithmetic, order, law, decision, and normalization structure. Concrete
    NativeHol ordered-ring compatibility remains in `covalence-hol-api` while
    consumers migrate.
- `crates/kernel/data/` — representation-independent scalar data and morphisms
  - `scalar` owns Bit/Bits, Byte/Bytes, Unicode scalar/String, and UTF-8/UTF-16
    capabilities.
  - `morphism` owns explicit cross-representation adapters such as Nat-backed
    radix-256 bytes. It must not contain S-expression, Lisp, JSON, K, or WASM
    domain concepts.
  - The abstract crate depends on `kernel/logic` and `data/numeric`; NativeHol
    datatype realization remains temporarily in `covalence-init` pending the
    separate `kernel/data/hol` extraction.
  - `covalence-init`'s `NativeHol` implements the extracted carrier and core
    capabilities; `covalence-hol-api` keeps the legacy concrete-HOL Nat facade
    as a forwarding compatibility adapter while consumers migrate.
  - `covalence-init::init::inductive::DoubleSuccNat` is a distinct Nat API
    backend whose nonzero literals use the derived binary double/successor
    encoding. It still shares native carriers and theory operations; it is a
    representation stress test, not yet complete leaf elimination.
  - `covalence-init::init::inductive::UnaryNat` is the corresponding
    linear-depth successor-tower backend. The representation adapters share
    their native-theory capability delegation in `nat_backend_common.rs`;
    neither advertises decision or normalization capabilities.
- `crates/kernel/lisp/` — stable, backend-neutral Lisp capability tower
  - `sexpr/` owns the abstract inductive S-expression API. Parsing remains in
    `crates/lang/sexpr-parsing`; concrete Lisp languages remain under
    `crates/lang/`.
  - The root package separates common syntax, explicit evaluation strategies,
    one-step relations, finite checked traces, and proof-producing replay
    capabilities. Its host CEK-style realization is proof-free and exists for
    trace discovery and differential/conformance testing. The host strategy is
    operational: it supports lexical or dynamic scope, deterministic
    left-to-right or right-to-left evaluation of operator and operands, and a
    relational mode whose bounded breadth-first explorer retains every
    discovered trace and an explicit truncated frontier. Effects use the A0025
    suspend/request/resume API: pure machines never perform host actions;
    proof-free handlers return responses and retain auditable transcripts,
    while theorem authority requires a separate replay capability.
  - `crates/lang/lisp` is the current compatibility/demo frontend. Its
    NativeHol `LispRel` implements the neutral step and replay capabilities,
    while ACL2-specific worlds and derivations are incrementally separated
    above the common Lisp semantics. Production Scheme and Sector sessions,
    plus translated ACL2 expression execution, lower through the shared
    `CoreExpr`; Scheme compiles it to equational HOL and Sector to relational
    HOL. The proof-free Forsp frontend instead targets the sibling stack
    capability because its call-by-push-value semantics is genuinely
    concatenative. `kernel/lisp::StackMachine` owns the
    representation-neutral transition algorithm for lexical closures,
    bindings, resolution, and continuations; a frontend supplies an observable
    instruction backend and WIT-shaped primitive dictionary.
    `kernel/lisp::StackEffectMachine` likewise owns the generic
    suspend/resume loop; the frontend policy maps effects plus an operand list
    to requests and maps responses back to operands. Forsp `read`/`print` and
    optional low-level pointer primitives suspend through A0025; the bundled safe host adapter handles
    only I/O and rejects pointer requests. Effect suspension observes the
    generic instruction layer, so it does not depend on the concrete
    instruction representation. Pure Forsp machines implement the
    common terminal-value observation and therefore produce checked `MayEval`
    traces on both the direct and opaque-resource runtimes; effectful runs
    retain the separate suspension/resume transcript.
  - Applicative and concatenative primitive dictionaries both transfer owned
    finite value lists rather than borrowing Rust slices. This is intentional:
    it keeps primitive dispatch resource-safe and directly expressible as WIT.
    Applicative dictionaries return either a value or an explicit request;
    `kernel/lisp::LispEffectMachine` preserves the suspended CEK continuation,
    validates it on resumption, and runs unchanged over direct or opaque-handle
    runtime representations. Pure execution rejects those requests rather than
    performing host effects. `LispIoRequest`/`LispIoResponse` are the common
    read/write protocol used by both Scheme's applicative dictionary and
    Forsp's stack-effect policy; Forsp layers its unsafe pointer requests around
    that protocol rather than defining a second I/O vocabulary.
    `lang/lisp::SchemeSession` specializes the generic stateful
    `RuntimeSession<R, P>` with that dictionary and returns a value plus the
    complete handled-effect transcript; the default `P = StandardPrimitives`
    preserves the pure Scheme/Sector/ACL2 session API.
- `crates/lang/computation/` — dependency-free computation theory, execution,
  compiler, simulation, and machine-model APIs.
  - `automata_api` (A0011) separates relational finite-automata syntax,
    universal closure/acceptance law bundles, untrusted search witnesses, and
    replay. Its core covers DFA/NFA uniformly; determinism and epsilon closure
    are optional capabilities.
  - Native HOL realizations and replay seams live in
    `crates/kernel/hol/init/src/init/computation/`.
  - Search witnesses are plain data and non-authoritative. Replay must
    reconstruct a kernel theorem and reject forged candidates; bounded replay
    milestones must not be described as universal semantic preservation.
- `crates/lang/grammar/` — neutral grammar IR; it must not depend on parser
  evaluation APIs.
- `crates/lang/cfg-parsing/` — bounded A0015 relational evaluator layered over
  both `covalence-grammar` and `covalence-parsing-api`. Derivation trees are
  untrusted data, ambiguity is retained, and exact versus prefix parsing is
  explicit. `ChartCfgParser` handles left recursion and nullable productions
  with explicit work/chart/result bounds. Its shared packed forest interns
  `(nonterminal, span)` nodes and represents nullable cycles finitely; expanding
  trees is a separately bounded operation that reports truncation.
- `crates/lang/regex-parsing/` — optional bounded A0013/A0015 evaluators for
  the syntax in `covalence-grammar`.
  - Functional evaluation uses an explicit longest-prefix policy; relational
    evaluation enumerates distinct accepted prefixes rather than derivation
    trees.
  - Host match witnesses carry no theorem authority. Logic-level replay and
    soundness/completeness capabilities remain separate.
- `crates/lang/lexer-parsing/` — A0016 bounded lexical analysis layered over
  regex parsing. Maximal munch, rule priority, ambiguity, skipped tokens, and
  byte/scalar source spans are explicit policy or witness data. Nullable token
  rules are rejected so tokenization cannot loop without consuming input.
- `crates/lang/peg-parsing/` — A0019 capture/action-free PEG syntax and
  bounded deterministic evaluation over bytes or Unicode scalars. Ordered
  choice, lookahead, recursion, exact/prefix policy, and limits are explicit;
  nullable repetition and left recursion fail rather than looping. Host
  witnesses carry no theorem authority.
- `crates/server/client/` — Remote backend implementations
  - `src/sync_client.rs` — `SyncHttpBackend` (ureq for TCP, raw HTTP/1.1 for Unix domain sockets)
  - `src/async_client.rs` — `AsyncHttpBackend` (hyper for TCP + UDS)
  - Features: `sync` (ureq), `async` (hyper)
- `crates/lib/hash/` — Cryptographic hash types (`O256`, `IdentityHasher`), git hashing (feature-gated on `git`)
- `crates/store/core/` — Generic store traits (`StoreGet`, `StoreGetRef`, `StorePut`, `StorePutMut`) and implementations
  - `MemoryStore`/`SharedMemoryStore` (feature `memory`, default)
  - `SqliteStore` (feature `sqlite`, backed by `covalence-sqlite`)
- `crates/lib/sqlite/` — Low-level SQLite blob store (rusqlite)
- `crates/lib/sexp/` — S-expression parser/printer (`parse()`, `prettyprint()`, `offset_to_line_col()`)
- `crates/lib/wasm/core/` — WASM/WAT gateway (see `wasm-guide` skill)
  - `src/validate.rs` — `compile_wat()` (WAT→WASM), `wasm_to_wat()` (WASM→WAT) — always available
  - `src/parse.rs` — `parse_module()`, `parse_component()` — binary inspection via wasmparser
  - `src/build.rs` — programmatic `ModuleBuilder` (~840 LoC)
  - `src/component.rs` — `encode_core_as_component`
  - `src/val.rs` — engine-agnostic `Val` / `ValType` (component-model values)
  - `src/engine.rs` — one-line `pub use wasmtime;` gated behind `runtime` feature (no higher-level abstraction yet)
  - `src/lib.rs` — `WasmError` enum
- `crates/server/lsp/` — Language server library (used by `cov lsp`)
  - `src/lib.rs` — LSP handlers for sexp files (`.smt`, `.smt2`, `.alethe`, `.cov`) and WAT files (`.wat`)
- `crates/lib/git/` — Cogit VCS library (used by `cov cog`)
- `crates/server/core/` — Web server library (used by `cov serve`)
  - `src/lib.rs` — `ServeConfig`, `ServeError`, `AppState` (holds `Kernel`), `run_serve()`
  - `src/api.rs` — REST API handlers (blobs, WAT, eval, decide, etc.)
  - `src/eval.rs` — `server_session()` — creates a REPL Session backed by a Kernel
  - `src/static_files.rs` — rust-embed static file serving with SPA fallback (feature `static`)
  - `build.rs` — Warns if `apps/covalence-web/build/` is missing (only when `static` feature enabled)
- `crates/lib/proto/` — Service discovery + configuration
  - `src/discovery.rs` — Server registration/discovery via XDG runtime dir
  - `src/config.rs` — Default paths (XDG data dir)
  - `src/error.rs` — `DiscoveryError`
- `apps/covalence-web/` — SvelteKit web app (adapter-static, SPA mode)
  - `src/lib/api.ts` — API client; base URL configurable via `VITE_COV_API_BASE` env var
  - `src/routes/+page.svelte` — Landing page with API health monitor (polls `/api/health` every `HEALTH_POLL_MS`)
  - `build/` — Static output embedded into the Rust binary (gitignored)
- `packages/covalence-ui/` — Shared Svelte 5 component library (scaffold, for future use)
- `extensions/covalence-vscode/` — VSCode extension (desktop + web)
  - `src/extension.ts` — Extension activation, LSP startup, restart command
  - `src/server.ts` — LSP server creation: detects native `cov` binary, falls back to WASM
  - `scripts/build.ts` — Build script (cargo rustc → esbuild → copy wasm)
  - `syntaxes/` — TextMate grammars for SMT (`smt.tmLanguage.json`) and WAT (`wat.tmLanguage.json`)
  - `dist/` — Final bundles (gitignored)

## Dependency Graph

**Status: partially stale — needs a fresh audit.** The high-level shape (covalence-wasm base vs runtime feature; client/repl staying lightweight; serve using Kernel + traits) is still directionally right, but specific claims about which crate owns which trait have moved (see kernel/shell note above). Verify against `Cargo.toml` files before relying on the details below.

```
covalence-wasm (WASM gateway)
  ├─ base: compile_wat(), wasm_to_wat(), parse_module(), parse_component(), build::*, encode_core_as_component
  └─ [runtime]: re-exports wasmtime (no abstraction layer yet — direct wasmtime usage in consumers)

covalence-shell (backend traits — formerly in covalence-kernel)
  └─ SyncBackend, AsyncBackend, BackendInfo, KernelError

covalence-client (remote backend implementations) — depends on covalence-shell
  ├─ [sync]: SyncHttpBackend (ureq + raw UDS)
  └─ [async]: AsyncHttpBackend (hyper + UDS)

covalence-repl (Session + command evaluation)
  ├─ Uses Box<dyn SyncBackend> from covalence-shell
  ├─ Always depends on covalence-wasm (base) for WAT ops
  └─ [fetch]: ureq for store-url

covalence-proto (discovery + config only)
  └─ No client code — just registration, discovery, and default paths

covalence-serve (HTTP server) — depends on covalence-shell::KernelError
```

**Key rules (still applicable):**

- `SyncBackend` trait is dyn-compatible (for REPL's `Box<dyn SyncBackend>`)
- `AsyncBackend` trait uses native `async fn` (NOT dyn-compatible — used with concrete types)
- `covalence-repl` and `covalence-client` stay lightweight (no wasmtime)

## CLI (`cov`)

Uses clap derive for arg parsing, `color-eyre` for error reporting (native only), and `tracing` + `tracing-subscriber` for logging (default level: `info`, override with `RUST_LOG`).

Features (all default, all compile on WASM except native-only deps are target-gated):

- `lsp` — `cov lsp` subcommand
- `cogit` — `cov cog` subcommand
- `serve` — `cov serve` subcommand (prints error on WASM; axum/tokio deps are `cfg(not(wasm))`)
- `repl` — `cov repl` subcommand (interactive S-expression REPL with syntax highlighting)

## Open work

Open work is authored as stable source-local markers such as
`TODO(cov:hol.script.source-spans, severe): ...`. Run `bun run todos` to
regenerate `docs/todos/todos.json` and `target/covalence-todos.sqlite`, or query
with `bun run todos -- --list`. The old `SKELETONS.md` registries have been
removed; do not recreate them.

Portfolio planning and current-state triage live in
`notes/vibes/plans/workstreams-and-state-report.md`. It divides work into
control-plane, TCB/base, HOL representation, abstract API, script/project,
metatheory, ACL2/Lisp, SAT/SMT, parsing/data, WASM/SpecTec/K, and product
workstreams. Use stable TODO IDs for ownership across those streams.

## REPL (`cov repl`)

Interactive S-expression evaluator with a content-addressed blob store. Backend is selected at startup:

- `--connect URL` → `SyncHttpBackend` (remote)
- `--standalone` → `Kernel` (in-process)
- Default → auto-discovery (find running server) → fallback to `Kernel`

Storage: `--store` enables SQLite persistence, `--memory` (default) uses in-memory.

Commands:

- `(store "data")` — hash and store inline text as a blob
- `(store-url "url")` — fetch URL content and store as blob
- `(store-file "path")` — read file and store as blob
- `(read <hash>)` — print blob as UTF-8 text
- `(read-wat <hash>)` — decompile blob as WASM→WAT
- `(module ...)` — compile WAT module, store as blob
- `(component ...)` — compile WAT component, store as blob
- `(parse-module <hash>)` — inspect WASM module imports/exports
- `(parse-component <hash>)` — inspect WASM component imports/exports
- `(decide <hash>)` — decide if a proposition (WASM component) calls attest() on startup
- `(list)` — list all stored blob hashes
- `(status)` — show backend connection info
- `(help)` — show available commands
- `(arrow-stats <hash>)` — parse blob as Arrow IPC, print schema + row/batch counts (requires `covalence-repl/arrow`)
- `(parquet-stats <hash>)` — parse Parquet stats; dispatches on `is_tree(hash)` — a tree is scanned as a hive-partitioned dataset (`key=value/` dirs with `.parquet` leaves), a blob is parsed as a single file (requires `covalence-repl/parquet`)
