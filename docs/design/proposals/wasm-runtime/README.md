# Proposal: `cov:wasm/*` WIT runtime + processes + containers

**Status:** proposed (2026-06-06). Three slices landed:
- **Phase 0 (wasmtime host):** `crates/covalence-wasm/{wit/cov-wasm.wit,src/runtime.rs}` — WIT + `wasmtime::component::bindgen!`-generated host trait, wasmtime impl. Both core modules (via `wasmtime::Module`) and components (via `wasmtime::component::Component`) supported through a `HostComponent`/`HostInstance` enum-dispatch.
- **Phase 1 floor (build interface, Rust host):** `cov:wasm/build` interface with `build-add-module(name, delta)` canned recipe AND a `module-builder` resource exposing constructor, `start-func` / instructions (`local-get`, `local-set`, `i32-const/add/sub/mul`, `call`) / `end-func` / `export-func` / `finish`. Rust impl is a thin wrapper around `covalence_wasm::build::ModuleBuilder` (no parallel recording layer — holds the real builder directly).
- **Phase 3 floor (JS host):** `packages/covalence-wasm-js/` — TS `Runtime` class mirroring `cov:wasm/runtime`, `WebAssembly.*`-backed for core modules AND `@bytecodealliance/jco`-backed for components. Components are transpiled at runtime (jco `instantiation: 'sync'`), loaded via a `data:` URL to dodge Vite's static analysis, and exposed under the same uniform `WasmInstance` / `callU32` API. **JS contributes only the executor — no build logic.** Run via `bun run test:wasm-js`.
- **Metacircular demo:** `crates/covalence-wasm-build-guest/` compiles `covalence_wasm::build::ModuleBuilder` to wasm32-unknown-unknown via a small C-ABI wrapper (`build_plus(delta) -> length` + `output_ptr() -> i32`). Loaded into the JS Runtime, called, and its output is fed back through the same Runtime — all in one process, with the build logic living in shared Rust code. Rebuild: `bun run build:wasm-build-guest`.

Metacircular smoke test passes in both backends:
- **Rust:** the `module-builder` resource builds `(x: i32) -> i32 { x*3 + 1 }` (two functions wired via `call`); same `RuntimeHost` compiles and runs it.
- **JS:** the Rust-built guest's `build_plus(5)` produces wasm bytes; the same `Runtime` compiles those bytes and `callU32(inst, "answer", 37)` returns 42.

A staged path to:
1. Abstract `covalence-wasm`'s engine surface behind a WIT API (`cov:wasm/*@0.1.0`) so the same Rust code can target wasmtime, a browser JS host, or any future runtime — and so the API is callable from inside WASM components themselves.
2. Layer two structural abstractions — **process** (a shared-fate graph of components) and **container** (a tree of processes with restart policies) — on top of the bare runtime.
3. Build a covalence kernel that runs entirely in the browser, so `covalence-ui` works as a static site with no server dependency, and (longer-term) can federate with a server kernel rather than depend on it.

---

## 1. Why WIT-first

Today `crates/covalence-wasm/src/engine.rs` is one line: `pub use wasmtime;`. Two consumers (`covalence-sat`, `covalence-wasm-spec`) reach straight through it. There is no abstraction.

A hand-written Rust trait would be a fine abstraction for *host code*, but it cannot be called from inside WASM. By defining the same surface as a WIT package, three impls fall out of one spec:

- **Native host**: implements the generated Rust traits using `wasmtime` + existing covalence-wasm code.
- **Browser host**: implements the same generated traits via `wasm-bindgen` + the browser `WebAssembly.*` API, with `jco`-transpiled JS modules keyed by O256 hash for the component-model case (see [`store-identity-component-hash`] memory).
- **Guest impl**: `inspect` and `build` can be implemented as a WASM component itself, since `wat`/`wasmparser`/`wasm-encoder`/`wit-component` all compile clean to `wasm32-wasip1-threads`. Only `runtime` must be host-provided.

This makes the runtime metacircular: components running on the kernel can build, inspect, and run other components — independent of where they're hosted.

## 2. Surface shape

Three interfaces in the `cov:wasm@0.1.0` package, plus a shared `types` interface that mirrors `covalence_wasm::val::{Val, ValType}`.

| Interface | Purpose | Implementable in-guest? |
|-----------|---------|-------------------------|
| `types`   | `val` / `val-type` variants — the canonical-ABI value lingua franca | n/a (just types) |
| `inspect` | `parse-module`, `parse-component`, `compile-wat`, `wasm-to-wat` | **yes** — wraps existing base-feature covalence-wasm code |
| `build`   | `module-builder` resource (mirror of `build::ModuleBuilder`), `encode-core-as-component` | **yes** |
| `runtime` | `component` / `instance` resources, `compile` / `instantiate` / `call` | **no** — must be host-provided |

**Sync-first.** All v0 exports are synchronous. Per the conversation that produced this proposal: simplicity wins over async-from-day-one for the WIT itself; we can add async variants alongside if/when a use case forces it. The host backends are free to drive the underlying engine async-style internally.

**Exact WIT shape is deferred** to implementation — resource semantics under wit-bindgen are non-trivial (see [`wit-component-gotchas`] memory: `interface-api` wrapping for exported resources, `cabi_realloc` growth, `resource-new` handle wrapping, variant→WIT convention). The MVP § below pins down only what we need first.

## 3. Process: shared-fate graph of components

**A *process* is a recursive graph of WASM components whose fate is shared.** If any node traps, the whole process is dead. Components are linked statically before execution begins — node A's WIT-typed import is satisfied by node B's matching export, recursively, until the import surface is closed under what the host provides.

Recursive: a process can itself appear as a node in a larger process. A "sub-process" is just a closed sub-graph that fits the parent's expected interface. This mirrors how the WASM component model already composes — the proposal is to lift that into a first-class concept the kernel manipulates.

Why this matters: the kernel often wants to run not "one component" but "this decision procedure linked against that hash oracle linked against that proof-witness reader." Today (in the spec harness, `crates/covalence-wasm-spec/tests/common/mod.rs`) that linking is hand-rolled per consumer. Lifting it to a process abstraction means:

- One representation (a content-addressed DAG of component hashes + edge labels) the kernel can store, hash, and replay.
- One execution path: `process.run()` instantiates the graph, calls the entrypoint, returns the result or the trap.
- Composability: a `process` is itself something you can hand to another process as a callable resource.

Process-level **does not** include restart, supervision, or retry — that's the container layer.

## 4. Container: tree of processes with operational policies

**A *container* is a recursive tree of processes carrying operational policy.** Each container node declares, for its children:

- **Restart policy** — Erlang/OTP-style choices: `one-for-one` (restart only the failed child), `one-for-all` (restart all children when one fails), `rest-for-one` (restart the failed child and everything started after it), `transient` (one-shot, propagate failure up), `permanent` (always restart).
- **Restart strategy** — immediate, fixed delay, exponential backoff, max-restarts-per-window.
- **Trap handling** — propagate, swallow, restart, log-and-continue.
- **Resource ceiling** — memory / fuel / wall-clock limits (delegated to the runtime backend where supported).

A container is itself recursive: containers contain containers. The leaves are processes.

This layer is **explicitly out of scope for MVP** and likely Phase 3+. But naming it now matters: it tells the v0 API not to bake one-shot semantics into the runtime interface, because the eventual operational mode is supervised.

## 5. End-state vision: browser kernel + federation

The driving end-state has two pieces.

**Browser kernel (static covalence-ui).** Today `apps/covalence-web` (SvelteKit + adapter-static) is a thin client that talks to a `cov serve` backend over HTTP. With a WIT-runtime browser host plus the existing kernel and store compiled to `wasm32`, the same static bundle ships a full local kernel. Users get a covalence-ui that works offline, on GitHub Pages, embedded in docs, or anywhere a static site loads — no backend required for any read-only or local-write workflow.

This depends on: (1) the browser host impl of `cov:wasm/runtime`; (2) browser-friendly store backends (IndexedDB or OPFS — covalence-store's trait surface is already committed to portability per [`store-api-portable`]); (3) audit of covalence-git and any networking pieces.

**Federation (longer-term).** The local browser kernel speaks the same protocol as the remote `cov serve` kernel (via existing covalence-client / covalence-proto). Long-term, a local kernel and remote kernels are peers — local-first with sync, content-addressing making replication trivial. The browser-kernel work is the prerequisite; the federation protocol is its own design proposal.

## 6. MVP scope

The smallest thing worth shipping is the simplest possible runtime: **compile, instantiate, and call one self-contained component, synchronously**, behind a WIT interface that already lives in the right place to grow.

WIT for v0:

```wit
package cov:wasm@0.1.0;

interface types {
    // Mirror of covalence_wasm::val::ValType / Val. Exact variant shape TBD;
    // start with the subset covalence-wasm-spec actually uses (primitives,
    // list, record, tuple, option, result, string). Resources deferred.
    variant val      { /* … */ }
    variant val-type { /* … */ }
}

interface runtime {
    use types.{val};

    resource component;
    resource instance;

    /// Compile component bytes. Caller owns the resulting `component`.
    compile: func(bytes: list<u8>) -> result<component, string>;

    /// Instantiate a component whose only imports are canonical-ABI
    /// intrinsics the host can stub (mirrors what the spec harness
    /// already does via `define_unknown_imports_as_traps`). Imported
    /// interfaces beyond that are out of scope for v0.
    instantiate: func(c: borrow<component>) -> result<instance, string>;

    /// Call an export by (optional interface name, export name).
    /// Args and results use the engine-agnostic `val` type.
    call: func(
        inst: borrow<instance>,
        iface: option<string>,
        export: string,
        args: list<val>,
    ) -> result<list<val>, string>;
}

world cov-wasm { export runtime; }
```

**Scope of "self-contained component":**
- Imports nothing the host cannot stub as a trap (i.e. canonical-ABI intrinsics only).
- No multi-component linking — that's process scope.
- No host-provided imports — that's later (probably a `cov:wasm/host` interface).
- Sync exports only.

**Implementation steps for MVP:**

1. **Define the WIT** (`crates/covalence-wasm/wit/cov-wasm.wit`) and wire wit-bindgen so the generated host trait builds.
2. **Wasmtime impl** of the generated trait — wraps the existing wasmtime usage from `covalence-wasm-spec/tests/common/mod.rs`. Reuses the `define_unknown_imports_as_traps` stubbing pattern.
3. **Port covalence-wasm-spec's `Harness`** to use the WIT-generated trait instead of `wasmtime::*` directly. This is the smoke test — if every existing spec test still passes through the trait, the surface is good enough.
4. **Stop.** Don't add `inspect`, `build`, browser host, or anything else in MVP. Each is its own follow-up phase. The `runtime` slice alone unblocks all the later work.

**Keep `pub use wasmtime;`** alongside the new interface — covalence-wasm-spec's fuzz targets exercise wasmtime-specific knobs and shouldn't be forced through the trait.

## 7. Phasing beyond MVP

Rough ordering, not a commitment:

| Phase | Adds | Unblocks |
|-------|------|----------|
| 0     | MVP `cov:wasm/runtime` + wasmtime backend | Single-component execution behind an abstraction |
| 1     | `cov:wasm/inspect` + `cov:wasm/build`, sync | Programmatic WASM authoring; metacircular base |
| 2     | Guest-component impl of `inspect`+`build` | "Build/inspect WASM from inside WASM" — first real use of the WIT being callable from guests |
| 3     | Browser JS host backend (core modules + `jco` components keyed by O256) | Run WASM in the browser at all |
| 3.5   | Component-model interpreter as a Rust→wasm guest (replaces per-component jco JS bundle with one shared interpreter + per-component metadata) | Retires the duplicated 80 KB jco runtime; same interpreter on native and browser |
| 4     | Browser-friendly store backends (IndexedDB/OPFS) | Browser kernel can persist |
| 5     | Process abstraction — content-addressed graph of components, linker that closes import graphs | Multi-component execution without per-consumer wiring |
| 5.5   | **Linker as a wasm-resident program** (see §9) — takes a root component hash + a store handle, walks the dependency graph, produces an instantiated process. Linking policy is itself content-addressed and pluggable. | Kernel stops embedding linking knowledge; linking becomes an artifact others can swap out |
| 6     | Container abstraction — restart policies, supervision trees | Production-grade execution of untrusted user components |
| 7     | Static covalence-ui shipping a local kernel | The headline deliverable |
| ∞     | Federation protocol between local kernels and `cov serve` peers | Local-first covalence |

## 8. Non-goals (for the proposal, not just MVP)

- **Async WIT at v0.** We may add async variants alongside if a real use case demands it; we don't gate the runtime on async resources working under wit-bindgen yet.
- **Generic in-browser component runtime.** The covalence-specific hash-keyed dispatch (via `jco` pre-transpile of the small known set of components) makes this unnecessary for years.
- **Replacing direct wasmtime usage in fuzz/perf-sensitive consumers.** The `pub use wasmtime;` re-export stays.
- **Resources-as-imports in v0.** Resource handles only appear as outputs of `runtime` (the `component` and `instance` types).

## 9. Long-term: the linker as a wasm-resident program

The endpoint the whole `runtime` / `build` / process stack is reaching toward: **linking is a wasm program over the store, not host code.**

### The shape

A "linker script" is itself a content-addressed WASM artifact. Its world looks roughly like:

```wit
package cov:link@0.x;

interface api {
    use cov:store/api.{store, blob};
    use cov:wasm/runtime.{component, instance};

    /// A description of what to assemble: which root hash, which
    /// concrete imports satisfy which expected interfaces, what
    /// policy to apply when something is missing.
    record link-request {
        root: blob,                  // O256 of the root component
        imports: list<binding>,      // (expected-import, satisfying-export)
        policy: link-policy,
    }
    record binding { ... }
    enum link-policy { eager, lazy, strict, ... }

    /// Walk the request's dependency graph, fetch each component from
    /// the store, resolve every WIT-typed import to a matching export,
    /// then hand back something the runtime can instantiate.
    link: func(s: borrow<store>, req: link-request) -> result<component, link-error>;
}
```

The caller hands the linker (1) a `cov:store` handle so it can fetch components by hash, and (2) a description of what to assemble. The linker returns a single `cov:wasm/runtime.component` ready to instantiate — possibly itself a *composed* component produced via `wasm-compose`-style merging, or a thin wrapper that holds onto the resolved dependency graph and lets the runtime walk it.

### Why the linker is wasm, not host code

- **Pluggable policy.** Different linkers can implement different resolution rules: strict (every import must be satisfied or fail), lazy (resolve on first call), policy-driven (consult an authority for which version of an import to bind), capability-restricted (only let certain components see certain hashes). Each is its own content-addressed artifact you can swap out.
- **Content-addressed reproducibility.** The linker artifact has an O256; "this process was linked by linker `0xABC…`" is a fact you can record alongside the result. Re-linking with the same inputs produces the same output — no host-side drift.
- **Same on every backend.** The native kernel and the browser kernel both load the same linker WASM and run it. No "linker for native, separate linker for browser" code path. Aligns with [[feedback-js-is-executor-only]] and [[browser-kernel-vision]].
- **Produces the "process" artifact** in the [[wasm-process-container]] vocabulary. The linker IS the thing that turns a hash + import bindings into a closed shared-fate graph. Containers (restart policies, supervision) operate on the linker's output, one level up.
- **Naturally caches via the store.** A `(root, imports, policy)` triple has its own O256; the linked result can be cached under that key. Re-link is just a store hit.

### How it composes with the rest of the stack

```
┌─────────────────────────────────────────────────────────┐
│  Kernel + applications        (Rust, mostly as wasm)    │
├─────────────────────────────────────────────────────────┤
│  Linker (wasm artifact)       — assembles processes     │
├─────────────────────────────────────────────────────────┤
│  Component-model interpreter  — lift/lower over the     │
│  (Rust → wasm)                  canonical ABI           │
├─────────────────────────────────────────────────────────┤
│  cov:wasm/runtime trait       — compile/instantiate/    │
│  + cov:store                    call + fetch by hash    │
├─────────────────────────────────────────────────────────┤
│  Low-level executor           — WebAssembly.* (JS) or   │
│                                 wasmtime (native)       │
└─────────────────────────────────────────────────────────┘
```

The bottom layer is engine-specific (wasmtime / `WebAssembly.*`). Every layer above is portable Rust→wasm. The linker sits between the interpreter and the kernel: it produces ready-to-run processes that the kernel and applications then invoke.

### Why not now

The linker depends on the layers below being settled — at minimum, the runtime trait (Phase 0, done), the process abstraction (Phase 5, deferred), and the store WIT (`cov:store@0.1.0`, exists per [[cov-store-wit-shape]]). The component-model interpreter (Phase 3.5) is the most expensive prerequisite; until that lands, jco-as-runtime is the stopgap.

But the architecture is clear enough now to *not paint into a corner.* Specifically:

- Don't put linking knowledge in the kernel. The kernel takes a "ready process" handle from somewhere; the somewhere is the linker eventually, a hand-wired composition today.
- Don't bake an import-resolution scheme into `cov:wasm/runtime`. Keep instantiate single-component for now; multi-component wiring is the linker's job, not the runtime trait's.
- Don't ship the same "what's in the dep graph?" walker twice (once in the build pipeline, once at load time). Both should be the linker, eventually.

See also [[wasm-linker-script]] for the short version of this vision, kept in conversation memory.

---

## 10. Open questions

- **Resource lifetime under wit-bindgen.** Per [`wit-component-gotchas`], exported resources need careful glue. Whether `instance` should be `borrow<instance>` or `own` at every call site needs prototyping.
- **What about `val` variants we don't yet need?** Start with what `covalence-wasm-spec` actually uses; extend lazily. Don't pre-enumerate every component-model type until something needs it.
- **Trap reporting.** A `result<_, string>` is fine for MVP; a richer error type (trap kind, location, backtrace handle) is a Phase-1 polish.
- **Where does the WIT package live?** Workspace `wit/` directory? Inside `crates/covalence-wasm/wit/`? Both have precedent in the BA ecosystem.
- **How does the browser host import map look?** Probably a `dist/components/<o256>.js` convention with a manifest. Defer until Phase 3.

---

## References

- `crates/covalence-wasm/src/engine.rs` — current state (one-line wasmtime re-export)
- `crates/covalence-wasm/src/val.rs` — engine-agnostic `Val` / `ValType`
- `crates/covalence-wasm-spec/tests/common/mod.rs` — the harness pattern this proposal abstracts
- `extensions/covalence-vscode/src/server.ts` — proves `WebAssembly.compile` works in both desktop and web VSCode
- Memories: `wit-component-gotchas`, `wasm-spec-crate-design`, `store-identity-component-hash`, `store-api-portable`
