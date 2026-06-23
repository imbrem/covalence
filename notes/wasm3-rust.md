# WebAssembly 3.0 in Rust — state of play (early 2026)

Research note backing the async decision in [`web-kernel.md`](./web-kernel.md).
Verified against primary sources (linked inline). Dates/versions move fast —
re-check against release notes before relying on exact numbers.

## TL;DR

| Capability | Status today | Notes |
|---|---|---|
| **Wasm 3.0 spec finalized** | ✅ **2025-09-17** | [webassembly.org](https://webassembly.org/news/2025-09-17-wasm-3.0/) |
| Browsers run Wasm 3.0 | ✅ mostly shipping | GC, EH, tail calls, memory64, multi-memory, relaxed-SIMD baseline in major browsers |
| rustc default wasm features | ✅ on `wasm32-unknown-unknown` | `reference-types`+`multivalue` (1.82), `bulk-memory`+`nontrapping-fptoint` (1.87), `mutable-globals`, `sign-ext` |
| SIMD `+simd128` | ✅ opt-in | not default |
| Threads/atomics | ✅ usable | `wasm32-wasip1-threads` or `+atomics`+shared memory — the mature path |
| Tail calls `+tail-call` | ✅ feature stabilized | source-level `become` still nightly |
| Exception handling `+exception-handling` | ⚠️ feature stabilized; Rust `panic=unwind` partial | mostly wired on Emscripten |
| memory64 / `wasm64-unknown-unknown` | ⚠️ Tier 3, experimental | compiles, rough, not production |
| **Rust → WasmGC** | ❌ **no** | Rust uses linear memory; `+gc` is for GC'd source langs |
| **JSPI in browsers** | ✅ Chrome/Edge 137+ default; ⚠️ Firefox 139 flag; ❌ Safari uncommitted | **not cross-browser baseline** |
| **JSPI from wasm-bindgen** | ⚠️ via JS-side `WebAssembly.Suspending`/`promising` | native `#[wasm_bindgen(jspi)]` open since 2023 ([#3633](https://github.com/rustwasm/wasm-bindgen/issues/3633)) |
| wasmtime Wasm 3.0 | ✅ GC/EH/tail-call/multi-mem/memory64/relaxed-simd/func-refs/extended-const default-on | stack-switching WIP; threads off by default |

## What Wasm 3.0 bundles

Finalized **2025-09-17** ([announcement](https://webassembly.org/news/2025-09-17-wasm-3.0/)): 64-bit address space (**memory64**), **multiple memories**, **garbage collection** (WasmGC struct/array heap types), **typed function references**, **tail calls**, **exception handling** (exnref/tags), **relaxed SIMD**, a **deterministic profile**, plus **custom annotation syntax** and **JS String Builtins**.

**Stack switching / typed continuations is _not_ in core 3.0** — it's an adjacent, in-flight proposal ([WebAssembly/stack-switching](https://github.com/WebAssembly/stack-switching)). **JSPI** is the JS-facing relative that actually shipped.

## JSPI (JS Promise Integration)

Lets *synchronous, sequential* Wasm call async Promise-returning JS: the engine **suspends** the whole Wasm stack (fiber-style, no binary instrumentation) when a Promise is returned and **resumes** on resolve — the call looks synchronous to the guest ([Chrome blog](https://developer.chrome.com/blog/webassembly-jspi-origin-trial), [V8 blog](https://v8.dev/blog/jspi)). Wired with `WebAssembly.promising` (export → Promise) + `WebAssembly.Suspending` (async import).

So **yes**, JSPI can do async `fetch` from a sync-looking guest **with no futures rewrite** — but only where it's available: **Chrome/Edge 137+** default, **Firefox 139** behind a flag, **Safari uncommitted**. From Rust there's no stable wasm-bindgen attribute; you hand-wire the JS wrappers ([walkthrough](https://www.dgendill.com/posts/technology/2025-10-01-web-assembly-javascript-promise-integration.html)).

## Rust targets & features

| Target | Tier | Purpose |
|---|---|---|
| `wasm32-unknown-unknown` | 2 | web/embedding; wasm-bindgen default |
| `wasm32-wasip1` / `wasm32-wasip1-threads` | 2 | WASI 0.1 (+threads) |
| `wasm32-wasip2` | 2 (since 1.82) | WASI 0.2 / Component Model |
| `wasm32v1-none` | 2 | strict Core 1.0 / MVP, no post-1.0 proposals |
| `wasm64-unknown-unknown` | 3 | memory64, experimental |

Default-feature shift caused real breakage: rustc **1.82** turned on `reference-types`+`multivalue`, changing the `call_indirect` encoding so **older Safari / older `wasm-opt` could not decode the output** ([Rust blog](https://blog.rust-lang.org/2024/09/24/webassembly-targets-change-in-default-target-features/)). Worth remembering for the build pipeline (`wasm-opt` version, target-feature pinning).

**Rust → WasmGC: no.** rustc/LLVM lower Rust to linear memory + malloc/free; WasmGC heap types don't map onto that ([V8](https://v8.dev/blog/wasm-gc-porting)). `+gc` is for Java/Kotlin/Dart/OCaml-style languages.

**Async from wasm-bindgen today:** `async fn` ⇄ JS `Promise` via **`wasm-bindgen-futures`** (`JsFuture` wraps a Promise as a Rust `Future`; `future_to_promise` exposes a Rust future as a Promise) — the stable, production path. Requires the guest to actually be future-based.

## wasmtime (native)

Full Wasm 3.0 set on by default ([proposals matrix](https://docs.wasmtime.dev/stability-wasm-proposals.html)): GC, EH, tail-call, multi-memory, memory64, relaxed-simd, function-references, extended-const. Threads supported but off by default; stack-switching WIP (x86_64 Linux only). Good news for the native `covalence-wasm`/wasmtime path.

## Implications for Covalence

The question that started this: *can we keep the proof engine synchronous and still load article dependencies over the network in the browser?*

1. **Our engine is already async.** `covalence_hol::script::run_async` takes a resolver returning `Import` **futures**; `#import` `await`s them. The "async colors the whole call graph" cost that pushes people toward JSPI is **largely pre-paid** here.

2. **category.wiki is open-web** → must work in Safari. JSPI does not (Chromium-only, Safari uncommitted), and has no stable Rust support. So JSPI **cannot be the baseline.**

3. **Rust can't use WasmGC**, and we don't need memory64/multi-memory/EH/tail-calls for the kernel — so the 3.0 headline features are mostly irrelevant to the browser kernel. The features we *do* rely on (`reference-types`, `bulk-memory`, etc.) are already default-on; threads (if ever needed for parallel verification) are the mature `wasm32-wasip1-threads` path.

**Decision:** baseline = **option (a), futures + `wasm-bindgen-futures`** — expose `check` as a JS `Promise`, drive `run_async` on the event loop, resolver = async JS `fetch`. Portable to every browser, and cheap for us because the engine is already future-based. **JSPI is a deferred Chromium-only fast-path** (feature-detect `'Suspending' in WebAssembly`) for contexts we control (Electron / VSCode-web on Chromium), where it would let the *native-shaped sync* path run in-browser unchanged. **Asyncify is rejected** (code-size/perf tax; superseded by JSPI).

## Caveats (from the research, unverified)

- JSPI "phase 4" + Chrome-137-default rests on V8/Chrome blogs + 2026 roundups, not the W3C phase doc or MDN BCD (the `WebAssembly.Suspending` MDN page 404'd at time of research). Firefox "flag vs shipped" in early 2026 is ambiguous.
- EH "stabilized mid-2025" and tail-call feature-stabilization dates come from Rust PRs/blogs, not a single release-notes line — glance at 1.82–1.90 notes if exact versions matter.
- wasm-bindgen `jspi` attribute confirmed *proposed/unresolved*; a very recent experimental landing wasn't exhaustively ruled out.
