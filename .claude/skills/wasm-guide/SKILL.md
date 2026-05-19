---
user-invocable: false
description: WASM engine features, proposition deciding, and WASM memory configuration
---

## `covalence-wasm` features

- **Base** (no features) — WAT validation (`validate_wat`), WASM decompilation (`wasm_to_wat`), binary parsing (`parse_module`, `parse_component`). Returns typed `WasmError`. Depends on `wat`, `wasmprinter`, `wasmparser`. Used by `covalence-lsp`, `covalence-repl`, and the VSCode extension (WASM-safe).
- **`runtime`** (non-default) — `WasmEngine` for running WASM components via `wasmtime`. Re-exports `wasmtime` crate. Used by `covalence-kernel[engine]`. Not WASM-compatible (native only).

## Proposition Deciding

A WASM component defines a proposition. `decide` asks: "is the proposition true?"

- Component imports `"attest"` → can call `attest()` to assert truth
- Component imports `"blob/{hash}"` → gets blob data from store (lazy — traps if unavailable)
- Component imports `"module/{hash}"` → core WASM module from store (stub — not yet linked)
- Component imports `"component-{hash}"` → instance import, linked recursively from the store

Instance imports (`component-{hash}`) are resolved eagerly: the dep component is loaded, compiled, and instantiated (with its own deps resolved recursively). All components in a decide tree share one `Store<HostState>`, so if any dep calls `attest()`, the shared flag is set. Instances are cached by hash and cycles are detected.

Result: `PropResult::True` (attest called), `PropResult::Unknown` (attest imported but not called), `PropResult::False` (attest not imported and no deps — statically false).

The `Kernel` caches True and False results across calls (Unknown is not cached).

## WASM Memory

Memory is fixed at 32768 pages (2 GB). This value must match in two places:
- `scripts/build.ts`: linker args `--initial-memory=2147483648 --max-memory=2147483648`
- `src/server.ts`: `wasm.createProcess(... { initial: 32768, maximum: 32768, shared: true })`

Note: because this is shared memory (`SharedArrayBuffer`), the full 2 GB is reserved as virtual address space. On Linux, physical RAM is only committed for pages actually touched (overcommit). On Windows, the full size may count against the system commit charge.
