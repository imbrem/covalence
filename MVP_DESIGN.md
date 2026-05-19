# MVP Design

This document tracks the MVP for `covalence` — an LCF-style theorem prover
based on the Curry-Howard correspondence using WASM components.

The top half describes what we have; the bottom half describes what we still need.

---

## What We Have

### Definitions

- A **blob** is a finite byte sequence with value semantics (equal iff same length + same bytes).

- A **WASM component** is a component-model binary, content-addressed by its BLAKE3 hash.

- A **name** is a `u256` (BLAKE3 digest). Encoding/decoding to blobs is just the 32-byte representation.

- Our hash function is BLAKE3: `H : blob -> name`, with default key `DATA`.

### Content-Addressed Store

- `covalence-hash` provides `O256` — a 256-bit BLAKE3 content hash.
- `covalence-store` provides `ContentStore<K>` trait + `BlobStore<K>` (Arc wrapper), with `MemoryStore` and `SqliteStore` backends.
- Blobs are stored and retrieved by hash. The store is used by the kernel, REPL, REST API, and remote client.

### Proposition Deciding (the WASM engine)

`covalence-wasm` loads, links, and executes WASM components via wasmtime.

A **proposition** is a component that may import `attest()`. A prop is **true**
if one can instantiate it and get it to call `attest()`.

The engine (`WasmEngine::decide()`) works as follows:

1. Load the component, classify all imports:
   - `"attest"` → host function that sets `attested = true`
   - `"blob/{hash}"` → lazy blob from store (traps if unavailable)
   - `"module/{hash}"` → core module from store (categorized but **not yet linked**)
   - `"component-{hash}"` → instance import, resolved recursively from store

2. Static pre-check: no `attest` import AND no component deps → `False`

3. Recursively pre-instantiate all `component-{hash}` deps (cycle detection + instance caching)

4. Instantiate the main component (runs start function)

5. Result:
   - `attested = true` → **True** (even if a trap occurred after attestation)
   - `attested = false` + `attest` was imported → **Unknown**
   - No `attest` import + no deps → **False**

### Kernel

`covalence-kernel` wraps the store and engine with decision caching (True/False sets).
Implements both `SyncBackend` (dyn-compatible) and `AsyncBackend` (async, for the server).

### REPL

`covalence-repl` provides an S-expression REPL (`Session`) backed by any `SyncBackend`:

| Command | Description |
|---|---|
| `(store "data")` | store string as blob, return hash |
| `(store-url "url")` | fetch URL, store as blob |
| `(store-file "path")` | store file as blob (CLI only) |
| `(read <hash>)` | read blob as UTF-8 |
| `(read-wat <hash>)` | decompile blob as WAT |
| `(module ...)` | compile WAT module, store, return hash |
| `(component ...)` | compile WAT component, store, return hash |
| `(parse-module <hash>)` | inspect module imports/exports |
| `(parse-component <hash>)` | inspect component imports/exports |
| `(decide <hash>)` | decide proposition |
| `(status)` | show backend info + blob count |
| `(help)` | list commands |

The CLI REPL (`cov repl`) uses rustyline with ANSI syntax highlighting.

### REST API & Server

`covalence-serve` exposes the kernel over HTTP (axum):

- `POST /api/blobs` — store blob, get hash
- `GET /api/blobs` — blob count
- `GET /api/blobs/{hash}` — retrieve blob
- `HEAD /api/blobs/{hash}` — existence check
- `POST /api/eval` — evaluate S-expression
- `GET /api/repl` — WebSocket REPL session
- `POST /api/wat/module` — compile WAT module
- `POST /api/wat/component` — compile WAT component
- `GET /api/wat/{hash}` — decompile to WAT
- `GET /api/parse/module/{hash}` — module imports/exports
- `GET /api/parse/component/{hash}` — component imports/exports
- `GET /api/decide/{hash}` — decide proposition

Service discovery via `$XDG_RUNTIME_DIR/covalence/registry/`.
Serves both TCP and Unix domain sockets.

### Remote Client

`covalence-client` implements `SyncBackend` over HTTP (TCP or Unix socket),
making the kernel remotable — the REPL can connect to a running `cov serve`.

### LSP

`covalence-lsp` provides diagnostics and formatting for `.smt`, `.smt2`, `.alethe`, `.cov` (S-expression) and `.wat` (WAT) files.

### Cogit (VCS)

Minimal so far: `cov cog hash-blob` hashes files using BLAKE3, SHA-256, or Git SHA-1/SHA-256.

---

## What We Still Need

### 1. Prop/Component Distinction

The current engine treats everything as `component-{hash}` instance imports.
The design calls for a clear separation:

- **Components** may import: blobs, modules, other components
- **Props** may additionally import: `attest()`, other props by `prop/{hash}`
- **Components may NOT import props** — props are a strictly richer category

This means:
- Add `ImportKind::Prop(O256)` alongside the existing `ImportKind::Import`
- Rename `component-{hash}` to `component/{hash}` for consistency with blob/module prefixes
- Enforce that a plain component cannot import `attest()` or `prop/{hash}`
- Inside a prop, a `prop/{hash}` import is wired as a component instance (since inside a prop, imported props look like any other component)

### 2. Blob API (Host Functions)

Props and components should be able to manipulate blobs from inside WASM.
Currently blobs are stored/retrieved but not accessible as a resource type.

We need to expose via the component model:

- **Resource**: `blob` — an opaque, lazily-loaded byte sequence
- **Functions**:
  - `cons(vector<u8>) -> blob` — create a blob
  - `cat(blob, blob) -> blob` — concatenate
  - `eq(blob, blob) -> bool` — equality
  - `length(blob) -> u64` — length
  - `slice(blob, u64, u64) -> vector<u8>` — extract byte range
  - `read(blob) -> vector<u8>` — materialize

### 3. Module Linking

`module/{hash}` imports are categorized but left unlinked.
Need to load core modules from the store and link them into the component.

### 4. Keyed Hashing

BLAKE3 supports keyed hashing and key derivation, which the design uses:
- Default key `DATA` — plain BLAKE3 (this is what we have)
- `K_name(o)` — BLAKE3 keyed hash with key `o` (a name/u256)
- `K_blob(c)` — BLAKE3 key derivation with context `c` (a blob)

These must be distinct (no overlap between key spaces).
`covalence-hash` needs keyed and derive modes.

### 5. Proofs as Components

A **proof** of a prop P is a component that imports P and drives it to call `attest()`.
This makes the proof itself a prop (it imports a prop, making it a prop; but it doesn't call attest directly — only through its import).

This gives us our first **inference rules**:

- If P is a prop, it implies the _disjunction_ of its prop imports
  (where `attest()` is the "true" prop)
- A prop with no prop imports (including `attest()`) is **false**

These are already partially reflected in the engine's True/Unknown/False logic,
but they need to be formalized and made explicit — especially the notion
of "proof" as a first-class object that can be stored, hashed, and referenced.

### 6. Beyond MVP (Future)

- Full cogit VCS — commits, trees, history, content-addressed object graph
- More inference rules and interfaces
- SMT integration
- Type theory / proof terms
- Richer component interfaces
