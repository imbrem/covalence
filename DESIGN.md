# Covalence Kernel: HOL Vision & Architecture

This document describes the long-term vision for the Covalence kernel as a
HOL-based theorem prover and the immediate architectural steps toward that goal.

## 1. HOL Foundation

All kernel facts will eventually be HOL theorems. The kernel's role is to
record **certified facts** about computation — not to trust any particular
runtime, but to verify that a stated relationship holds.

The fact store will work with **local indices** — wrapped i32s acting as
"externrefs" to objects held by the Store and Evaluator. This enables
composition of relations without requiring the kernel to understand the
internal representation of every object.

Example fact (fully spelled out):

```
(relation: wasm-result)
(program:  evaluator-instance 56)
(entry:    function-id 3)
(input:    store-data 21)
(input:    store-data 44)
```

This says: "evaluator instance 56 ran function 3 on store objects 21 and 44,
producing a result described by this relation." The kernel doesn't interpret
the program or data — it records that the evaluator attested to the relation.

The current `sat_set` / `unsat_set` hash caches in the Kernel are a placeholder.
They will be replaced by a proper HOL fact store in a future redesign.

## 2. Kernel Architecture

The kernel is parameterized over two components:

```
Kernel<S, E>
```

- **`S: ContentStore<O256>`** — content-addressed blob store mapping `O256` hashes
  to byte data. The current implementation is `BlobStore<O256>` backed by a
  `SharedMemoryStore`, but any `ContentStore<O256>` works (e.g. `SqliteStore`,
  a future distributed store, or a store composed of multiple backends).

- **`E: Evaluator<S>`** — proposition evaluator. Given raw bytes (a proposition)
  and a reference to the store, produces a `DecideOutput` (decision + transitively
  proved hashes). The MVP evaluator is `WasmEngine`; future evaluators include
  native container engines and remote attestation services.

The **fact store** (decision caches) is internal to the Kernel struct. It is
deliberately not abstracted behind a trait — the current O256-based `HashSet`
caches would be the wrong interface for the future HOL kernel, which works with
local indices rather than content hashes. Abstracting it now would create an API
we'd throw away.

## 3. Execution Hierarchy

Five levels, inner to outer:

### Function
A single exported function within a module. The smallest unit of execution.

### Module
A stateful WASM core module. Traps are fatal to the module — a trap terminates
the module's execution and propagates to its container.

### Component
A WASM component with typed interfaces (the component model). Components
declare imports and exports with rich types. A component may contain one or
more core modules.

### Process
A set of linked components (`link-{hash}`) that share state within a linking
scope. All components in a process trap together — if any component traps,
the entire process is terminated.

### Container
A collection of processes that can be killed and restarted independently.
**Containers nest** — a container can spawn child containers via `prove-{hash}`,
each with isolated state and link scopes.

"Container" is intentionally general — not WASM-specific. Containers are
**untrusted**: they are spawned from a hash, and the only thing we trust is
"this is the container described by that hash." The sandboxing mechanism need
not be WASM: future containers can run native x86 code, Docker images, or any
other isolation technology. The kernel records HOL facts about execution
regardless of runtime.

Covalence is a **"UNIX theorem prover"** — it treats programs as propositions
and execution as proof, across any runtime environment.

## 4. Blob Relations

HOL relations the kernel can derive about blobs and execution:

| Relation | Meaning |
|----------|---------|
| `blob_stored(h)` | Blob with hash `h` is present in the store |
| `attested(h)` | A proposition `h` called `attest()` during execution |
| `proved(h, p)` | Hash `h` was on the prove stack when `p` attested |
| `kv_set(ns, k, v)` | Key `k` was set to value `v` in namespace `ns` |
| `executed(h, result)` | Container for hash `h` produced `result` |
| `container_of(c, p)` | Process `p` runs inside container `c` |
| `nested(c_outer, c_inner)` | Container `c_inner` is nested inside `c_outer` |

These relations form the basis for reasoning about programs. The kernel
records them as HOL facts; higher-level reasoning combines them.

## 5. MVP Scope

### Built now
- `Kernel<S, E>` with default type parameters (`BlobStore<O256>`, `WasmEngine`)
- `Evaluator<S>` trait abstracting the proposition evaluator
- `WasmEngine` implements `Evaluator<BlobStore<O256>>`
- Decision caches stay inline in Kernel (not abstracted)
- All existing consumers unchanged (default type params preserve compatibility)

### Deferred
- HOL fact store replacing `sat_set` / `unsat_set`
- Local index system (wrapped i32 externrefs)
- Container nesting beyond `prove-{hash}`
- Native (non-WASM) container execution
- Multiple store backends composed at runtime
- Remote attestation / distributed proving
