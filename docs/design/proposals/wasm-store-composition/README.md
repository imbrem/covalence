# WASM Store Composition

> **STATUS: SKETCH.** Not committed; this is a roadmap from the
> currently-built skeleton to a fully composable store layer where
> every store — leaf or transformer — is a content-addressed WASM
> component carrying its own manifest.
>
> Sibling to [`../shared-backbone/`](../shared-backbone/) (which
> declares the content-addressed substrate) and
> [`../layered-framework/`](../layered-framework/) (which says stores
> sit *outside* the kernel TCB as oracles). This proposal designs the
> store layer those two leave under-specified.

## 1. The shape

A store is **a WASM component implementing
[`cov:store/api@0.1.0`](../../../../crates/covalence-wasm/wit/store.wit)**.

Its **identity is the content hash of its component binary**:
`store_id = O256::blob(component_bytes)`.

Its **self-description** is a [`StoreManifest`][manifest] —
serialised JSON — **embedded inside that binary** as a
`cov:store/manifest` custom section, so the identity hash pins the
manifest too.

Its **composition is tree-shaped**: a store can delegate to *N*
backing stores (cache → {primary, replica, fallback}, scatter/gather
across shards, fallback chains, signed-overlay over content). The
manifest already shapes for this — `wraps: Vec<StoreRef>` and
`depends_on: Vec<StoreRef>` are lists, not single fields. The WIT
side needs to match: a composer takes a runtime list of upstream
handles, not a fixed-arity import set.

The two declarations live in parallel:

- The **manifest**: `wraps` (dependencies the store is unsound
  without) and `depends_on` (dependencies it can ride out missing).
  Both are lists keyed by content hash.
- The **WIT world**: a composer imports `cov:store/api` to use the
  `store` *resource type*, exports its own `cov:store/api` (a
  freshly-constructed `store`), and exposes a factory:
  ```wit
  build: func(backings: list<store>) -> store;
  ```
  At realisation time the host hands the composer one `store`
  handle per resolved upstream; the composer can dispatch to any
  subset per request.

The two layers are redundant by design: the WIT shape is the runtime
contract, the manifest is the declarative description used by tools
that don't want to (or can't) load the binary.

[manifest]: ../../../../crates/covalence-store/src/metadata.rs

## 2. Why this shape

It mirrors three existing systems that work:

| System            | Identity                  | Self-description           | Composition                       |
|-------------------|---------------------------|----------------------------|-----------------------------------|
| Linux mount       | block device              | superblock (in-FS)         | mount table                       |
| OCI image         | content digest            | image manifest (in-image)  | layer ancestry                    |
| **Covalence store** | `O256(component_bytes)` | embedded custom section    | `wraps` / `depends_on` + WIT imports |

The kernel can address a store the same way it addresses any other
content (one `O256`), recover its topology without a side channel,
and refuse to mount a store whose manifest disagrees with its actual
imports — same way `mount` will refuse a superblock that doesn't
match the device. The "looks like a Linux kernel managing
filesystems" framing the user wants falls out of this directly.

## 3. What is built today

Pieces that exist on `wasm-store-composition`:

- **`cov:store@0.1.0` WIT** — `store` as a resource with `get` /
  `contains` / `head` methods plus an `open()` factory; mirror
  `upstream` interface for the import side; `compose` interface
  with `build(list<store>)` factory; two worlds (`leaf`,
  `composer`).
- **`covalence-json`** — workspace-wide `serde_json` wrapper.
- **`covalence-store::metadata`** — `StoreManifest` / `StoreRef`
  with `wraps` / `depends_on` / opaque `config: Value` and a
  forward-compat `extra` bucket.
- **`covalence-wasm::custom`** — generic `append_custom_section` /
  `find_custom_section` over the WASM custom-section ABI.
- **`covalence-wasm-store`** —
  - `WasmStore`: an `AsyncContentStore<Vec<u8>>` over a wasmtime
    component instance.
  - `embed_manifest` / `extract_manifest`: round-trip a
    `StoreManifest` through the `cov:store/manifest` custom section.
  - `single_blob`: a 60-line WAT example that knows one
    (hash → blob) pair, used as the round-trip exemplar.
- **Identity contract proven by test**: same code + different
  manifest ⇒ different `O256`; same inputs ⇒ same `O256`.

- **`covalence-wasm-store`** — `WasmStore` over a typed wasmtime
  `Store<HostState>`; `from_component_bytes` (leaves) and
  `compose(composer_bytes, backings)` (composers). Linker shims
  register a host-resource type for the upstream and forward
  `contains` to the right backing.
- **`merge` example composer** — Forwards `get`, `contains`, `head`
  across N backings (first-hit wins for `get`/`head`, OR for
  `contains`). Demonstrates host-side resource registration + full
  method forwarding in both canonical-ABI shapes.
- Integration tests `compose_roundtrip.rs` (5 tests) exercise the
  composition end-to-end for `get` / `contains` / `head` plus the
  zero-backings and 3-backings cases.

- **`cov:kv@0.1.0` WIT** — Abstract key-value store mirroring the
  cov:store shape: `kv` resource with `get` / `contains` / `head`
  methods + `open()` factory, mirror `upstream` interface, `compose`
  with `build(list<kv>)`, two worlds (`leaf`, `composer`). Keys are
  `string`; values are `list<u8>`. Smoke-tested via `wit_parser`;
  no host adapter yet (mirrors covalence-wasm-store).

What is *not* yet built:

- WASM-component-backed **kv adapter** (`covalence-wasm-kv` crate).
  Same pattern as covalence-wasm-store: a `WasmKv` wrapping a
  wasmtime component instance, exposing it as
  `covalence_kv::KvStore`. Plus example leaf / composer.
- `StoreRef` carries a `name` (string) and an optional inline
  manifest. **It does not yet carry an `O256` hash**, so a manifest
  cannot canonically point at its dependencies.
- There is no `StoreRegistry`: nothing reads a manifest graph and
  realises it as an `AsyncBlobStore`.
- **Cross-WIT composers** — a `cov:store` composer that also
  *imports* `cov:kv/upstream` for routing decisions (the
  SQLite-routed S3-fetcher pattern). Mechanically straightforward
  once both adapters exist: just register the kv linker shims
  alongside the store ones.
- No write side (`insert` / `put`) on either WIT.

## 4. Roadmap

Four phases. Each ends with the workspace passing `cargo test
--workspace` and a working demo.

### Phase 1 — resource-based WIT + tree composition (**DONE**)

The smallest unit of progress that materially advances the vision:
prove a composer component can take a runtime list of upstream
stores and dispatch to them. All three read operations (`get`,
`contains`, `head`) now forward through composers end to end —
including the import-side return-area canonical ABI for non-flat
returns (`option<list<u8>>`, `option<blob-info>`).

1. **Promote `store` to a resource** — DONE. Read methods now live
   on a resource type. Crucially, the upstream side gets a
   **distinct interface name** (`cov:store/upstream@0.1.0`) — a
   world that both imports and exports `api` would make
   `use api.{store}` ambiguous, so the import side is its own
   interface with the same shape. Final WIT:
   ```wit
   package cov:store@0.1.0;

   interface api {
       resource store {
           get:      func(key: key) -> option<blob>;
           contains: func(key: key) -> bool;
           head:     func(key: key) -> option<blob-info>;
       }
       open: func() -> store;
   }

   /// Mirror of `api` for the upstream side. Same shape, distinct
   /// resource identity — the canonical ABI requires it.
   interface upstream {
       resource store { /* same methods */ }
   }

   interface compose {
       use upstream.{store};
       build: func(backings: list<store>);
   }

   world leaf     { export api; }
   world composer { import upstream; export api; export compose; }
   ```
   `list<store>` makes the **fan-out arbitrary at runtime** — no
   need to ship a new component for "2-way vs. 3-way fallback".
   `build` doesn't return; the composed store is retrieved via
   `api.open()`, which sidesteps the "which interface's `store`?"
   question for the return type.
2. **Update the leaf example** — DONE. `single_blob` exports the
   resource shape (`open()` factory + `[method]store.get` /
   `.contains` / `.head` with handle-as-first-param).
3. **Extend `WasmStore`** — DONE.
   ```rust
   impl WasmStore {
       pub fn from_component_bytes(bytes: &[u8])
           -> Result<Self, WasmStoreError>;
       pub fn compose(composer_bytes: &[u8], backings: Vec<WasmStore>)
           -> Result<Self, WasmStoreError>;
   }
   ```
   Compose wires the composer's `cov:store/upstream` import via
   `Linker::instance(...).resource(...)` (host-resource type
   `BackingHandle`, rep = index into `Vec<WasmStore>`) plus
   `func_new` shims forwarding each method to the right backing.
   Backings are stored in a typed wasmtime `Store<HostState>` so
   linker callbacks can find them.
4. **Second example: `merge` composer** — DONE.
   * `contains` ORs the backings' answers.
   * `get` returns the first backing's `Some(blob)`.
   * `head` returns the first backing's `Some(blob-info)`.
   Each upstream call uses a fresh return-area block allocated via
   the composer's own `cabi_realloc`; results are forwarded into
   our own export return area without copying the underlying bytes.
5. **Integration tests** — DONE. `compose_roundtrip.rs` (5 tests):
   `aggregates_contains`, `forwards_get_first_hit_wins`,
   `forwards_head`, `with_zero_backings_is_empty`, and
   `with_three_backings_routes_correctly` (variable-arity).

**Exit criterion:** met. The resource ABI for `list<store>` factory
invocation, host-resource type registration, and method forwarding
in both directions (flat-fitting return like `bool` and
return-area-via-extra-param like `option<list<u8>>`) are all
exercised end-to-end.

### Phase 2 — Hash-keyed `StoreRef`

Tighten `StoreRef` so manifests can name dependencies *canonically*:

```rust
pub struct StoreRef {
    pub name: String,            // human handle, unchanged
    pub hash: Option<O256>,      // NEW: content hash of the
                                 // referenced store's component
    pub manifest: Option<Box<StoreManifest>>,   // unchanged
    pub extra: BTreeMap<String, Value>,
}
```

The hash field is what lets the registry actually resolve the graph
from a content store. The inline manifest stays for the
"single-document deployment" use case but the hash is the
canonical pointer. Add a `O256`-aware (de)serialiser in
`covalence-store::metadata` (likely "hex" or "base32" of the 32
bytes).

**Exit criterion:** a unit test builds a wrapper component whose
manifest names its upstream by hash, embeds it, then proves
`extract_manifest(...).wraps[0].hash == upstream_hash`.

### Phase 3 — `StoreRegistry`

A live builder that walks the graph:

```rust
pub struct StoreRegistry {
    blobs: AsyncBlobStore<O256>,                    // where component
                                                    // bytes live
    builders: HashMap<String, Arc<dyn KindBuilder>>,// kind -> adapter
    instances: Mutex<HashMap<O256, AsyncBlobStore<Vec<u8>>>>,
}

impl StoreRegistry {
    pub async fn realise(&self, root: O256)
        -> Result<AsyncBlobStore<Vec<u8>>, RegistryError>;
}
```

`realise` fetches `root` from `blobs`, extracts the manifest,
recursively realises every `wraps[i].hash` (must be present) and
each *available* `depends_on[i].hash`, then hands the **complete
list** of upstreams to the right `KindBuilder` for `manifest.kind`.

`kind = "wasm-component"` calls either
`WasmStore::from_component_bytes(bytes)` (when `wraps` is empty) or
`WasmStore::compose(bytes, backings)` (when it isn't). Native kinds
— `"memory"`, `"sqlite"`, `"git-prefix"` — are registered builders
that ignore the component bytes (or read configuration out of
`manifest.config`); they receive the same list of upstreams and
decide how to use it.

Tree resolution is parallel: a composer's children resolve
concurrently (via `futures::try_join_all`) before the composer
itself is built. The `instances` cache keyed by `O256` dedupes
diamond dependencies — the same backing referenced from two
composers is realised once.

`wraps` is required (registry errors if missing); `depends_on` is
best-effort (registry logs and continues, matching the
"unsound vs. tolerable" split the manifest already encodes).

**Exit criterion:** end-to-end test — a deployment ships a
content-store seed with the five component blobs from the worked
example in §5; the registry, given the cache's hash, materialises
the full tree and answers `get` through all four layers.

### Phase 4 — write side + richer errors (deferred)

Add `insert` / `put` to the WIT. Replace `option`-shaped returns
with a `variant store-error` (IO, range-not-satisfiable, write
denied). The host adapter grows matching error decoding; the
single-blob example WAT keeps its current shape since it's read-only.
Single-blob also gains a sister example: an in-memory writable store
(component-allocated bump-heap as the storage).

The deferral is intentional: phases 1–3 unlock composition; the
write side is parallel work that does not block them.

## 5. Worked example: end of phase 3

A deployment wants a four-node store graph:

```
              cache (LRU)
                  │
                  └── wraps ──> scatter
                                 │
              ┌──────────────────┼──────────────────┐
              ▼                  ▼                  ▼
        primary (HTTP)      replica (HTTP)     fallback (embedded)
```

`cache` is a single-upstream wrapper (one entry in `wraps`).
`scatter` is a **tree node** — its `wraps` lists three children, all
required for soundness. (A `multi-tier` composer with one `wraps` +
two `depends_on` is a separate shape; the registry distinguishes by
which list each child sits in.)

Each store ships as a WASM component with an embedded manifest:

```
primary_id   = O256(primary_component_bytes)
replica_id   = O256(replica_component_bytes)
fallback_id  = O256(fallback_component_bytes)   // "single-blob" leaf
scatter_id   = O256(scatter_component_bytes)    // composer
cache_id     = O256(cache_component_bytes)      // composer with N=1
```

The scatter node's manifest:

```json
{
  "name": "scatter",
  "kind": "wasm-component",
  "wraps": [
    { "name": "primary",  "hash": "<primary_id>"  },
    { "name": "replica",  "hash": "<replica_id>"  },
    { "name": "fallback", "hash": "<fallback_id>" }
  ],
  "config": { "policy": "first-hit" }
}
```

The cache's manifest names `scatter` as its sole `wraps` entry.

The deployment ships one content-store seed (the five component
binaries) and one root hash (`cache_id`). The registry:

1. Fetches `cache_id` → cache bytes → extracts cache manifest.
2. Sees `wraps[0].hash = scatter_id`; recurses.
3. Fetches `scatter_id` → manifest names three children.
4. Recurses on each child in parallel; each resolves to a
   `WasmStore`.
5. Calls `WasmStore::compose(scatter_bytes, vec![primary, replica,
   fallback])` — the scatter composer's `build` call receives three
   `store` handles, returns the composed `store`.
6. Calls `WasmStore::compose(cache_bytes, vec![scatter])` — cache
   wraps the composed scatter as its single backing.
7. Hands the resulting `AsyncBlobStore<Vec<u8>>` to the kernel.

Adding a fourth replica is a metadata-only change to `scatter`'s
manifest + shipping the new replica's component bytes. The composer
WASM does not change. The new `scatter_id` propagates through
`cache`'s manifest (since `wraps[0].hash` now differs), giving
`cache` a new identity hash too — same way an OCI image gets a new
digest when any of its layers change.

## 6. Open questions

- **Key type at the WIT.** Today `key = list<u8>`. Tightening to a
  fixed-width record (`record key { bytes: tuple<u8;32> }`) would
  pin O256 at the WIT layer at the cost of generality. Defer until a
  non-32-byte key shape lands.
- **Resource handle ownership across compose chains.** The composer's
  `build` takes `list<store>` by-value, so backing handles transfer
  ownership into the composer's ResourceTable. Re-using a backing
  under two parents (a diamond in the graph) therefore needs the
  registry to instantiate the backing component once per consumer
  *unless* we add an explicit `clone` method on `store`. Decide in
  phase 1: per-consumer instantiation is simpler and matches the
  "store identity = component hash" contract; explicit `clone` is a
  bigger ABI commitment.
- **Linker scope across compose chains.** Is one wasmtime `Store<()>`
  per resolved root the right granularity, or one per component?
  Affects parallel-call throughput. Decide in phase 1 against
  measurements.
- **Manifest schema versioning.** `cov:store@0.1.0` pins the WIT;
  the manifest is implicitly versioned via the `cov:store/manifest`
  custom-section name. Future schema breaks bump the section name
  (`cov:store/manifest@2`). The `extra` bucket on `StoreManifest`
  buys forward-compat for additive changes.
- **Cycle detection in the registry.** A malicious or buggy manifest
  could declare `cache.wraps = [cache]`. The realiser needs a
  visited set keyed on `O256`. Trivial to add but worth saying
  explicitly.

## 7. Integration with `wasm-runtime`: store = container, not process

A `cov:store/api` store is a **container** in the
[`wasm-runtime`](../wasm-runtime/) sense, not a process. The
distinction matters and recalibrates several decisions:

- **External ABI**: `cov:store/api` (get / contains / head / open).
- **Internal shape**: a supervised *tree of processes*, each its
  own shared-fate component graph. Restart policies, resource
  ceilings, and trap handling are container-level concerns the
  store inherits.

The store's container is the unit that abstracts over the
*executor* — what is actually running each internal process. A
single store graph can mix:

- a WASM composer (`single_blob`, `merge`, `s3_path`),
- a Docker-wrapped real S3 client (e.g. written in Go),
- a Kubernetes-resident remote fetcher,
- a host-side adapter (the `BlobSource` trait — see
  `covalence-wasm-store::lib`),
- … and treat them uniformly behind the store ABI.

This is the load-bearing reason to lean on containers, not
processes, for stores. Stores are long-lived services, not
one-shot executions, so they need supervision; and the only way
to abstract over heterogeneous executors (WASM, Docker, native
binary, remote HTTP) is at the container layer.

### Implications for this proposal

1. **`covalence-wasm-store` is one executor implementation**,
   alongside future `covalence-docker-store` /
   `covalence-http-store` / etc. The `BlobSource` trait is the
   executor-agnostic seam on the Rust side; `cov:store/api` is
   the executor-agnostic seam on the WIT side. Both stay
   unchanged when the second executor lands.
2. **`StoreManifest`'s `wraps` / `depends_on` are
   supervision-tree edges.** When container restart policies
   materialise in `cov:wasm/*`, these become concrete policy
   choices: `wraps` ≈ OTP `permanent` (rebuild on failure;
   store is unsound without this child), `depends_on` ≈
   `transient` (log and continue, optional fallback).
3. **Identity is unchanged**:
   `O256(container_bytes_including_manifest)`. Recursive — the
   manifest names its child containers by hash; each child may
   itself be a container.
4. **Don't migrate `WasmStore::compose` onto `cov:wasm/runtime`
   until the runtime's *container* layer is real.** Riding only
   on the process layer would lose supervision and executor
   heterogeneity, which is a regression for stores
   specifically. The bare runtime swap (process-equivalent) is
   only worth doing standalone if it gains us browser parity
   meanwhile and the migration is mechanical.

## 8. Cross-references

- [`crates/covalence-wasm/wit/store.wit`](../../../../crates/covalence-wasm/wit/store.wit) — current WIT.
- [`crates/covalence-wasm-store/`](../../../../crates/covalence-wasm-store/) — current implementation.
- [`crates/covalence-store/src/metadata.rs`](../../../../crates/covalence-store/src/metadata.rs) — manifest schema.
- [`../shared-backbone/`](../shared-backbone/) — the substrate this
  store layer rides on.
- [`../layered-framework/`](../layered-framework/) — places stores
  outside the TCB; this proposal is one realisation of that.
