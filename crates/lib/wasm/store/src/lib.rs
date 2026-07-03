//! Host-side adapter: present a wasmtime component instance that
//! implements `cov:store/api@0.1.0` as an [`AsyncContentStore`].
//!
//! The WIT trait is sync from the guest's perspective; the Rust
//! adapter wraps each call in an `async fn` so the same trait
//! ([`AsyncContentStore`]) is satisfied by both WASM-backed and
//! native backends. wasmtime is invoked synchronously inside the
//! adapter — fine for in-memory components; for backends that block
//! on I/O the call site should already be moving execution to a
//! dedicated thread (e.g. via `spawn_blocking`).
//!
//! Key type is `Vec<u8>`: the WIT-level `key = list<u8>` makes no
//! commitment to a fixed hash width. Callers that work in `O256` can
//! convert at the boundary.
//!
//! See [`single_blob`] for the example component that knows exactly
//! one (hash → blob) pair and rejects everything else.

#![forbid(unsafe_code)]

use std::sync::{Arc, Mutex};

use async_trait::async_trait;
use bytes::Bytes;
use covalence_store::{AsyncContentStore, BlobInfo, StoreError, StoreManifest};
use covalence_wasm::engine::wasmtime::{
    Engine, Store,
    component::{Component, ComponentExportIndex, Func, Linker, Resource, ResourceType, Val},
};

pub mod manifest;
pub mod merge;
pub mod s3_path;
pub mod single_blob;

pub use manifest::{ManifestError, STORE_MANIFEST_SECTION, embed_manifest, extract_manifest};

/// Errors from constructing a [`WasmStore`].
#[derive(Debug, thiserror::Error)]
pub enum WasmStoreError {
    #[error("wasmtime engine: {0}")]
    Engine(String),
    #[error("component decode: {0}")]
    Component(String),
    #[error("instantiate: {0}")]
    Instantiate(String),
    #[error("missing export instance `{0}`")]
    MissingApi(&'static str),
    #[error("missing export `{0}` in {1}")]
    MissingExport(&'static str, &'static str),
    #[error("manifest: {0}")]
    Manifest(#[from] ManifestError),
}

/// Name of the WIT interface (`cov:store/api@0.1.0`) the component
/// must export.
pub const STORE_API: &str = "cov:store/api@0.1.0";

/// Abstract blob source — anything that can answer the three
/// resource methods of `cov:store/api.store` synchronously.
///
/// Composer linker shims call into this trait to dispatch upstream
/// `get` / `contains` / `head` requests; both `WasmStore` itself
/// and host-side adapters (an S3-backed KV, a memory dict, …)
/// implement it the same way. Anything passed to
/// [`WasmStore::compose`] is type-erased to `Arc<dyn BlobSource>`.
///
/// Sync because the wasmtime linker context is sync — async
/// callers stand up a blocking adapter (a `tokio::runtime::Handle`
/// + `block_on`) inside their impl.
pub trait BlobSource: Send + Sync {
    /// Fetch the full value for `key`. `None` ≡ absent.
    fn blob_get(&self, key: &[u8]) -> Result<Option<Vec<u8>>, StoreError>;

    /// Existence probe.
    fn blob_contains(&self, key: &[u8]) -> Result<bool, StoreError>;

    /// Cheap metadata probe. `None` ≡ absent.
    fn blob_head(&self, key: &[u8]) -> Result<Option<BlobInfo>, StoreError>;
}

impl BlobSource for WasmStore {
    fn blob_get(&self, key: &[u8]) -> Result<Option<Vec<u8>>, StoreError> {
        self.sync_get(key)
    }
    fn blob_contains(&self, key: &[u8]) -> Result<bool, StoreError> {
        self.sync_contains(key)
    }
    fn blob_head(&self, key: &[u8]) -> Result<Option<BlobInfo>, StoreError> {
        self.sync_head(key)
    }
}

impl From<WasmStore> for Arc<dyn BlobSource> {
    fn from(ws: WasmStore) -> Self {
        Arc::new(ws)
    }
}

/// A content store backed by a wasmtime component implementing
/// `cov:store/api@0.1.0`.
///
/// Cheap to `clone` — internal state is `Arc<Mutex<_>>`-shared, so
/// clones contend on the same wasmtime store. For multi-reader use
/// instantiate one `WasmStore` per worker.
///
/// If the component carries a [`STORE_MANIFEST_SECTION`] custom
/// section, the parsed [`StoreManifest`] is cached at construction
/// and accessible via [`WasmStore::manifest`]. Together with the
/// component's content hash this gives a stable, self-describing
/// store identity.
#[derive(Clone)]
pub struct WasmStore {
    inner: Arc<Mutex<Inner>>,
    manifest: Option<Arc<StoreManifest>>,
}

/// Data carried by every wasmtime `Store` we create.
///
/// Leaves get `backings = Vec::new()`; composers store one
/// `Arc<dyn BlobSource>` per backing so the linker shims can
/// forward imported `cov:store/api` calls into the right upstream
/// regardless of whether it's another `WasmStore` or a host-side
/// adapter (S3 kv, in-memory dict, …). A "Backing" host-side
/// resource type then wraps a `u32` index into this vector — the
/// `rep` value is the index.
pub struct HostState {
    backings: Vec<Arc<dyn BlobSource>>,
}

impl HostState {
    fn new() -> Self {
        Self {
            backings: Vec::new(),
        }
    }
    fn with_backings(backings: Vec<Arc<dyn BlobSource>>) -> Self {
        Self { backings }
    }
}

/// Empty marker type used as the host-resource type identifier for
/// upstream stores in composer wirings. The rep value carried by
/// each handle is the index into [`HostState::backings`].
struct BackingHandle;

struct Inner {
    store: Store<HostState>,
    get_func: Func,
    contains_func: Func,
    head_func: Func,
    /// `Val::Resource` handle obtained from the component's
    /// `cov:store/api.open()` factory. Methods receive this as their
    /// first argument (self).
    handle: Val,
}

impl WasmStore {
    /// Build a store from raw component bytes.
    ///
    /// Validates the component, instantiates it, and looks up the
    /// three required exports (`get`, `contains`, `head`) inside the
    /// `cov:store/api@0.1.0` interface.
    pub fn from_component_bytes(bytes: &[u8]) -> Result<Self, WasmStoreError> {
        let engine = default_engine()?;
        Self::from_component_bytes_with_engine(&engine, bytes)
    }

    /// Same as [`from_component_bytes`](Self::from_component_bytes)
    /// but reusing a caller-provided engine — useful when sharing one
    /// engine across many components.
    pub fn from_component_bytes_with_engine(
        engine: &Engine,
        bytes: &[u8],
    ) -> Result<Self, WasmStoreError> {
        let component = Component::from_binary(engine, bytes)
            .map_err(|e| WasmStoreError::Component(e.to_string()))?;
        let mut linker = Linker::<HostState>::new(engine);
        linker
            .define_unknown_imports_as_traps(&component)
            .map_err(|e| WasmStoreError::Instantiate(e.to_string()))?;
        let mut store = Store::new(engine, HostState::new());
        let instance = linker
            .instantiate(&mut store, &component)
            .map_err(|e| WasmStoreError::Instantiate(e.to_string()))?;

        let api_idx: ComponentExportIndex = instance
            .get_export_index(&mut store, None, STORE_API)
            .ok_or(WasmStoreError::MissingApi(STORE_API))?;

        let open_func = lookup(&mut store, &instance, &api_idx, "open")?;
        let get_func = lookup(&mut store, &instance, &api_idx, "[method]store.get")?;
        let contains_func = lookup(&mut store, &instance, &api_idx, "[method]store.contains")?;
        let head_func = lookup(&mut store, &instance, &api_idx, "[method]store.head")?;

        // Open the store. For a leaf, returns the singleton; for a
        // composer, returns the store last built by `compose.build`
        // (so the caller is expected to invoke `build` first).
        let mut handle_out = [Val::Bool(false)];
        open_func
            .call(&mut store, &[], &mut handle_out)
            .map_err(|e| WasmStoreError::Instantiate(format!("open(): {e}")))?;
        let handle = std::mem::replace(&mut handle_out[0], Val::Bool(false));
        if !matches!(handle, Val::Resource(_)) {
            return Err(WasmStoreError::Instantiate(format!(
                "open() returned {handle:?}, expected resource",
            )));
        }

        let manifest = extract_manifest(bytes)?.map(Arc::new);

        Ok(Self {
            inner: Arc::new(Mutex::new(Inner {
                store,
                get_func,
                contains_func,
                head_func,
                handle,
            })),
            manifest,
        })
    }

    /// Self-description embedded in the component's
    /// `cov:store/manifest` custom section, if any.
    pub fn manifest(&self) -> Option<&StoreManifest> {
        self.manifest.as_deref()
    }

    /// Sync read: full blob, `None` ≡ absent. Used by composer
    /// linker shims (synchronous wasmtime contexts can't `.await`).
    pub fn sync_get(&self, key: &[u8]) -> Result<Option<Vec<u8>>, StoreError> {
        let mut inner = self.inner.lock().expect("WasmStore mutex poisoned");
        let Inner {
            store,
            get_func,
            handle,
            ..
        } = &mut *inner;
        let args = [handle.clone(), key_val(key)];
        let mut results = [Val::Bool(false)];
        get_func
            .call(&mut *store, &args, &mut results)
            .map_err(|e| StoreError::Io(format!("wasm sync_get: {e}")))?;
        match &results[0] {
            Val::Option(Some(inner)) => list_to_vec(inner)
                .map(Some)
                .ok_or_else(|| StoreError::Io("wasm sync_get: expected list<u8>".into())),
            Val::Option(None) => Ok(None),
            other => Err(StoreError::Io(format!(
                "wasm sync_get: expected option<list<u8>>, got {other:?}"
            ))),
        }
    }

    /// Sync probe: blob metadata, `None` ≡ absent.
    pub fn sync_head(&self, key: &[u8]) -> Result<Option<BlobInfo>, StoreError> {
        let mut inner = self.inner.lock().expect("WasmStore mutex poisoned");
        let Inner {
            store,
            head_func,
            handle,
            ..
        } = &mut *inner;
        let args = [handle.clone(), key_val(key)];
        let mut results = [Val::Bool(false)];
        head_func
            .call(&mut *store, &args, &mut results)
            .map_err(|e| StoreError::Io(format!("wasm sync_head: {e}")))?;
        match &results[0] {
            Val::Option(Some(rec)) => match &**rec {
                Val::Record(fields) => fields
                    .iter()
                    .find(|(n, _)| n == "size")
                    .and_then(|(_, v)| match v {
                        Val::U64(n) => Some(*n),
                        _ => None,
                    })
                    .map(|size| Some(BlobInfo { size }))
                    .ok_or_else(|| {
                        StoreError::Io("wasm sync_head: missing record field `size`".into())
                    }),
                other => Err(StoreError::Io(format!(
                    "wasm sync_head: expected record, got {other:?}"
                ))),
            },
            Val::Option(None) => Ok(None),
            other => Err(StoreError::Io(format!(
                "wasm sync_head: expected option<blob-info>, got {other:?}"
            ))),
        }
    }

    /// Sync probe: forward `contains` to this store. Used by composer
    /// linker shims (which run inside a synchronous wasmtime call
    /// context and so can't `.await`).
    pub fn sync_contains(&self, key: &[u8]) -> Result<bool, StoreError> {
        let mut inner = self.inner.lock().expect("WasmStore mutex poisoned");
        let Inner {
            store,
            contains_func,
            handle,
            ..
        } = &mut *inner;
        let args = [handle.clone(), key_val(key)];
        let mut results = [Val::Bool(false)];
        contains_func
            .call(&mut *store, &args, &mut results)
            .map_err(|e| StoreError::Io(format!("wasm contains: {e}")))?;
        match results[0] {
            Val::Bool(b) => Ok(b),
            ref other => Err(StoreError::Io(format!(
                "wasm contains: expected bool, got {other:?}"
            ))),
        }
    }

    /// Compose a store out of N backings using a composer component.
    ///
    /// The composer must target the `composer` world from
    /// `cov:store@0.1.0`: imports `cov:store/api` (consumed for the
    /// upstream stores) and exports `cov:store/api` + `cov:store/compose`
    /// (its own composed store and the `build` factory).
    ///
    /// On instantiation this:
    /// 1. Registers a host-side `store` resource type for the
    ///    composer's imports, with `rep = index into backings`.
    /// 2. Installs Linker shims for `[method]store.{get,contains,head}`
    ///    that forward to the corresponding backing.
    /// 3. Calls `compose.build(backings)` once with a handle per
    ///    upstream — ownership of the backings transfers to the
    ///    composer's resource table.
    /// 4. Calls `api.open()` to retrieve the composed store handle.
    ///
    /// Backings can themselves be composers; the resulting WasmStore
    /// is just another `AsyncContentStore<Vec<u8>>`.
    pub fn compose<I>(composer_bytes: &[u8], backings: I) -> Result<Self, WasmStoreError>
    where
        I: IntoIterator,
        I::Item: Into<Arc<dyn BlobSource>>,
    {
        let engine = default_engine()?;
        Self::compose_with_engine(&engine, composer_bytes, backings)
    }

    /// Like [`compose`](Self::compose) but reusing a caller-provided engine.
    pub fn compose_with_engine<I>(
        engine: &Engine,
        composer_bytes: &[u8],
        backings: I,
    ) -> Result<Self, WasmStoreError>
    where
        I: IntoIterator,
        I::Item: Into<Arc<dyn BlobSource>>,
    {
        let backings: Vec<Arc<dyn BlobSource>> = backings.into_iter().map(Into::into).collect();
        let component = Component::from_binary(engine, composer_bytes)
            .map_err(|e| WasmStoreError::Component(e.to_string()))?;
        let mut linker = Linker::<HostState>::new(engine);

        // Wire the imported `cov:store/upstream` with a host-side
        // `store` resource type and method shims that forward each
        // call into the backing identified by the handle's rep.
        {
            let mut upstream = linker
                .instance(UPSTREAM_API)
                .map_err(|e| WasmStoreError::Instantiate(e.to_string()))?;
            upstream
                .resource(
                    "store",
                    ResourceType::host::<BackingHandle>(),
                    |_, _| Ok(()),
                )
                .map_err(|e| WasmStoreError::Instantiate(e.to_string()))?;

            // contains(self, key) -> bool. Forwards to backing[rep].
            upstream
                .func_new("[method]store.contains", |mut cx, _ty, params, results| {
                    let rep = backing_rep(params.first(), &mut cx)?;
                    let key = list_to_vec(&params[1])
                        .ok_or_else(|| wasmtime_err("contains: expected list<u8> key"))?;
                    let backing = cx
                        .data()
                        .backings
                        .get(rep as usize)
                        .ok_or_else(|| wasmtime_err("contains: rep out of range"))?
                        .clone();
                    // Release the borrow before calling back into wasm.
                    drop(cx);
                    let r = backing
                        .blob_contains(&key)
                        .map_err(|e| wasmtime_err(&format!("upstream contains: {e}")))?;
                    results[0] = Val::Bool(r);
                    Ok(())
                })
                .map_err(|e| WasmStoreError::Instantiate(e.to_string()))?;

            // get(self, key) -> option<list<u8>>. Forwards to backing[rep].
            upstream
                .func_new("[method]store.get", |mut cx, _ty, params, results| {
                    let rep = backing_rep(params.first(), &mut cx)?;
                    let key = list_to_vec(&params[1])
                        .ok_or_else(|| wasmtime_err("get: expected list<u8> key"))?;
                    let backing = cx
                        .data()
                        .backings
                        .get(rep as usize)
                        .ok_or_else(|| wasmtime_err("get: rep out of range"))?
                        .clone();
                    drop(cx);
                    let r = backing
                        .blob_get(&key)
                        .map_err(|e| wasmtime_err(&format!("upstream get: {e}")))?;
                    results[0] = match r {
                        Some(bytes) => Val::Option(Some(Box::new(Val::List(
                            bytes.into_iter().map(Val::U8).collect(),
                        )))),
                        None => Val::Option(None),
                    };
                    Ok(())
                })
                .map_err(|e| WasmStoreError::Instantiate(e.to_string()))?;

            // head(self, key) -> option<blob-info>. Forwards to backing[rep].
            upstream
                .func_new("[method]store.head", |mut cx, _ty, params, results| {
                    let rep = backing_rep(params.first(), &mut cx)?;
                    let key = list_to_vec(&params[1])
                        .ok_or_else(|| wasmtime_err("head: expected list<u8> key"))?;
                    let backing = cx
                        .data()
                        .backings
                        .get(rep as usize)
                        .ok_or_else(|| wasmtime_err("head: rep out of range"))?
                        .clone();
                    drop(cx);
                    let r = backing
                        .blob_head(&key)
                        .map_err(|e| wasmtime_err(&format!("upstream head: {e}")))?;
                    results[0] = match r {
                        Some(info) => Val::Option(Some(Box::new(Val::Record(vec![(
                            "size".to_string(),
                            Val::U64(info.size),
                        )])))),
                        None => Val::Option(None),
                    };
                    Ok(())
                })
                .map_err(|e| WasmStoreError::Instantiate(e.to_string()))?;
        }

        let backings_count = backings.len();
        let mut store = Store::new(engine, HostState::with_backings(backings));
        let instance = linker
            .instantiate(&mut store, &component)
            .map_err(|e| WasmStoreError::Instantiate(e.to_string()))?;

        let api_idx = instance
            .get_export_index(&mut store, None, STORE_API)
            .ok_or(WasmStoreError::MissingApi(STORE_API))?;
        let compose_idx = instance
            .get_export_index(&mut store, None, COMPOSE_API)
            .ok_or(WasmStoreError::MissingApi(COMPOSE_API))?;

        let build_func = {
            let idx = instance
                .get_export_index(&mut store, Some(&compose_idx), "build")
                .ok_or(WasmStoreError::MissingExport("build", COMPOSE_API))?;
            instance
                .get_func(&mut store, &idx)
                .ok_or(WasmStoreError::MissingExport("build", COMPOSE_API))?
        };

        // Materialise one host-owned Resource<BackingHandle> per
        // backing; rep = index. Convert to Val::Resource for `build`.
        let mut backing_vals = Vec::with_capacity(backings_count);
        for i in 0..backings_count {
            let resource = Resource::<BackingHandle>::new_own(i as u32);
            let any = resource
                .try_into_resource_any(&mut store)
                .map_err(|e| WasmStoreError::Instantiate(format!("backing handle: {e}")))?;
            backing_vals.push(Val::Resource(any));
        }
        build_func
            .call(&mut store, &[Val::List(backing_vals)], &mut [])
            .map_err(|e| WasmStoreError::Instantiate(format!("compose.build: {e}")))?;

        // Now extract the composed `store` handle and the method funcs.
        let open_func = lookup(&mut store, &instance, &api_idx, "open")?;
        let get_func = lookup(&mut store, &instance, &api_idx, "[method]store.get")?;
        let contains_func = lookup(&mut store, &instance, &api_idx, "[method]store.contains")?;
        let head_func = lookup(&mut store, &instance, &api_idx, "[method]store.head")?;

        let mut handle_out = [Val::Bool(false)];
        open_func
            .call(&mut store, &[], &mut handle_out)
            .map_err(|e| WasmStoreError::Instantiate(format!("compose open(): {e}")))?;
        let handle = std::mem::replace(&mut handle_out[0], Val::Bool(false));

        let manifest = extract_manifest(composer_bytes)?.map(Arc::new);

        Ok(Self {
            inner: Arc::new(Mutex::new(Inner {
                store,
                get_func,
                contains_func,
                head_func,
                handle,
            })),
            manifest,
        })
    }
}

/// Interface name of the composer factory.
pub const COMPOSE_API: &str = "cov:store/compose@0.1.0";

/// Interface name of the upstream side (imported by composers).
pub const UPSTREAM_API: &str = "cov:store/upstream@0.1.0";

fn wasmtime_err(msg: &str) -> covalence_wasm::engine::wasmtime::Error {
    covalence_wasm::engine::wasmtime::Error::msg(msg.to_string())
}

fn backing_rep(
    val: Option<&Val>,
    cx: &mut covalence_wasm::engine::wasmtime::StoreContextMut<'_, HostState>,
) -> Result<u32, covalence_wasm::engine::wasmtime::Error> {
    let Val::Resource(any) = val.ok_or_else(|| wasmtime_err("missing resource arg"))? else {
        return Err(wasmtime_err("expected resource arg"));
    };
    let res = any
        .try_into_resource::<BackingHandle>(&mut *cx)
        .map_err(|e| wasmtime_err(&format!("typed resource: {e}")))?;
    Ok(res.rep())
}

fn default_engine() -> Result<Engine, WasmStoreError> {
    let mut config = covalence_wasm::engine::wasmtime::Config::new();
    config.wasm_component_model(true);
    Engine::new(&config).map_err(|e| WasmStoreError::Engine(e.to_string()))
}

fn lookup(
    store: &mut Store<HostState>,
    instance: &covalence_wasm::engine::wasmtime::component::Instance,
    api_idx: &ComponentExportIndex,
    name: &'static str,
) -> Result<Func, WasmStoreError> {
    let idx = instance
        .get_export_index(&mut *store, Some(api_idx), name)
        .ok_or(WasmStoreError::MissingExport(name, STORE_API))?;
    instance
        .get_func(&mut *store, &idx)
        .ok_or(WasmStoreError::MissingExport(name, STORE_API))
}

fn key_val(key: &[u8]) -> Val {
    Val::List(key.iter().copied().map(Val::U8).collect())
}

fn list_to_vec(v: &Val) -> Option<Vec<u8>> {
    match v {
        Val::List(items) => {
            let mut out = Vec::with_capacity(items.len());
            for item in items {
                match item {
                    Val::U8(b) => out.push(*b),
                    _ => return None,
                }
            }
            Some(out)
        }
        _ => None,
    }
}

#[async_trait]
impl AsyncContentStore<Vec<u8>> for WasmStore {
    async fn get_slice(
        &self,
        key: &Vec<u8>,
        range: std::ops::Range<u64>,
    ) -> Result<Bytes, StoreError> {
        let bytes = {
            let mut inner = self.inner.lock().expect("WasmStore mutex poisoned");
            let Inner {
                store,
                get_func,
                handle,
                ..
            } = &mut *inner;
            let args = [handle.clone(), key_val(key)];
            let mut results = [Val::Bool(false)];
            get_func
                .call(&mut *store, &args, &mut results)
                .map_err(|e| StoreError::Io(format!("wasm get: {e}")))?;
            match &results[0] {
                Val::Option(Some(inner)) => list_to_vec(inner)
                    .ok_or_else(|| StoreError::Io("wasm get: expected list<u8>".into()))?,
                Val::Option(None) => return Err(StoreError::NotFound),
                other => {
                    return Err(StoreError::Io(format!(
                        "wasm get: expected option<list<u8>>, got {other:?}"
                    )));
                }
            }
        };
        let sliced = covalence_store::slice_range(&bytes, range)?;
        Ok(Bytes::from(sliced))
    }

    async fn head(&self, key: &Vec<u8>) -> Result<BlobInfo, StoreError> {
        let mut inner = self.inner.lock().expect("WasmStore mutex poisoned");
        let Inner {
            store,
            head_func,
            handle,
            ..
        } = &mut *inner;
        let args = [handle.clone(), key_val(key)];
        let mut results = [Val::Bool(false)];
        head_func
            .call(&mut *store, &args, &mut results)
            .map_err(|e| StoreError::Io(format!("wasm head: {e}")))?;
        match &results[0] {
            Val::Option(Some(rec)) => match &**rec {
                Val::Record(fields) => {
                    let size = fields
                        .iter()
                        .find(|(n, _)| n == "size")
                        .and_then(|(_, v)| match v {
                            Val::U64(n) => Some(*n),
                            _ => None,
                        })
                        .ok_or_else(|| {
                            StoreError::Io("wasm head: missing record field `size`".into())
                        })?;
                    Ok(BlobInfo { size })
                }
                other => Err(StoreError::Io(format!(
                    "wasm head: expected record, got {other:?}"
                ))),
            },
            Val::Option(None) => Err(StoreError::NotFound),
            other => Err(StoreError::Io(format!(
                "wasm head: expected option<blob-info>, got {other:?}"
            ))),
        }
    }

    async fn insert(&self, _data: Bytes) -> Result<Vec<u8>, StoreError> {
        Err(StoreError::Io(
            "cov:store/api@0.1.0 has no write side; insert is unimplemented".into(),
        ))
    }

    async fn put(&self, _key: Vec<u8>, _data: Bytes) -> Result<(), StoreError> {
        Err(StoreError::Io(
            "cov:store/api@0.1.0 has no write side; put is unimplemented".into(),
        ))
    }

    async fn contains(&self, key: &Vec<u8>) -> Result<bool, StoreError> {
        let mut inner = self.inner.lock().expect("WasmStore mutex poisoned");
        let Inner {
            store,
            contains_func,
            handle,
            ..
        } = &mut *inner;
        let args = [handle.clone(), key_val(key)];
        let mut results = [Val::Bool(false)];
        contains_func
            .call(&mut *store, &args, &mut results)
            .map_err(|e| StoreError::Io(format!("wasm contains: {e}")))?;
        match results[0] {
            Val::Bool(b) => Ok(b),
            ref other => Err(StoreError::Io(format!(
                "wasm contains: expected bool, got {other:?}"
            ))),
        }
    }
}
