//! WASM-based proposition engine.
//!
//! A **proposition** is a WASM component whose start function may call
//! `attest()` to declare itself true. The engine decides propositions by
//! compiling and instantiating them, observing whether `attest()` is called.
//!
//! ## Import system
//!
//! Components declare dependencies via specially-named imports. The three
//! instance import types map to a container model:
//!
//! | Import prefix | Semantics | Instance sharing |
//! |---------------|-----------|-----------------|
//! | `link-{hash}` | Shared instance in the container | Cached by hash |
//! | `copy-{hash}` | Instance embedded in the importer | Always fresh |
//! | `prove-{hash}` | Container boundary (nested scope) | Isolated + lazy |
//!
//! **Link** deps are eagerly instantiated once and shared across all importers
//! within the same linking scope (the "diamond dep" pattern).
//!
//! **Copy** deps are eagerly instantiated per import site — each `copy-{hash}`
//! gets a fresh instance with its own mutable state. Sub-link-deps of a copy
//! still participate in the shared cache.
//!
//! **Prove** deps are lazily instantiated on first function call, with fully
//! isolated link-instances. When a function is called through a prove-dep,
//! the dep's hash is pushed onto a prove stack; if `attest()` fires while
//! the hash is on the stack, that hash is recorded as proved.

use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};

use covalence_hash::O256;
use covalence_store::ContentStore;
use covalence_wasm::engine::wasmtime;
use wasmtime::component::{Component, Func, Linker, Resource, ResourceTable, ResourceType};
use wasmtime::{Engine, Store, StoreContextMut};

use crate::{DecideOutput, Decision};

/// Host-side representation of a blob resource.
struct BlobHandle {
    hash: O256,
    data: Option<Vec<u8>>,
}

/// Host state threaded through wasmtime's Store.
struct HostState {
    attested: bool,
    table: ResourceTable,
    /// Stack of prove-dep hashes currently being called through.
    /// When attest() is called, all hashes on this stack are marked as proved.
    prove_stack: Vec<O256>,
    /// Hashes that were on the prove stack when attest() was called.
    proved: HashSet<O256>,
}

/// Categorized import from a proposition component.
#[derive(Debug)]
enum ImportKind {
    /// The `attest()` function — calling it marks the proposition as true.
    Attest,
    /// The blob interface: "cov:blob/api".
    BlobInterface,
    /// A content-addressed blob by hash: "blob-{hex}".
    Blob(O256),
    /// A shared component instance by hash: "link-{hash}".
    /// All importers of the same hash within a linking scope share one instance.
    Link(O256),
    /// A fresh (unshared) component instance by hash: "copy-{hash}".
    /// Each import site gets its own instance; sub-link-deps still share.
    Copy(O256),
    /// A proof-composition dep by hash: "prove-{hash}".
    /// Lazily instantiated with isolated link-instances. Calling a function
    /// through this dep pushes its hash onto the prove stack; if `attest()`
    /// fires while the hash is on the stack, it is recorded as proved.
    Prove(O256),
    /// Unknown import name.
    Unknown(String),
}

fn categorize_import(name: &str) -> ImportKind {
    if name == "attest" {
        return ImportKind::Attest;
    }
    if name == "cov:blob/api" {
        return ImportKind::BlobInterface;
    }
    if let Some(hex) = name.strip_prefix("blob-") {
        if let Some(hash) = O256::from_hex(hex) {
            return ImportKind::Blob(hash);
        }
    }
    if let Some(hex) = name.strip_prefix("link-") {
        if let Some(hash) = O256::from_hex(hex) {
            return ImportKind::Link(hash);
        }
    }
    if let Some(hex) = name.strip_prefix("copy-") {
        if let Some(hash) = O256::from_hex(hex) {
            return ImportKind::Copy(hash);
        }
    }
    if let Some(hex) = name.strip_prefix("prove-") {
        if let Some(hash) = O256::from_hex(hex) {
            return ImportKind::Prove(hash);
        }
    }
    ImportKind::Unknown(name.to_string())
}

/// Wire pre-resolved exports into a linker instance slot.
fn wire_instance_exports(
    linker: &mut Linker<HostState>,
    name: &str,
    exports: Vec<(String, Func)>,
) -> Result<(), DecideError> {
    let mut root = linker.root();
    let mut li = root
        .instance(name)
        .map_err(|e| DecideError::LinkError(e.to_string()))?;
    for (export_name, export_func) in exports {
        li.func_new(&export_name, move |mut cx, _ty, args, results| {
            export_func.call(&mut cx, args, results)?;
            Ok(())
        })
        .map_err(|e| DecideError::LinkError(e.to_string()))?;
    }
    Ok(())
}

/// A deferred prove-dep. The component is compiled and its linker prepared,
/// but instantiation is deferred until the first function call through the
/// prove-dep wrapper. This avoids instantiating prove-deps that are never
/// called.
struct LazyProve {
    linker: Linker<HostState>,
    component: Component,
    instance: Mutex<Option<wasmtime::component::Instance>>,
}

/// WASM engine backed by wasmtime.
pub struct WasmEngine {
    engine: Engine,
}

impl WasmEngine {
    pub fn new() -> Result<Self, wasmtime::Error> {
        let mut config = wasmtime::Config::new();
        config.wasm_gc(true);
        let engine = Engine::new(&config)?;
        Ok(WasmEngine { engine })
    }

    /// Decide if a proposition (WASM component) is true,
    /// i.e. whether its start function calls `attest()`.
    ///
    /// ## Import types
    ///
    /// - `"attest"`: a zero-argument function that marks this proposition as
    ///   true. Calling it also proves every hash currently on the prove stack.
    /// - `"blob-{hash}"`: a content-addressed blob from the store, surfaced
    ///   as a `cov:blob/api` resource (lazy — traps if data is unavailable).
    /// - `"link-{hash}"`: a **shared** component instance (linked recursively,
    ///   eagerly instantiated). All importers of the same hash share one
    ///   instance within the same linking scope.
    /// - `"copy-{hash}"`: a **fresh** component instance per import site.
    ///   Eagerly instantiated like `link`, but never cached — each occurrence
    ///   gets its own instance. Sub-link-deps of a copy still use the shared
    ///   instance cache.
    /// - `"prove-{hash}"`: a component instance used for proof composition.
    ///   Lazily instantiated on first function call. When called, the hash
    ///   is pushed onto the prove stack; if `attest()` fires while the hash
    ///   is on the stack, that hash is recorded as proved. The prove-dep gets
    ///   isolated link-instances (not shared with the parent).
    ///
    /// Returns a `DecideOutput` with the decision and any hashes proved.
    pub fn decide(
        &self,
        bytes: &[u8],
        blobs: &dyn ContentStore<O256>,
    ) -> Result<DecideOutput, DecideError> {
        let component = Component::new(&self.engine, bytes)
            .map_err(|e| DecideError::InvalidComponent(e.to_string()))?;

        let ty = component.component_type();

        // Classify all imports and collect dep hashes
        let mut imports_attest = false;
        let mut link_deps: Vec<O256> = Vec::new();
        let mut copy_deps: Vec<(String, O256)> = Vec::new();
        let mut prove_deps: Vec<O256> = Vec::new();
        for (name, _) in ty.imports(&self.engine) {
            match categorize_import(name) {
                ImportKind::Attest => imports_attest = true,
                ImportKind::Link(hash) => link_deps.push(hash),
                ImportKind::Copy(hash) => copy_deps.push((name.to_string(), hash)),
                ImportKind::Prove(hash) => prove_deps.push(hash),
                _ => {}
            }
        }

        // Pre-check: if attest is not imported AND there are no deps that
        // could transitively attest, this prop is statically false
        if !imports_attest && link_deps.is_empty() && copy_deps.is_empty() && prove_deps.is_empty()
        {
            return Ok(DecideOutput {
                decision: Decision::False,
                proved: vec![],
            });
        }

        let mut store = Store::new(
            &self.engine,
            HostState {
                attested: false,
                table: ResourceTable::new(),
                prove_stack: Vec::new(),
                proved: HashSet::new(),
            },
        );
        let mut instance_cache: HashMap<O256, Vec<(String, Func)>> = HashMap::new();
        let mut lazy_proves: HashMap<O256, Arc<LazyProve>> = HashMap::new();
        let mut resolving: HashSet<O256> = HashSet::new();

        // Resolve prove deps (compile + prepare lazy linker)
        for dep_hash in &prove_deps {
            self.resolve_prove(
                dep_hash,
                blobs,
                &mut store,
                &mut instance_cache,
                &mut lazy_proves,
                &mut resolving,
            )?;
        }

        // Pre-resolve all link deps (shared instances, instantiated eagerly)
        for dep_hash in &link_deps {
            self.resolve_import(
                dep_hash,
                blobs,
                &mut store,
                &mut instance_cache,
                &mut lazy_proves,
                &mut resolving,
            )?;
        }

        // Resolve copy deps (fresh instance per import site)
        let mut copy_cache: HashMap<String, Vec<(String, Func)>> = HashMap::new();
        for (import_name, dep_hash) in &copy_deps {
            let exports = self.resolve_copy(
                dep_hash,
                blobs,
                &mut store,
                &mut instance_cache,
                &mut lazy_proves,
                &mut resolving,
            )?;
            copy_cache.insert(import_name.clone(), exports);
        }

        let linker = self.build_linker(
            &component,
            blobs,
            &instance_cache,
            &lazy_proves,
            &copy_cache,
        )?;

        // Instantiate the component — this runs the start function.
        // A trap during instantiation means the start function didn't complete;
        // if attest was already called before the trap, result is True,
        // otherwise Unknown (we can't determine the result).
        let instantiation = linker.instantiate(&mut store, &component);

        let proved: Vec<O256> = store.data().proved.iter().copied().collect();

        if instantiation.is_err() {
            return Ok(DecideOutput {
                decision: if store.data().attested {
                    Decision::True
                } else {
                    Decision::Unknown
                },
                proved,
            });
        }

        let decision = if store.data().attested {
            Decision::True
        } else if imports_attest {
            // Imported attest but didn't call it during startup
            Decision::Unknown
        } else {
            // No attest import, deps didn't transitively attest
            Decision::False
        };

        Ok(DecideOutput { decision, proved })
    }

    /// Build a linker for a component, wiring up attest, blob, link, copy,
    /// and prove imports.
    fn build_linker(
        &self,
        component: &Component,
        blobs: &dyn ContentStore<O256>,
        instance_cache: &HashMap<O256, Vec<(String, Func)>>,
        lazy_proves: &HashMap<O256, Arc<LazyProve>>,
        copy_cache: &HashMap<String, Vec<(String, Func)>>,
    ) -> Result<Linker<HostState>, DecideError> {
        let ty = component.component_type();
        let mut linker: Linker<HostState> = Linker::new(&self.engine);

        // Check if any blob imports exist — if so, register the blob interface.
        let has_blob_imports = ty
            .imports(&self.engine)
            .any(|(name, _)| matches!(categorize_import(name), ImportKind::Blob(_)));

        if has_blob_imports {
            let blob_ty = ResourceType::host::<BlobHandle>();
            let mut root = linker.root();
            let mut api = root
                .instance("cov:blob/api")
                .map_err(|e| DecideError::LinkError(e.to_string()))?;

            // Register the blob resource type with a destructor.
            api.resource(
                "blob",
                blob_ty,
                |mut cx: StoreContextMut<'_, HostState>, rep| {
                    cx.data_mut()
                        .table
                        .delete(Resource::<BlobHandle>::new_own(rep))?;
                    Ok(())
                },
            )
            .map_err(|e| DecideError::LinkError(e.to_string()))?;

            // [method]blob.read: (borrow<blob>) -> list<u8>
            api.func_wrap(
                "[method]blob.read",
                |cx: StoreContextMut<'_, HostState>,
                 (blob,): (Resource<BlobHandle>,)|
                 -> wasmtime::Result<(Vec<u8>,)> {
                    let handle = cx.data().table.get(&blob)?;
                    match &handle.data {
                        Some(d) => Ok((d.clone(),)),
                        None => Err(wasmtime::Error::msg("blob data not available")),
                    }
                },
            )
            .map_err(|e| DecideError::LinkError(e.to_string()))?;

            // [method]blob.eq: (borrow<blob>, borrow<blob>) -> bool
            api.func_wrap(
                "[method]blob.eq",
                |cx: StoreContextMut<'_, HostState>,
                 (a, b): (Resource<BlobHandle>, Resource<BlobHandle>)|
                 -> wasmtime::Result<(bool,)> {
                    let ha = cx.data().table.get(&a)?.hash;
                    let hb = cx.data().table.get(&b)?.hash;
                    Ok((ha == hb,))
                },
            )
            .map_err(|e| DecideError::LinkError(e.to_string()))?;
        }

        for (name, _) in ty.imports(&self.engine) {
            match categorize_import(name) {
                ImportKind::Attest => {
                    linker
                        .root()
                        .func_wrap(name, |mut cx: StoreContextMut<'_, HostState>, _args: ()| {
                            let state = cx.data_mut();
                            state.attested = true;
                            // Prove all hashes currently on the prove stack
                            let stack: Vec<O256> = state.prove_stack.clone();
                            for hash in stack {
                                state.proved.insert(hash);
                            }
                            Ok(())
                        })
                        .map_err(|e| DecideError::LinkError(e.to_string()))?;
                }
                ImportKind::BlobInterface => {
                    // Already registered above.
                }
                ImportKind::Blob(hash) => {
                    let data = blobs.get(&hash);
                    linker
                        .root()
                        .func_wrap(
                            name,
                            move |mut cx: StoreContextMut<'_, HostState>,
                                  _args: ()|
                                  -> wasmtime::Result<(Resource<BlobHandle>,)> {
                                let handle = BlobHandle {
                                    hash,
                                    data: data.clone(),
                                };
                                let resource = cx.data_mut().table.push(handle)?;
                                Ok((resource,))
                            },
                        )
                        .map_err(|e| DecideError::LinkError(e.to_string()))?;
                }
                ImportKind::Link(hash) => {
                    let exports = instance_cache.get(&hash).cloned().unwrap_or_default();
                    wire_instance_exports(&mut linker, name, exports)?;
                }
                ImportKind::Copy(_) => {
                    let exports = copy_cache.get(name).cloned().unwrap_or_default();
                    wire_instance_exports(&mut linker, name, exports)?;
                }
                ImportKind::Prove(hash) => {
                    let lazy = lazy_proves.get(&hash).cloned().ok_or_else(|| {
                        DecideError::LinkError(format!("prove dep not resolved: {hash}"))
                    })?;

                    let prove_ty = lazy.component.component_type();
                    let mut root = linker.root();
                    let mut li = root
                        .instance(name)
                        .map_err(|e| DecideError::LinkError(e.to_string()))?;

                    for (export_name, _) in prove_ty.exports(&self.engine) {
                        let lazy = lazy.clone();
                        let export_name_owned = export_name.to_string();
                        let prove_hash = hash;
                        li.func_new(export_name, move |mut cx, _ty, args, results| {
                            // Push prove hash BEFORE lazy instantiation so the
                            // dep's start function sees it on the stack.
                            cx.data_mut().prove_stack.push(prove_hash);

                            // Lazy instantiation
                            let init_result = {
                                let mut guard = lazy.instance.lock().unwrap();
                                if guard.is_none() {
                                    match lazy.linker.instantiate(&mut cx, &lazy.component) {
                                        Ok(inst) => {
                                            *guard = Some(inst);
                                            Ok(())
                                        }
                                        Err(e) => Err(e),
                                    }
                                } else {
                                    Ok(())
                                }
                            };
                            if let Err(e) = init_result {
                                cx.data_mut().prove_stack.pop();
                                return Err(e);
                            }

                            // Get the real function from the instance
                            let func = {
                                let guard = lazy.instance.lock().unwrap();
                                let instance = guard.as_ref().unwrap();
                                instance
                                    .get_func(&mut cx, &export_name_owned)
                                    .ok_or_else(|| {
                                        wasmtime::Error::msg(format!(
                                            "export not found: {}",
                                            export_name_owned
                                        ))
                                    })
                            };
                            let func = match func {
                                Ok(f) => f,
                                Err(e) => {
                                    cx.data_mut().prove_stack.pop();
                                    return Err(e);
                                }
                            };

                            // Call, then pop
                            let call_result = func.call(&mut cx, args, results);
                            cx.data_mut().prove_stack.pop();

                            call_result
                        })
                        .map_err(|e| DecideError::LinkError(e.to_string()))?;
                    }
                }
                ImportKind::Unknown(ref unknown) => {
                    return Err(DecideError::LinkError(format!("unknown import: {unknown}")));
                }
            }
        }

        Ok(linker)
    }

    /// Collect and recursively resolve link/copy/prove sub-deps for a
    /// compiled component. Returns a copy cache (keyed by import name)
    /// for any `copy-{hash}` sub-imports.
    fn resolve_sub_deps(
        &self,
        dep_component: &Component,
        blobs: &dyn ContentStore<O256>,
        store: &mut Store<HostState>,
        instance_cache: &mut HashMap<O256, Vec<(String, Func)>>,
        lazy_proves: &mut HashMap<O256, Arc<LazyProve>>,
        resolving: &mut HashSet<O256>,
    ) -> Result<HashMap<String, Vec<(String, Func)>>, DecideError> {
        let dep_ty = dep_component.component_type();

        let mut link_sub_deps: Vec<O256> = Vec::new();
        let mut copy_sub_deps: Vec<(String, O256)> = Vec::new();
        let mut prove_sub_deps: Vec<O256> = Vec::new();
        for (name, _) in dep_ty.imports(&self.engine) {
            match categorize_import(name) {
                ImportKind::Link(hash) => link_sub_deps.push(hash),
                ImportKind::Copy(hash) => copy_sub_deps.push((name.to_string(), hash)),
                ImportKind::Prove(hash) => prove_sub_deps.push(hash),
                _ => {}
            }
        }
        for sub_hash in &link_sub_deps {
            self.resolve_import(
                sub_hash,
                blobs,
                store,
                instance_cache,
                lazy_proves,
                resolving,
            )?;
        }
        for sub_hash in &prove_sub_deps {
            self.resolve_prove(
                sub_hash,
                blobs,
                store,
                instance_cache,
                lazy_proves,
                resolving,
            )?;
        }

        let mut copy_cache: HashMap<String, Vec<(String, Func)>> = HashMap::new();
        for (import_name, dep_hash) in &copy_sub_deps {
            let exports = self.resolve_copy(
                dep_hash,
                blobs,
                store,
                instance_cache,
                lazy_proves,
                resolving,
            )?;
            copy_cache.insert(import_name.clone(), exports);
        }

        Ok(copy_cache)
    }

    /// Resolve a `link-{hash}` import: load, compile, and instantiate the
    /// dep component (recursively resolving its own deps). Caches instances
    /// by hash (shared across all importers in the same scope) and detects
    /// cycles.
    fn resolve_import(
        &self,
        dep_hash: &O256,
        blobs: &dyn ContentStore<O256>,
        store: &mut Store<HostState>,
        instance_cache: &mut HashMap<O256, Vec<(String, Func)>>,
        lazy_proves: &mut HashMap<O256, Arc<LazyProve>>,
        resolving: &mut HashSet<O256>,
    ) -> Result<(), DecideError> {
        // Check cache first — shared instance already exists
        if instance_cache.contains_key(dep_hash) {
            return Ok(());
        }

        // Cycle detection
        if !resolving.insert(*dep_hash) {
            return Err(DecideError::CycleDetected(format!(
                "cycle detected resolving: {}",
                dep_hash
            )));
        }

        // Load bytes from store
        let dep_bytes = blobs
            .get(dep_hash)
            .ok_or_else(|| DecideError::MissingDep(format!("blob not found: {}", dep_hash)))?;

        let dep_component = Component::new(&self.engine, &dep_bytes)
            .map_err(|e| DecideError::InvalidComponent(format!("dep {}: {e}", dep_hash)))?;

        let dep_ty = dep_component.component_type();

        let copy_cache = self.resolve_sub_deps(
            &dep_component,
            blobs,
            store,
            instance_cache,
            lazy_proves,
            resolving,
        )?;

        let dep_linker = self.build_linker(
            &dep_component,
            blobs,
            instance_cache,
            lazy_proves,
            &copy_cache,
        )?;

        // Instantiate the dep
        let instance = dep_linker
            .instantiate(&mut *store, &dep_component)
            .map_err(|e| DecideError::InstantiationError(format!("dep {}: {e}", dep_hash)))?;

        // Collect exported functions
        let mut exports = Vec::new();
        for (export_name, _) in dep_ty.exports(&self.engine) {
            if let Some(func) = instance.get_func(&mut *store, export_name) {
                exports.push((export_name.to_string(), func));
            }
        }

        // Remove from resolving set, add to cache
        resolving.remove(dep_hash);
        instance_cache.insert(*dep_hash, exports);

        Ok(())
    }

    /// Resolve a `copy-{hash}` import: load, compile, and instantiate a
    /// fresh (unshared) instance of the dep component. Unlike `resolve_import`,
    /// this never checks or populates the shared instance cache — each call
    /// produces a new instance. Sub-link-deps of the copy still use the
    /// shared `instance_cache`. Cycle detection still applies.
    fn resolve_copy(
        &self,
        dep_hash: &O256,
        blobs: &dyn ContentStore<O256>,
        store: &mut Store<HostState>,
        instance_cache: &mut HashMap<O256, Vec<(String, Func)>>,
        lazy_proves: &mut HashMap<O256, Arc<LazyProve>>,
        resolving: &mut HashSet<O256>,
    ) -> Result<Vec<(String, Func)>, DecideError> {
        // Cycle detection (no cache check — always fresh)
        if !resolving.insert(*dep_hash) {
            return Err(DecideError::CycleDetected(format!(
                "cycle detected resolving copy dep: {}",
                dep_hash
            )));
        }

        let dep_bytes = blobs
            .get(dep_hash)
            .ok_or_else(|| DecideError::MissingDep(format!("blob not found: {}", dep_hash)))?;

        let dep_component = Component::new(&self.engine, &dep_bytes)
            .map_err(|e| DecideError::InvalidComponent(format!("copy dep {}: {e}", dep_hash)))?;

        let dep_ty = dep_component.component_type();

        // Sub-link-deps use the shared instance_cache
        let copy_cache = self.resolve_sub_deps(
            &dep_component,
            blobs,
            store,
            instance_cache,
            lazy_proves,
            resolving,
        )?;

        let dep_linker = self.build_linker(
            &dep_component,
            blobs,
            instance_cache,
            lazy_proves,
            &copy_cache,
        )?;

        let instance = dep_linker
            .instantiate(&mut *store, &dep_component)
            .map_err(|e| DecideError::InstantiationError(format!("copy dep {}: {e}", dep_hash)))?;

        let mut exports = Vec::new();
        for (export_name, _) in dep_ty.exports(&self.engine) {
            if let Some(func) = instance.get_func(&mut *store, export_name) {
                exports.push((export_name.to_string(), func));
            }
        }

        resolving.remove(dep_hash);
        // No cache store — the exports are returned directly to the caller
        Ok(exports)
    }

    /// Resolve a `prove-{hash}` import: load, compile, and prepare a lazy
    /// linker for proof composition. The component is NOT instantiated until
    /// the first function call through the prove-dep wrapper.
    ///
    /// Prove-deps get **isolated** link-instances: their sub-deps are resolved
    /// into fresh local caches, not the parent's shared cache. This prevents
    /// the parent from sharing mutable state (e.g. a union-find) with the
    /// prove-dep — the only way to interact with the prove-dep's internals
    /// is through its exports.
    fn resolve_prove(
        &self,
        dep_hash: &O256,
        blobs: &dyn ContentStore<O256>,
        store: &mut Store<HostState>,
        _instance_cache: &mut HashMap<O256, Vec<(String, Func)>>,
        lazy_proves: &mut HashMap<O256, Arc<LazyProve>>,
        resolving: &mut HashSet<O256>,
    ) -> Result<(), DecideError> {
        // Already resolved
        if lazy_proves.contains_key(dep_hash) {
            return Ok(());
        }

        // Cycle detection (shared with link/copy resolution)
        if !resolving.insert(*dep_hash) {
            return Err(DecideError::CycleDetected(format!(
                "cycle detected resolving prove dep: {}",
                dep_hash
            )));
        }

        // Load bytes from store
        let dep_bytes = blobs
            .get(dep_hash)
            .ok_or_else(|| DecideError::MissingDep(format!("blob not found: {}", dep_hash)))?;

        let dep_component = Component::new(&self.engine, &dep_bytes)
            .map_err(|e| DecideError::InvalidComponent(format!("prove dep {}: {e}", dep_hash)))?;

        // Isolated caches for prove-dep sub-deps
        let mut local_instances: HashMap<O256, Vec<(String, Func)>> = HashMap::new();
        let mut local_proves: HashMap<O256, Arc<LazyProve>> = HashMap::new();

        let copy_cache = self.resolve_sub_deps(
            &dep_component,
            blobs,
            store,
            &mut local_instances,
            &mut local_proves,
            resolving,
        )?;

        // Build linker using the isolated caches (the linker clones what it
        // needs, so the local maps can be dropped after this).
        let dep_linker = self.build_linker(
            &dep_component,
            blobs,
            &local_instances,
            &local_proves,
            &copy_cache,
        )?;

        let lazy = Arc::new(LazyProve {
            linker: dep_linker,
            component: dep_component,
            instance: Mutex::new(None),
        });

        resolving.remove(dep_hash);
        lazy_proves.insert(*dep_hash, lazy);

        Ok(())
    }
}

/// Errors from proposition deciding.
#[derive(Debug, thiserror::Error)]
pub enum DecideError {
    #[error("invalid component: {0}")]
    InvalidComponent(String),
    #[error("missing dep: {0}")]
    MissingDep(String),
    #[error("link error: {0}")]
    LinkError(String),
    #[error("instantiation error: {0}")]
    InstantiationError(String),
    #[error("cycle detected: {0}")]
    CycleDetected(String),
}
