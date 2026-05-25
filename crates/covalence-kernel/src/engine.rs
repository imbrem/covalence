//! WASM-based proposition engine.
//!
//! A **proposition** is a WASM component whose start function may call
//! `attest()` to declare itself true. The engine decides propositions by
//! compiling and instantiating them, observing whether `attest()` is called.
//!
//! ## Container hierarchy
//!
//! - **Container** — a collection of components with a distinguished root.
//!   `prove-{hash}` creates nested containers with isolated state.
//! - **Component** — a WASM component with typed imports and exports.
//! - **Module** — a WASM core module within a component (not yet used directly).
//!
//! ## Import system
//!
//! Components declare dependencies via specially-named imports:
//!
//! | Import prefix | Semantics | Sharing |
//! |---------------|-----------|---------|
//! | `link-{hash}` | Shared instance in the container | Cached by hash |
//! | `copy-{hash}` | Instance embedded in the importer | Always fresh |
//! | `prove-{hash}` | Container boundary (nested scope) | Isolated + lazy |
//! | `map-{name}` | Named key-value store | Shared in container |
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
//!
//! **Map** stores provide a key-value store (`get`/`set`) shared across all
//! components in the same container. Prove-dep boundaries create fresh,
//! isolated stores. Maps are **strictly typed**: each (key\_type, value\_type)
//! combination is disjoint (e.g. `map<u8,u8>` and `map<u16,u8>` don't share
//! state). Supported types for keys and values: u8, s8, u16, s16, u32, s32,
//! u64, s64, string, and `list<T>` for any of those integer types (where
//! `list<u8>` serves as the blob type).

use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};

use covalence_hash::O256;
use covalence_store::{BlobStore, ContentStore};
use covalence_wasm::engine::wasmtime;
use wasmtime::component::{Component, Func, Linker, Resource, ResourceTable, ResourceType, Val};
use wasmtime::{Engine, Store, StoreContextMut};

use crate::{DecideOutput, Decision};

/// Host-side representation of a blob resource.
struct BlobHandle {
    hash: O256,
    data: Option<Vec<u8>>,
}

/// Host-side representation of a name resource.
struct NameHandle {
    hash: O256,
}

/// Host state threaded through wasmtime's Store.
pub(crate) struct HostState {
    attested: bool,
    table: ResourceTable,
    /// Stack of prove-dep hashes currently being called through.
    /// When attest() is called, all hashes on this stack are marked as proved.
    prove_stack: Vec<O256>,
    /// Hashes that were on the prove stack when attest() was called.
    proved: HashSet<O256>,
}

impl HostState {
    fn new() -> Self {
        HostState {
            attested: false,
            table: ResourceTable::new(),
            prove_stack: Vec::new(),
            proved: HashSet::new(),
        }
    }
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
    /// A named key-value store: `map-{name}`.
    /// Shared within a container, isolated across prove-dep boundaries.
    Map(String),
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
    if let Some(store_name) = name.strip_prefix("map-") {
        return ImportKind::Map(store_name.to_string());
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

// ---------------------------------------------------------------------------
// ImportManifest — classifies a component's imports
// ---------------------------------------------------------------------------

/// Pre-classified import manifest for a component.
pub(crate) struct ImportManifest {
    /// Overall decision based on static analysis of imports.
    /// - `Unsat` if no attest/link/copy/prove imports exist.
    /// - `Unknown` otherwise (might become Sat at runtime).
    decision: Decision,
    link_deps: Vec<O256>,
    copy_deps: Vec<(String, O256)>,
    prove_deps: Vec<O256>,
    kv_stores: Vec<String>,
}

impl ImportManifest {
    /// Classify all imports of a component and determine the static decision.
    fn classify(engine: &Engine, component: &Component) -> Self {
        let ty = component.component_type();

        let mut imports_attest = false;
        let mut link_deps: Vec<O256> = Vec::new();
        let mut copy_deps: Vec<(String, O256)> = Vec::new();
        let mut prove_deps: Vec<O256> = Vec::new();
        let mut kv_stores: Vec<String> = Vec::new();

        for (name, _) in ty.imports(engine) {
            match categorize_import(name) {
                ImportKind::Attest => imports_attest = true,
                ImportKind::Link(hash) => link_deps.push(hash),
                ImportKind::Copy(hash) => copy_deps.push((name.to_string(), hash)),
                ImportKind::Prove(hash) => prove_deps.push(hash),
                ImportKind::Map(store_name) => kv_stores.push(store_name),
                _ => {}
            }
        }

        let decision = if !imports_attest
            && link_deps.is_empty()
            && copy_deps.is_empty()
            && prove_deps.is_empty()
        {
            Decision::Unsat
        } else {
            Decision::Unknown
        };

        ImportManifest {
            decision,
            link_deps,
            copy_deps,
            prove_deps,
            kv_stores,
        }
    }

    /// Check whether the component imports the `cov:blob/api` interface
    /// (directly or via `blob-{hash}` imports that reference its types).
    fn needs_api(engine: &Engine, component: &Component) -> bool {
        let ty = component.component_type();
        ty.imports(engine).any(|(name, _)| {
            matches!(
                categorize_import(name),
                ImportKind::BlobInterface | ImportKind::Blob(_)
            )
        })
    }
}

// ---------------------------------------------------------------------------
// LinkScope — instance caching and recursive dependency resolution
// ---------------------------------------------------------------------------

/// Linking scope: caches shared instances and lazy prove-deps during
/// recursive dependency resolution.
///
/// `resolving` is passed as a parameter (not a field) because
/// `resolve_prove` creates a child `LinkScope` with isolated caches
/// but shared cycle detection.
pub(crate) struct LinkScope<'a> {
    engine: &'a Engine,
    instance_cache: HashMap<O256, Vec<(String, Func)>>,
    lazy_proves: HashMap<O256, Arc<LazyProve>>,
    kv_stores: HashMap<String, Arc<Mutex<HashMap<Vec<u8>, Vec<u8>>>>>,
}

impl<'a> LinkScope<'a> {
    fn new(engine: &'a Engine) -> Self {
        LinkScope {
            engine,
            instance_cache: HashMap::new(),
            lazy_proves: HashMap::new(),
            kv_stores: HashMap::new(),
        }
    }

    /// Resolve all dependencies and build a linker for the component.
    pub(crate) fn link(
        &mut self,
        component: &Component,
        manifest: &ImportManifest,
        blobs: &BlobStore<O256>,
        store: &mut Store<HostState>,
    ) -> Result<Linker<HostState>, DecideError> {
        let mut resolving: HashSet<O256> = HashSet::new();

        // Resolve prove deps (compile + prepare lazy linker)
        for dep_hash in &manifest.prove_deps {
            self.resolve_prove(dep_hash, blobs, store, &mut resolving)?;
        }

        // Pre-resolve all link deps (shared instances, instantiated eagerly)
        for dep_hash in &manifest.link_deps {
            self.resolve_import(dep_hash, blobs, store, &mut resolving)?;
        }

        // Resolve copy deps (fresh instance per import site)
        let mut copy_cache: HashMap<String, Vec<(String, Func)>> = HashMap::new();
        for (import_name, dep_hash) in &manifest.copy_deps {
            let exports = self.resolve_copy(dep_hash, blobs, store, &mut resolving)?;
            copy_cache.insert(import_name.clone(), exports);
        }

        // Pre-create KV stores from manifest
        for store_name in &manifest.kv_stores {
            self.kv_stores
                .entry(store_name.clone())
                .or_insert_with(|| Arc::new(Mutex::new(HashMap::new())));
        }

        build_linker(
            self.engine,
            component,
            blobs,
            &self.instance_cache,
            &self.lazy_proves,
            &copy_cache,
            &self.kv_stores,
        )
    }

    /// Collect and recursively resolve link/copy/prove sub-deps for a
    /// compiled component. Returns a copy cache (keyed by import name)
    /// for any `copy-{hash}` sub-imports.
    fn resolve_sub_deps(
        &mut self,
        dep_component: &Component,
        blobs: &BlobStore<O256>,
        store: &mut Store<HostState>,
        resolving: &mut HashSet<O256>,
    ) -> Result<HashMap<String, Vec<(String, Func)>>, DecideError> {
        let dep_ty = dep_component.component_type();

        let mut link_sub_deps: Vec<O256> = Vec::new();
        let mut copy_sub_deps: Vec<(String, O256)> = Vec::new();
        let mut prove_sub_deps: Vec<O256> = Vec::new();
        for (name, _) in dep_ty.imports(self.engine) {
            match categorize_import(name) {
                ImportKind::Link(hash) => link_sub_deps.push(hash),
                ImportKind::Copy(hash) => copy_sub_deps.push((name.to_string(), hash)),
                ImportKind::Prove(hash) => prove_sub_deps.push(hash),
                ImportKind::Map(store_name) => {
                    self.kv_stores
                        .entry(store_name)
                        .or_insert_with(|| Arc::new(Mutex::new(HashMap::new())));
                }
                _ => {}
            }
        }
        for sub_hash in &link_sub_deps {
            self.resolve_import(sub_hash, blobs, store, resolving)?;
        }
        for sub_hash in &prove_sub_deps {
            self.resolve_prove(sub_hash, blobs, store, resolving)?;
        }

        let mut copy_cache: HashMap<String, Vec<(String, Func)>> = HashMap::new();
        for (import_name, dep_hash) in &copy_sub_deps {
            let exports = self.resolve_copy(dep_hash, blobs, store, resolving)?;
            copy_cache.insert(import_name.clone(), exports);
        }

        Ok(copy_cache)
    }

    /// Resolve a `link-{hash}` import: load, compile, and instantiate the
    /// dep component (recursively resolving its own deps). Caches instances
    /// by hash (shared across all importers in the same scope) and detects
    /// cycles.
    fn resolve_import(
        &mut self,
        dep_hash: &O256,
        blobs: &BlobStore<O256>,
        store: &mut Store<HostState>,
        resolving: &mut HashSet<O256>,
    ) -> Result<(), DecideError> {
        // Check cache first — shared instance already exists
        if self.instance_cache.contains_key(dep_hash) {
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

        let dep_component = Component::new(self.engine, &dep_bytes)
            .map_err(|e| DecideError::InvalidComponent(format!("dep {}: {e}", dep_hash)))?;

        let dep_ty = dep_component.component_type();

        let copy_cache = self.resolve_sub_deps(&dep_component, blobs, store, resolving)?;

        let dep_linker = build_linker(
            self.engine,
            &dep_component,
            blobs,
            &self.instance_cache,
            &self.lazy_proves,
            &copy_cache,
            &self.kv_stores,
        )?;

        // Instantiate the dep
        let instance = dep_linker
            .instantiate(&mut *store, &dep_component)
            .map_err(|e| DecideError::InstantiationError(format!("dep {}: {e}", dep_hash)))?;

        // Collect exported functions
        let mut exports = Vec::new();
        for (export_name, _) in dep_ty.exports(self.engine) {
            if let Some(func) = instance.get_func(&mut *store, export_name) {
                exports.push((export_name.to_string(), func));
            }
        }

        // Remove from resolving set, add to cache
        resolving.remove(dep_hash);
        self.instance_cache.insert(*dep_hash, exports);

        Ok(())
    }

    /// Resolve a `copy-{hash}` import: load, compile, and instantiate a
    /// fresh (unshared) instance of the dep component. Unlike `resolve_import`,
    /// this never checks or populates the shared instance cache — each call
    /// produces a new instance. Sub-link-deps of the copy still use the
    /// shared `instance_cache`. Cycle detection still applies.
    fn resolve_copy(
        &mut self,
        dep_hash: &O256,
        blobs: &BlobStore<O256>,
        store: &mut Store<HostState>,
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

        let dep_component = Component::new(self.engine, &dep_bytes)
            .map_err(|e| DecideError::InvalidComponent(format!("copy dep {}: {e}", dep_hash)))?;

        let dep_ty = dep_component.component_type();

        // Sub-link-deps use the shared instance_cache
        let copy_cache = self.resolve_sub_deps(&dep_component, blobs, store, resolving)?;

        let dep_linker = build_linker(
            self.engine,
            &dep_component,
            blobs,
            &self.instance_cache,
            &self.lazy_proves,
            &copy_cache,
            &self.kv_stores,
        )?;

        let instance = dep_linker
            .instantiate(&mut *store, &dep_component)
            .map_err(|e| DecideError::InstantiationError(format!("copy dep {}: {e}", dep_hash)))?;

        let mut exports = Vec::new();
        for (export_name, _) in dep_ty.exports(self.engine) {
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
        &mut self,
        dep_hash: &O256,
        blobs: &BlobStore<O256>,
        store: &mut Store<HostState>,
        resolving: &mut HashSet<O256>,
    ) -> Result<(), DecideError> {
        // Already resolved
        if self.lazy_proves.contains_key(dep_hash) {
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

        let dep_component = Component::new(self.engine, &dep_bytes)
            .map_err(|e| DecideError::InvalidComponent(format!("prove dep {}: {e}", dep_hash)))?;

        // Isolated caches for prove-dep sub-deps
        let mut child = LinkScope::new(self.engine);

        let copy_cache = child.resolve_sub_deps(&dep_component, blobs, store, resolving)?;

        // Build linker using the isolated caches (the linker clones what it
        // needs, so the local maps can be dropped after this).
        let dep_linker = build_linker(
            self.engine,
            &dep_component,
            blobs,
            &child.instance_cache,
            &child.lazy_proves,
            &copy_cache,
            &child.kv_stores,
        )?;

        let lazy = Arc::new(LazyProve {
            linker: dep_linker,
            component: dep_component,
            instance: Mutex::new(None),
        });

        resolving.remove(dep_hash);
        self.lazy_proves.insert(*dep_hash, lazy);

        Ok(())
    }
}

// ---------------------------------------------------------------------------
// KV store value serialization
// ---------------------------------------------------------------------------

// Type tags for serialization. Each scalar/list type gets a unique tag so
// that maps are strictly typed: map<u8,u8> and map<u16,u8> are disjoint.
const TAG_U8: u8 = 0x01;
const TAG_S8: u8 = 0x02;
const TAG_U16: u8 = 0x03;
const TAG_S16: u8 = 0x04;
const TAG_U32: u8 = 0x05;
const TAG_S32: u8 = 0x06;
const TAG_U64: u8 = 0x07;
const TAG_S64: u8 = 0x08;
const TAG_STRING: u8 = 0x09;
// Lists: 0x10 + element scalar tag
const TAG_LIST_U8: u8 = 0x11;
const TAG_LIST_S8: u8 = 0x12;
const TAG_LIST_U16: u8 = 0x13;
const TAG_LIST_S16: u8 = 0x14;
const TAG_LIST_U32: u8 = 0x15;
const TAG_LIST_S32: u8 = 0x16;
const TAG_LIST_U64: u8 = 0x17;
const TAG_LIST_S64: u8 = 0x18;

/// Map a component-model `Type` (from the function signature) to a type tag.
fn component_type_to_tag(ty: &wasmtime::component::types::Type) -> wasmtime::Result<u8> {
    use wasmtime::component::types::Type;
    match ty {
        Type::U8 => Ok(TAG_U8),
        Type::S8 => Ok(TAG_S8),
        Type::U16 => Ok(TAG_U16),
        Type::S16 => Ok(TAG_S16),
        Type::U32 => Ok(TAG_U32),
        Type::S32 => Ok(TAG_S32),
        Type::U64 => Ok(TAG_U64),
        Type::S64 => Ok(TAG_S64),
        Type::String => Ok(TAG_STRING),
        Type::List(list) => {
            let elem = list.ty();
            match &elem {
                Type::U8 => Ok(TAG_LIST_U8),
                Type::S8 => Ok(TAG_LIST_S8),
                Type::U16 => Ok(TAG_LIST_U16),
                Type::S16 => Ok(TAG_LIST_S16),
                Type::U32 => Ok(TAG_LIST_U32),
                Type::S32 => Ok(TAG_LIST_S32),
                Type::U64 => Ok(TAG_LIST_U64),
                Type::S64 => Ok(TAG_LIST_S64),
                _ => Err(wasmtime::Error::msg(format!(
                    "map store: unsupported list element type: {elem:?}"
                ))),
            }
        }
        _ => Err(wasmtime::Error::msg(format!(
            "map store: unsupported type: {ty:?}"
        ))),
    }
}

/// Serialize a component-model `Val` to a tagged byte sequence.
///
/// Supported scalar types: u8, s8, u16, s16, u32, s32, u64, s64, string.
/// Supported list types: list<u8> (blob), list<s8>, list<u16..u64>, list<s16..s64>.
fn serialize_val(val: &Val) -> wasmtime::Result<Vec<u8>> {
    match val {
        Val::U8(n) => Ok(vec![TAG_U8, *n]),
        Val::S8(n) => Ok(vec![TAG_S8, *n as u8]),
        Val::U16(n) => {
            let mut buf = vec![TAG_U16];
            buf.extend_from_slice(&n.to_le_bytes());
            Ok(buf)
        }
        Val::S16(n) => {
            let mut buf = vec![TAG_S16];
            buf.extend_from_slice(&n.to_le_bytes());
            Ok(buf)
        }
        Val::U32(n) => {
            let mut buf = vec![TAG_U32];
            buf.extend_from_slice(&n.to_le_bytes());
            Ok(buf)
        }
        Val::S32(n) => {
            let mut buf = vec![TAG_S32];
            buf.extend_from_slice(&n.to_le_bytes());
            Ok(buf)
        }
        Val::U64(n) => {
            let mut buf = vec![TAG_U64];
            buf.extend_from_slice(&n.to_le_bytes());
            Ok(buf)
        }
        Val::S64(n) => {
            let mut buf = vec![TAG_S64];
            buf.extend_from_slice(&n.to_le_bytes());
            Ok(buf)
        }
        Val::String(s) => {
            let mut buf = vec![TAG_STRING];
            buf.extend_from_slice(s.as_bytes());
            Ok(buf)
        }
        Val::List(elems) => serialize_list(elems),
        _ => Err(wasmtime::Error::msg("map store: unsupported value type")),
    }
}

/// Serialize a list Val to tagged bytes. The tag encodes the element type.
fn serialize_list(elems: &[Val]) -> wasmtime::Result<Vec<u8>> {
    if elems.is_empty() {
        // Empty list — we still need the tag. Infer from context is hard,
        // but an empty list serializes to just the tag with no data.
        // The caller should use component_type_to_tag for the full key.
        // Use a generic list-u8 tag; the strict-typing key prefix
        // disambiguates anyway.
        return Ok(vec![TAG_LIST_U8]);
    }
    match &elems[0] {
        Val::U8(_) => {
            let mut buf = vec![TAG_LIST_U8];
            for v in elems {
                match v {
                    Val::U8(b) => buf.push(*b),
                    _ => return Err(wasmtime::Error::msg("map store: heterogeneous list")),
                }
            }
            Ok(buf)
        }
        Val::S8(_) => {
            let mut buf = vec![TAG_LIST_S8];
            for v in elems {
                match v {
                    Val::S8(b) => buf.push(*b as u8),
                    _ => return Err(wasmtime::Error::msg("map store: heterogeneous list")),
                }
            }
            Ok(buf)
        }
        Val::U16(_) => {
            let mut buf = vec![TAG_LIST_U16];
            for v in elems {
                match v {
                    Val::U16(n) => buf.extend_from_slice(&n.to_le_bytes()),
                    _ => return Err(wasmtime::Error::msg("map store: heterogeneous list")),
                }
            }
            Ok(buf)
        }
        Val::S16(_) => {
            let mut buf = vec![TAG_LIST_S16];
            for v in elems {
                match v {
                    Val::S16(n) => buf.extend_from_slice(&n.to_le_bytes()),
                    _ => return Err(wasmtime::Error::msg("map store: heterogeneous list")),
                }
            }
            Ok(buf)
        }
        Val::U32(_) => {
            let mut buf = vec![TAG_LIST_U32];
            for v in elems {
                match v {
                    Val::U32(n) => buf.extend_from_slice(&n.to_le_bytes()),
                    _ => return Err(wasmtime::Error::msg("map store: heterogeneous list")),
                }
            }
            Ok(buf)
        }
        Val::S32(_) => {
            let mut buf = vec![TAG_LIST_S32];
            for v in elems {
                match v {
                    Val::S32(n) => buf.extend_from_slice(&n.to_le_bytes()),
                    _ => return Err(wasmtime::Error::msg("map store: heterogeneous list")),
                }
            }
            Ok(buf)
        }
        Val::U64(_) => {
            let mut buf = vec![TAG_LIST_U64];
            for v in elems {
                match v {
                    Val::U64(n) => buf.extend_from_slice(&n.to_le_bytes()),
                    _ => return Err(wasmtime::Error::msg("map store: heterogeneous list")),
                }
            }
            Ok(buf)
        }
        Val::S64(_) => {
            let mut buf = vec![TAG_LIST_S64];
            for v in elems {
                match v {
                    Val::S64(n) => buf.extend_from_slice(&n.to_le_bytes()),
                    _ => return Err(wasmtime::Error::msg("map store: heterogeneous list")),
                }
            }
            Ok(buf)
        }
        _ => Err(wasmtime::Error::msg(
            "map store: unsupported list element type",
        )),
    }
}

/// Deserialize a tagged byte sequence back to a component-model `Val`.
fn deserialize_val(bytes: &[u8]) -> wasmtime::Result<Val> {
    if bytes.is_empty() {
        return Err(wasmtime::Error::msg("map store: empty serialized value"));
    }
    let data = &bytes[1..];
    match bytes[0] {
        TAG_U8 => {
            if data.is_empty() {
                return Err(wasmtime::Error::msg("map store: truncated u8"));
            }
            Ok(Val::U8(data[0]))
        }
        TAG_S8 => {
            if data.is_empty() {
                return Err(wasmtime::Error::msg("map store: truncated s8"));
            }
            Ok(Val::S8(data[0] as i8))
        }
        TAG_U16 => {
            Ok(Val::U16(u16::from_le_bytes(data[..2].try_into().map_err(
                |_| wasmtime::Error::msg("map store: truncated u16"),
            )?)))
        }
        TAG_S16 => {
            Ok(Val::S16(i16::from_le_bytes(data[..2].try_into().map_err(
                |_| wasmtime::Error::msg("map store: truncated s16"),
            )?)))
        }
        TAG_U32 => {
            Ok(Val::U32(u32::from_le_bytes(data[..4].try_into().map_err(
                |_| wasmtime::Error::msg("map store: truncated u32"),
            )?)))
        }
        TAG_S32 => {
            Ok(Val::S32(i32::from_le_bytes(data[..4].try_into().map_err(
                |_| wasmtime::Error::msg("map store: truncated s32"),
            )?)))
        }
        TAG_U64 => {
            Ok(Val::U64(u64::from_le_bytes(data[..8].try_into().map_err(
                |_| wasmtime::Error::msg("map store: truncated u64"),
            )?)))
        }
        TAG_S64 => {
            Ok(Val::S64(i64::from_le_bytes(data[..8].try_into().map_err(
                |_| wasmtime::Error::msg("map store: truncated s64"),
            )?)))
        }
        TAG_STRING => {
            let s = std::str::from_utf8(data)
                .map_err(|e| wasmtime::Error::msg(format!("map store: invalid UTF-8: {e}")))?;
            Ok(Val::String(s.to_string()))
        }
        TAG_LIST_U8 => Ok(Val::List(data.iter().map(|&b| Val::U8(b)).collect())),
        TAG_LIST_S8 => Ok(Val::List(data.iter().map(|&b| Val::S8(b as i8)).collect())),
        TAG_LIST_U16 => Ok(Val::List(
            data.chunks_exact(2)
                .map(|c| Val::U16(u16::from_le_bytes([c[0], c[1]])))
                .collect(),
        )),
        TAG_LIST_S16 => Ok(Val::List(
            data.chunks_exact(2)
                .map(|c| Val::S16(i16::from_le_bytes([c[0], c[1]])))
                .collect(),
        )),
        TAG_LIST_U32 => Ok(Val::List(
            data.chunks_exact(4)
                .map(|c| Val::U32(u32::from_le_bytes(c.try_into().unwrap())))
                .collect(),
        )),
        TAG_LIST_S32 => Ok(Val::List(
            data.chunks_exact(4)
                .map(|c| Val::S32(i32::from_le_bytes(c.try_into().unwrap())))
                .collect(),
        )),
        TAG_LIST_U64 => Ok(Val::List(
            data.chunks_exact(8)
                .map(|c| Val::U64(u64::from_le_bytes(c.try_into().unwrap())))
                .collect(),
        )),
        TAG_LIST_S64 => Ok(Val::List(
            data.chunks_exact(8)
                .map(|c| Val::S64(i64::from_le_bytes(c.try_into().unwrap())))
                .collect(),
        )),
        tag => Err(wasmtime::Error::msg(format!(
            "map store: unknown type tag {tag:#x}"
        ))),
    }
}

// ---------------------------------------------------------------------------
// build_linker — free function (avoids borrow conflicts)
// ---------------------------------------------------------------------------

/// Build a linker for a component, wiring up attest, blob, link, copy,
/// prove, and map imports.
fn build_linker(
    engine: &Engine,
    component: &Component,
    blobs: &BlobStore<O256>,
    instance_cache: &HashMap<O256, Vec<(String, Func)>>,
    lazy_proves: &HashMap<O256, Arc<LazyProve>>,
    copy_cache: &HashMap<String, Vec<(String, Func)>>,
    kv_stores: &HashMap<String, Arc<Mutex<HashMap<Vec<u8>, Vec<u8>>>>>,
) -> Result<Linker<HostState>, DecideError> {
    let ty = component.component_type();
    let mut linker: Linker<HostState> = Linker::new(engine);

    // Register the cov:blob/api interface if the component imports it
    // (either directly or via blob-{hash} imports).
    let needs_api = ImportManifest::needs_api(engine, component);

    if needs_api {
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

        // --- name resource ---

        let name_ty = ResourceType::host::<NameHandle>();
        api.resource(
            "name",
            name_ty,
            |mut cx: StoreContextMut<'_, HostState>, rep| {
                cx.data_mut()
                    .table
                    .delete(Resource::<NameHandle>::new_own(rep))?;
                Ok(())
            },
        )
        .map_err(|e| DecideError::LinkError(e.to_string()))?;

        // [constructor]name: (borrow<blob>) -> own<name>
        {
            let store = blobs.clone();
            api.func_wrap(
                "[constructor]name",
                move |mut cx: StoreContextMut<'_, HostState>,
                      (blob,): (Resource<BlobHandle>,)|
                      -> wasmtime::Result<(Resource<NameHandle>,)> {
                    let handle = cx.data().table.get(&blob)?;
                    let hash = handle.hash;
                    let data = handle.data.clone();
                    if let Some(ref data) = data {
                        store
                            .put(hash, data)
                            .map_err(|e| wasmtime::Error::msg(format!("store put: {e}")))?;
                    }
                    let name = NameHandle { hash };
                    let resource = cx.data_mut().table.push(name)?;
                    Ok((resource,))
                },
            )
            .map_err(|e| DecideError::LinkError(e.to_string()))?;
        }

        // [method]name.uncons: (borrow<name>) -> own<blob>
        {
            let store = blobs.clone();
            api.func_wrap(
                "[method]name.uncons",
                move |mut cx: StoreContextMut<'_, HostState>,
                      (name_res,): (Resource<NameHandle>,)|
                      -> wasmtime::Result<(Resource<BlobHandle>,)> {
                    let hash = cx.data().table.get(&name_res)?.hash;
                    let data = store.get(&hash);
                    let blob = BlobHandle { hash, data };
                    let resource = cx.data_mut().table.push(blob)?;
                    Ok((resource,))
                },
            )
            .map_err(|e| DecideError::LinkError(e.to_string()))?;
        }

        // [method]name.eq: (borrow<name>, borrow<name>) -> bool
        api.func_wrap(
            "[method]name.eq",
            |cx: StoreContextMut<'_, HostState>,
             (a, b): (Resource<NameHandle>, Resource<NameHandle>)|
             -> wasmtime::Result<(bool,)> {
                let ha = cx.data().table.get(&a)?.hash;
                let hb = cx.data().table.get(&b)?.hash;
                Ok((ha == hb,))
            },
        )
        .map_err(|e| DecideError::LinkError(e.to_string()))?;

        // [static]name.cons: (borrow<name>, borrow<blob>) -> own<name>
        api.func_wrap(
            "[static]name.cons",
            |mut cx: StoreContextMut<'_, HostState>,
             (tag, blob): (Resource<NameHandle>, Resource<BlobHandle>)|
             -> wasmtime::Result<(Resource<NameHandle>,)> {
                let tag_hash = cx.data().table.get(&tag)?.hash;
                let blob_data = cx
                    .data()
                    .table
                    .get(&blob)?
                    .data
                    .as_ref()
                    .ok_or_else(|| wasmtime::Error::msg("blob data not available"))?
                    .clone();
                let name_hash = tag_hash.tag(&blob_data);
                let name = NameHandle { hash: name_hash };
                let resource = cx.data_mut().table.push(name)?;
                Ok((resource,))
            },
        )
        .map_err(|e| DecideError::LinkError(e.to_string()))?;

        // [method]name.repr: (borrow<name>) -> own<blob>
        // Currently works like uncons.
        {
            let store = blobs.clone();
            api.func_wrap(
                "[method]name.repr",
                move |mut cx: StoreContextMut<'_, HostState>,
                      (name_res,): (Resource<NameHandle>,)|
                      -> wasmtime::Result<(Resource<BlobHandle>,)> {
                    let hash = cx.data().table.get(&name_res)?.hash;
                    let data = store.get(&hash);
                    let blob = BlobHandle { hash, data };
                    let resource = cx.data_mut().table.push(blob)?;
                    Ok((resource,))
                },
            )
            .map_err(|e| DecideError::LinkError(e.to_string()))?;
        }

        // [method]name.tag: (borrow<name>) -> own<name>
        // Currently always traps.
        api.func_wrap(
            "[method]name.tag",
            |_cx: StoreContextMut<'_, HostState>,
             (_name_res,): (Resource<NameHandle>,)|
             -> wasmtime::Result<(Resource<NameHandle>,)> {
                Err(wasmtime::Error::msg("name.tag not yet implemented"))
            },
        )
        .map_err(|e| DecideError::LinkError(e.to_string()))?;
    }

    for (name, _) in ty.imports(engine) {
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

                for (export_name, _) in prove_ty.exports(engine) {
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
            ImportKind::Map(ref store_name) => {
                let store = kv_stores
                    .get(store_name)
                    .cloned()
                    .expect("kv store not pre-created");
                let store_for_set = store.clone();
                let store_for_get = store;
                let err_name = store_name.clone();

                let mut root = linker.root();
                let mut inst = root
                    .instance(name)
                    .map_err(|e| DecideError::LinkError(e.to_string()))?;

                // set(key, value) — strict typing: value type tag is
                // appended to the serialized key so that map<K,V1> and
                // map<K,V2> are disjoint.
                inst.func_new("set", move |_cx, ty, args, _results| {
                    let val_tag = component_type_to_tag(&ty.params().nth(1).unwrap().1)?;
                    let mut key = serialize_val(&args[0])?;
                    key.push(val_tag);
                    let value = serialize_val(&args[1])?;
                    store_for_set.lock().unwrap().insert(key, value);
                    Ok(())
                })
                .map_err(|e| DecideError::LinkError(e.to_string()))?;

                // get(key) -> value — uses result type tag for strict typing.
                inst.func_new("get", move |_cx, ty, args, results| {
                    let val_tag = component_type_to_tag(&ty.results().next().unwrap())?;
                    let mut key = serialize_val(&args[0])?;
                    key.push(val_tag);
                    match store_for_get.lock().unwrap().get(&key).cloned() {
                        Some(v) => {
                            results[0] = deserialize_val(&v)?;
                            Ok(())
                        }
                        None => Err(wasmtime::Error::msg(format!(
                            "key not found in map-{}",
                            err_name
                        ))),
                    }
                })
                .map_err(|e| DecideError::LinkError(e.to_string()))?;
            }
            ImportKind::Unknown(ref unknown) => {
                return Err(DecideError::LinkError(format!("unknown import: {unknown}")));
            }
        }
    }

    Ok(linker)
}

// ---------------------------------------------------------------------------
// WasmEngine — public API
// ---------------------------------------------------------------------------

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
    /// - `"map-{name}"`: a named key-value store with `get(key) -> value` and
    ///   `set(key, value)`. Shared within a container, isolated across
    ///   prove-dep boundaries. Strictly typed: each (key\_type, value\_type)
    ///   combination is disjoint. Supports u8, s8, u16, s16, u32, s32, u64,
    ///   s64, string, and `list<T>` (integer element types) for both keys
    ///   and values.
    ///
    /// Returns a `DecideOutput` with the decision and any hashes proved.
    pub fn decide(
        &self,
        bytes: &[u8],
        blobs: &BlobStore<O256>,
    ) -> Result<DecideOutput, DecideError> {
        let component = Component::new(&self.engine, bytes)
            .map_err(|e| DecideError::InvalidComponent(e.to_string()))?;
        let manifest = ImportManifest::classify(&self.engine, &component);

        if manifest.decision == Decision::Unsat {
            return Ok(DecideOutput {
                decision: Decision::Unsat,
                proved: vec![],
            });
        }

        let mut store = Store::new(&self.engine, HostState::new());
        let mut scope = LinkScope::new(&self.engine);
        let linker = scope.link(&component, &manifest, blobs, &mut store)?;

        // Instantiate the component — this runs the start function.
        // A trap during instantiation means the start function didn't complete;
        // if attest was already called before the trap, result is Sat,
        // otherwise Unknown (we can't determine the result).
        let instantiation = linker.instantiate(&mut store, &component);

        let proved: Vec<O256> = store.data().proved.iter().copied().collect();

        if instantiation.is_err() {
            return Ok(DecideOutput {
                decision: if store.data().attested {
                    Decision::Sat
                } else {
                    Decision::Unknown
                },
                proved,
            });
        }

        Ok(DecideOutput {
            decision: if store.data().attested {
                Decision::Sat
            } else {
                manifest.decision
            },
            proved,
        })
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
