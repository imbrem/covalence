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
//! | `store` | Hierarchical KV store resource | Shared in container |
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
//! **Store** provides a hierarchical key-value resource shared across all
//! components in the same container. Prove-dep boundaries create fresh,
//! isolated stores. The store is **strictly typed**: each (key\_type, value\_type)
//! combination is disjoint (e.g. `store<u8,u8>` and `store<u16,u8>` don't share
//! state). Supported types for keys and values: u8, s8, u16, s16, u32, s32,
//! u64, s64, string, and `list<T>` for any of those integer types (where
//! `list<u8>` serves as the blob type).
//!
//! The store resource API:
//! - `root()` → the container's shared root store
//! - `new()` → a fresh anonymous store (not shared)
//! - `set(borrow<store>, key, value)` — insert/overwrite
//! - `get(borrow<store>, key) → value` — lookup (traps if missing)
//! - `try-get(borrow<store>, key) → option<value>` — lookup (None if missing)
//! - `assert-exists(borrow<store>, key)` — traps if key never set
//! - `try-exists(borrow<store>, key) → bool` — true if set, false otherwise
//! - `ns(borrow<store>, key) → own<store>` — sub-namespace navigation
//! - `clone(borrow<store>) → own<store>` — duplicate handle (same data)
//! - `read-only(borrow<store>) → own<store>` — read-only clone (set traps)
//!
//! Supported key/value types: u8, s8, u16, s16, u32, s32, u64, s64, string,
//! `list<T>` for integer element types, `borrow<blob>` / `own<blob>`, and
//! `borrow<name>` / `own<name>`. Blob and name values are stored by hash
//! (without fetching blob data) and are distinct from each other even when
//! their hashes coincide.

use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};

use covalence_hash::O256;
use covalence_store::{BlobStore, ContentStore, KvStore, MemoryKvStore};
use covalence_wasm::engine::wasmtime;
use wasmtime::component::{
    Component, Func, Linker, Resource, ResourceAny, ResourceTable, ResourceType, Val,
};
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

/// Host-side representation of a principal resource (public key).
struct PrincipalHandle {
    key: covalence_sig::VerifyingKey,
}

/// Host-side representation of a signature resource (opaque).
struct SignatureHandle {
    sig: covalence_sig::Signature,
}

/// Host-side representation of a signer resource (keypair).
struct SignerHandle {
    key: covalence_sig::SigningKey,
}

/// A handle to a KV store, optionally read-only.
struct StoreHandle {
    data: Arc<dyn KvStore>,
    writable: bool,
}

/// Host-side representation of a HOL Light type resource.
#[cfg(feature = "hol")]
struct HolTypeHandle {
    ty: covalence_hol::TypeId,
}

/// Host-side representation of a HOL Light term resource.
#[cfg(feature = "hol")]
struct TermHandle {
    term: covalence_hol::TermId,
}

/// Host-side representation of a HOL Light theorem resource.
#[cfg(feature = "hol")]
struct ThmHandle {
    thm: covalence_hol::ThmId,
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
    /// The store resource interface: "store".
    /// Provides a hierarchical KV store shared within a container.
    Store,
    /// The signing interface: "cov:sign/api".
    SignInterface,
    /// A generate-signer host function (test/dev only).
    GenerateSigner,
    /// The HOL Light kernel interface: "cov:hol/kernel".
    #[cfg(feature = "hol")]
    HolKernelInterface,
    /// Unknown import name.
    Unknown(String),
}

/// Check that every import name is a recognized kernel import.
/// Returns Ok(()) if valid, Err(name) for the first unknown import.
pub fn validate_container_imports(import_names: &[String]) -> Result<(), String> {
    for name in import_names {
        if let ImportKind::Unknown(s) = categorize_import(name) {
            return Err(s);
        }
    }
    Ok(())
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
    if name == "store" {
        return ImportKind::Store;
    }
    if name == "cov:sign/api" {
        return ImportKind::SignInterface;
    }
    if name == "generate-signer" {
        return ImportKind::GenerateSigner;
    }
    #[cfg(feature = "hol")]
    if name == "cov:hol/kernel" {
        return ImportKind::HolKernelInterface;
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
    #[allow(dead_code)] // stored for future use (read-only imports)
    has_store: bool,
}

impl ImportManifest {
    /// Classify all imports of a component and determine the static decision.
    fn classify(engine: &Engine, component: &Component) -> Self {
        let ty = component.component_type();

        let mut imports_attest = false;
        let mut link_deps: Vec<O256> = Vec::new();
        let mut copy_deps: Vec<(String, O256)> = Vec::new();
        let mut prove_deps: Vec<O256> = Vec::new();
        let mut has_store = false;

        for (name, _) in ty.imports(engine) {
            match categorize_import(name) {
                ImportKind::Attest => imports_attest = true,
                ImportKind::Link(hash) => link_deps.push(hash),
                ImportKind::Copy(hash) => copy_deps.push((name.to_string(), hash)),
                ImportKind::Prove(hash) => prove_deps.push(hash),
                ImportKind::Store => has_store = true,
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
            has_store,
        }
    }

    /// Check whether the component imports the `cov:sign/api` interface
    /// or the `generate-signer` host function.
    fn needs_sign_api(engine: &Engine, component: &Component) -> bool {
        let ty = component.component_type();
        ty.imports(engine).any(|(name, _)| {
            matches!(
                categorize_import(name),
                ImportKind::SignInterface | ImportKind::GenerateSigner
            )
        })
    }

    /// Check whether the component imports the `cov:hol/kernel` interface.
    #[cfg(feature = "hol")]
    fn needs_hol_api(engine: &Engine, component: &Component) -> bool {
        let ty = component.component_type();
        ty.imports(engine)
            .any(|(name, _)| matches!(categorize_import(name), ImportKind::HolKernelInterface))
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
    root_store: Arc<dyn KvStore>,
}

impl<'a> LinkScope<'a> {
    fn new(engine: &'a Engine) -> Self {
        LinkScope {
            engine,
            instance_cache: HashMap::new(),
            lazy_proves: HashMap::new(),
            root_store: Arc::new(MemoryKvStore::new()),
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

        build_linker(
            self.engine,
            component,
            blobs,
            &self.instance_cache,
            &self.lazy_proves,
            &copy_cache,
            &self.root_store,
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
            &self.root_store,
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
            &self.root_store,
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
            &child.root_store,
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
// Resource types (stored by O256 hash)
const TAG_BLOB: u8 = 0x20;
const TAG_NAME: u8 = 0x21;

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
                    "store: unsupported list element type: {elem:?}"
                ))),
            }
        }
        Type::Own(rt) | Type::Borrow(rt) => {
            if *rt == ResourceType::host::<BlobHandle>() {
                Ok(TAG_BLOB)
            } else if *rt == ResourceType::host::<NameHandle>() {
                Ok(TAG_NAME)
            } else {
                Err(wasmtime::Error::msg("store: unsupported resource type"))
            }
        }
        _ => Err(wasmtime::Error::msg(format!(
            "store: unsupported type: {ty:?}"
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
            "store: unknown type tag {tag:#x}"
        ))),
    }
}

/// Serialize a store key/value, handling resource types (blob, name) by hash.
fn serialize_store_val(
    val: &Val,
    cx: &mut StoreContextMut<'_, HostState>,
) -> wasmtime::Result<Vec<u8>> {
    match val {
        Val::Resource(ra) => {
            // Try blob first
            if let Ok(resource) = ra.try_into_resource::<BlobHandle>(&mut *cx) {
                let hash = cx.data().table.get(&resource)?.hash;
                let mut buf = vec![TAG_BLOB];
                buf.extend_from_slice(hash.as_bytes());
                return Ok(buf);
            }
            // Try name
            if let Ok(resource) = ra.try_into_resource::<NameHandle>(&mut *cx) {
                let hash = cx.data().table.get(&resource)?.hash;
                let mut buf = vec![TAG_NAME];
                buf.extend_from_slice(hash.as_bytes());
                return Ok(buf);
            }
            Err(wasmtime::Error::msg("store: unsupported resource type"))
        }
        _ => serialize_val(val),
    }
}

/// Deserialize a store value, creating resource handles for blob/name types.
fn deserialize_store_val(
    bytes: &[u8],
    cx: &mut StoreContextMut<'_, HostState>,
    blobs: &BlobStore<O256>,
) -> wasmtime::Result<Val> {
    if bytes.is_empty() {
        return Err(wasmtime::Error::msg("store: empty serialized value"));
    }
    match bytes[0] {
        TAG_BLOB => {
            let hash_bytes: [u8; 32] = bytes[1..33]
                .try_into()
                .map_err(|_| wasmtime::Error::msg("store: truncated blob hash"))?;
            let hash = O256::from_bytes(hash_bytes);
            let data = blobs.get(&hash);
            let handle = BlobHandle { hash, data };
            let resource = cx.data_mut().table.push(handle)?;
            Ok(Val::Resource(ResourceAny::try_from_resource(resource, cx)?))
        }
        TAG_NAME => {
            let hash_bytes: [u8; 32] = bytes[1..33]
                .try_into()
                .map_err(|_| wasmtime::Error::msg("store: truncated name hash"))?;
            let hash = O256::from_bytes(hash_bytes);
            let handle = NameHandle { hash };
            let resource = cx.data_mut().table.push(handle)?;
            Ok(Val::Resource(ResourceAny::try_from_resource(resource, cx)?))
        }
        _ => deserialize_val(bytes),
    }
}

// ---------------------------------------------------------------------------
// build_linker — free function (avoids borrow conflicts)
// ---------------------------------------------------------------------------

/// Serialize a HOL type to a canonical byte representation.
#[cfg(feature = "hol")]
fn hol_type_to_bytes(arena: &covalence_hol::HolArena, ty: covalence_hol::TypeId) -> Vec<u8> {
    let mut buf = Vec::new();
    hol_type_to_bytes_acc(arena, ty, &mut buf);
    buf
}

#[cfg(feature = "hol")]
fn hol_type_to_bytes_acc(
    arena: &covalence_hol::HolArena,
    ty: covalence_hol::TypeId,
    buf: &mut Vec<u8>,
) {
    match arena.get_type(ty) {
        covalence_hol::HolTypeDef::Tyvar(n) => {
            buf.push(0);
            buf.extend_from_slice(&n.to_le_bytes());
        }
        covalence_hol::HolTypeDef::Tyapp(n, args) => {
            buf.push(1);
            buf.extend_from_slice(&n.to_le_bytes());
            buf.extend_from_slice(&(args.len() as u32).to_le_bytes());
            for arg in args {
                hol_type_to_bytes_acc(arena, arg, buf);
            }
        }
    }
}

/// Serialize a HOL term to a canonical byte representation.
#[cfg(feature = "hol")]
fn hol_term_to_bytes(arena: &covalence_hol::HolArena, tm: covalence_hol::TermId) -> Vec<u8> {
    let mut buf = Vec::new();
    hol_term_to_bytes_acc(arena, tm, &mut buf);
    buf
}

#[cfg(feature = "hol")]
fn hol_term_to_bytes_acc(
    arena: &covalence_hol::HolArena,
    tm: covalence_hol::TermId,
    buf: &mut Vec<u8>,
) {
    match arena.get_term(tm) {
        covalence_hol::TermDef::Var(n, ty) => {
            buf.push(0);
            buf.extend_from_slice(&n.to_le_bytes());
            hol_type_to_bytes_acc(arena, ty, buf);
        }
        covalence_hol::TermDef::Const(n, ty) => {
            buf.push(1);
            buf.extend_from_slice(&n.to_le_bytes());
            hol_type_to_bytes_acc(arena, ty, buf);
        }
        covalence_hol::TermDef::Comb(f, x) => {
            buf.push(2);
            hol_term_to_bytes_acc(arena, f, buf);
            hol_term_to_bytes_acc(arena, x, buf);
        }
        covalence_hol::TermDef::Abs(v, b) => {
            buf.push(3);
            hol_term_to_bytes_acc(arena, v, buf);
            hol_term_to_bytes_acc(arena, b, buf);
        }
    }
}

/// Extract a `ResourceAny` from a `Val::Resource`.
fn extract_resource(val: &Val) -> wasmtime::Result<ResourceAny> {
    match val {
        Val::Resource(r) => Ok(*r),
        _ => Err(wasmtime::Error::msg("expected resource")),
    }
}

/// Build a linker for a component, wiring up attest, blob, link, copy,
/// prove, and store imports.
fn build_linker(
    engine: &Engine,
    component: &Component,
    blobs: &BlobStore<O256>,
    instance_cache: &HashMap<O256, Vec<(String, Func)>>,
    lazy_proves: &HashMap<O256, Arc<LazyProve>>,
    copy_cache: &HashMap<String, Vec<(String, Func)>>,
    root_store: &Arc<dyn KvStore>,
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

    // Register the cov:sign/api interface if the component imports it
    // (directly or via generate-signer).
    let needs_sign_api = ImportManifest::needs_sign_api(engine, component);

    if needs_sign_api {
        // sign API implies blob API — ensure cov:blob/api is always registered.
        // (The blob API was already registered above if needs_api was true.
        //  If not, this is a sign-only component — blob types are still needed
        //  for the sign/verify methods that take borrow<blob>.)

        let principal_ty = ResourceType::host::<PrincipalHandle>();
        let signature_ty = ResourceType::host::<SignatureHandle>();
        let signer_ty = ResourceType::host::<SignerHandle>();

        let mut root = linker.root();
        let mut api = root
            .instance("cov:sign/api")
            .map_err(|e| DecideError::LinkError(e.to_string()))?;

        // --- principal resource ---
        api.resource(
            "principal",
            principal_ty,
            |mut cx: StoreContextMut<'_, HostState>, rep| {
                cx.data_mut()
                    .table
                    .delete(Resource::<PrincipalHandle>::new_own(rep))?;
                Ok(())
            },
        )
        .map_err(|e| DecideError::LinkError(e.to_string()))?;

        // [constructor]principal: (list<u8>) -> own<principal>
        api.func_wrap(
            "[constructor]principal",
            |mut cx: StoreContextMut<'_, HostState>,
             (bytes,): (Vec<u8>,)|
             -> wasmtime::Result<(Resource<PrincipalHandle>,)> {
                let key_bytes: [u8; 32] = bytes
                    .as_slice()
                    .try_into()
                    .map_err(|_| wasmtime::Error::msg("principal: expected exactly 32 bytes"))?;
                let key = covalence_sig::VerifyingKey::from_bytes(&key_bytes)
                    .map_err(|e| wasmtime::Error::msg(format!("invalid public key: {e}")))?;
                let handle = PrincipalHandle { key };
                let resource = cx.data_mut().table.push(handle)?;
                Ok((resource,))
            },
        )
        .map_err(|e| DecideError::LinkError(e.to_string()))?;

        // [method]principal.bytes: (borrow<principal>) -> list<u8>
        api.func_wrap(
            "[method]principal.bytes",
            |cx: StoreContextMut<'_, HostState>,
             (principal,): (Resource<PrincipalHandle>,)|
             -> wasmtime::Result<(Vec<u8>,)> {
                let handle = cx.data().table.get(&principal)?;
                Ok((handle.key.to_bytes().to_vec(),))
            },
        )
        .map_err(|e| DecideError::LinkError(e.to_string()))?;

        // [method]principal.eq: (borrow<principal>, borrow<principal>) -> bool
        api.func_wrap(
            "[method]principal.eq",
            |cx: StoreContextMut<'_, HostState>,
             (a, b): (Resource<PrincipalHandle>, Resource<PrincipalHandle>)|
             -> wasmtime::Result<(bool,)> {
                let ka = cx.data().table.get(&a)?.key;
                let kb = cx.data().table.get(&b)?.key;
                Ok((ka == kb,))
            },
        )
        .map_err(|e| DecideError::LinkError(e.to_string()))?;

        // --- signature resource (opaque) ---
        api.resource(
            "signature",
            signature_ty,
            |mut cx: StoreContextMut<'_, HostState>, rep| {
                cx.data_mut()
                    .table
                    .delete(Resource::<SignatureHandle>::new_own(rep))?;
                Ok(())
            },
        )
        .map_err(|e| DecideError::LinkError(e.to_string()))?;

        // [method]signature.verify: (borrow<signature>, borrow<principal>, borrow<blob>) -> bool
        api.func_wrap(
            "[method]signature.verify",
            |cx: StoreContextMut<'_, HostState>,
             (sig_res, principal_res, blob_res): (
                Resource<SignatureHandle>,
                Resource<PrincipalHandle>,
                Resource<BlobHandle>,
            )|
             -> wasmtime::Result<(bool,)> {
                let sig = cx.data().table.get(&sig_res)?.sig;
                let key = cx.data().table.get(&principal_res)?.key;
                let hash = cx.data().table.get(&blob_res)?.hash;
                let result = covalence_sig::Verifier::verify(&key, hash.as_bytes(), &sig);
                Ok((result.is_ok(),))
            },
        )
        .map_err(|e| DecideError::LinkError(e.to_string()))?;

        // --- signer resource ---
        api.resource(
            "signer",
            signer_ty,
            |mut cx: StoreContextMut<'_, HostState>, rep| {
                cx.data_mut()
                    .table
                    .delete(Resource::<SignerHandle>::new_own(rep))?;
                Ok(())
            },
        )
        .map_err(|e| DecideError::LinkError(e.to_string()))?;

        // [method]signer.principal: (borrow<signer>) -> own<principal>
        api.func_wrap(
            "[method]signer.principal",
            |mut cx: StoreContextMut<'_, HostState>,
             (signer_res,): (Resource<SignerHandle>,)|
             -> wasmtime::Result<(Resource<PrincipalHandle>,)> {
                let verifying_key = cx.data().table.get(&signer_res)?.key.verifying_key();
                let handle = PrincipalHandle { key: verifying_key };
                let resource = cx.data_mut().table.push(handle)?;
                Ok((resource,))
            },
        )
        .map_err(|e| DecideError::LinkError(e.to_string()))?;

        // [method]signer.sign: (borrow<signer>, borrow<blob>) -> own<signature>
        api.func_wrap(
            "[method]signer.sign",
            |mut cx: StoreContextMut<'_, HostState>,
             (signer_res, blob_res): (Resource<SignerHandle>, Resource<BlobHandle>)|
             -> wasmtime::Result<(Resource<SignatureHandle>,)> {
                let signing_key = &cx.data().table.get(&signer_res)?.key;
                let hash = cx.data().table.get(&blob_res)?.hash;
                let sig = covalence_sig::Signer::sign(signing_key, hash.as_bytes());
                let handle = SignatureHandle { sig };
                let resource = cx.data_mut().table.push(handle)?;
                Ok((resource,))
            },
        )
        .map_err(|e| DecideError::LinkError(e.to_string()))?;
    }

    // Register the cov:hol/kernel interface if the component imports it.
    #[cfg(feature = "hol")]
    {
        use covalence_hol::{HolLightKernel, HolLightTerms, HolLightTypes};

        if ImportManifest::needs_hol_api(engine, component) {
            let kernel = Arc::new(Mutex::new(covalence_hol::HolKernel::new(
                covalence_hol::FUN_TYCON_ID,
                covalence_hol::BOOL_TYCON_ID,
                covalence_hol::EQ_CONST_ID,
            )));
            let names = Arc::new(Mutex::new(covalence_opentheory::NameTable::new()));

            let hol_type_ty = ResourceType::host::<HolTypeHandle>();
            let term_res_ty = ResourceType::host::<TermHandle>();
            let thm_res_ty = ResourceType::host::<ThmHandle>();

            let mut root = linker.root();
            let mut api = root
                .instance("cov:hol/kernel")
                .map_err(|e| DecideError::LinkError(e.to_string()))?;

            // --- hol-type resource ---
            api.resource(
                "hol-type",
                hol_type_ty,
                |mut cx: StoreContextMut<'_, HostState>, rep| {
                    cx.data_mut()
                        .table
                        .delete(Resource::<HolTypeHandle>::new_own(rep))?;
                    Ok(())
                },
            )
            .map_err(|e| DecideError::LinkError(e.to_string()))?;

            // --- term resource ---
            api.resource(
                "term",
                term_res_ty,
                |mut cx: StoreContextMut<'_, HostState>, rep| {
                    cx.data_mut()
                        .table
                        .delete(Resource::<TermHandle>::new_own(rep))?;
                    Ok(())
                },
            )
            .map_err(|e| DecideError::LinkError(e.to_string()))?;

            // --- thm resource ---
            api.resource(
                "thm",
                thm_res_ty,
                |mut cx: StoreContextMut<'_, HostState>, rep| {
                    cx.data_mut()
                        .table
                        .delete(Resource::<ThmHandle>::new_own(rep))?;
                    Ok(())
                },
            )
            .map_err(|e| DecideError::LinkError(e.to_string()))?;

            // [method]hol-type.to-bytes: (borrow<hol-type>) -> list<u8>
            {
                let kernel = kernel.clone();
                api.func_wrap(
                    "[method]hol-type.to-bytes",
                    move |cx: StoreContextMut<'_, HostState>,
                          (ty_res,): (Resource<HolTypeHandle>,)|
                          -> wasmtime::Result<(Vec<u8>,)> {
                        let ty = cx.data().table.get(&ty_res)?.ty;
                        let k = kernel.lock().unwrap();
                        Ok((hol_type_to_bytes(k.arena(), ty),))
                    },
                )
                .map_err(|e| DecideError::LinkError(e.to_string()))?;
            }

            // [method]hol-type.eq: (borrow<hol-type>, borrow<hol-type>) -> bool
            {
                let kernel = kernel.clone();
                api.func_wrap(
                    "[method]hol-type.eq",
                    move |cx: StoreContextMut<'_, HostState>,
                          (a, b): (Resource<HolTypeHandle>, Resource<HolTypeHandle>)|
                          -> wasmtime::Result<(bool,)> {
                        let ty_a = cx.data().table.get(&a)?.ty;
                        let ty_b = cx.data().table.get(&b)?.ty;
                        let k = kernel.lock().unwrap();
                        Ok((k.type_eq(ty_a, ty_b),))
                    },
                )
                .map_err(|e| DecideError::LinkError(e.to_string()))?;
            }

            // [method]term.to-bytes: (borrow<term>) -> list<u8>
            {
                let kernel = kernel.clone();
                api.func_wrap(
                    "[method]term.to-bytes",
                    move |cx: StoreContextMut<'_, HostState>,
                          (tm_res,): (Resource<TermHandle>,)|
                          -> wasmtime::Result<(Vec<u8>,)> {
                        let tm = cx.data().table.get(&tm_res)?.term;
                        let k = kernel.lock().unwrap();
                        Ok((hol_term_to_bytes(k.arena(), tm),))
                    },
                )
                .map_err(|e| DecideError::LinkError(e.to_string()))?;
            }

            // [method]term.eq: (borrow<term>, borrow<term>) -> bool
            {
                let kernel = kernel.clone();
                api.func_wrap(
                    "[method]term.eq",
                    move |cx: StoreContextMut<'_, HostState>,
                          (a, b): (Resource<TermHandle>, Resource<TermHandle>)|
                          -> wasmtime::Result<(bool,)> {
                        let tm_a = cx.data().table.get(&a)?.term;
                        let tm_b = cx.data().table.get(&b)?.term;
                        let k = kernel.lock().unwrap();
                        Ok((k.aconv(tm_a, tm_b),))
                    },
                )
                .map_err(|e| DecideError::LinkError(e.to_string()))?;
            }

            // [method]term.type-of: (borrow<term>) -> own<hol-type>
            {
                let kernel = kernel.clone();
                api.func_wrap(
                    "[method]term.type-of",
                    move |mut cx: StoreContextMut<'_, HostState>,
                          (tm_res,): (Resource<TermHandle>,)|
                          -> wasmtime::Result<(Resource<HolTypeHandle>,)> {
                        let tm = cx.data().table.get(&tm_res)?.term;
                        let ty = kernel.lock().unwrap().type_of(tm);
                        let handle = HolTypeHandle { ty };
                        let resource = cx.data_mut().table.push(handle)?;
                        Ok((resource,))
                    },
                )
                .map_err(|e| DecideError::LinkError(e.to_string()))?;
            }

            // [method]thm.hyps: (borrow<thm>) -> list<term>
            {
                let kernel = kernel.clone();
                api.func_new("[method]thm.hyps", move |mut cx, _ty, args, results| {
                    let resource_any = extract_resource(&args[0])?;
                    let resource = resource_any.try_into_resource::<ThmHandle>(&mut cx)?;
                    let thm = cx.data().table.get(&resource)?.thm;
                    let hyps = kernel.lock().unwrap().hyps(thm);
                    let mut term_vals = Vec::new();
                    for hyp in hyps {
                        let handle = TermHandle { term: hyp };
                        let r = cx.data_mut().table.push(handle)?;
                        term_vals.push(Val::Resource(ResourceAny::try_from_resource(r, &mut cx)?));
                    }
                    results[0] = Val::List(term_vals);
                    Ok(())
                })
                .map_err(|e| DecideError::LinkError(e.to_string()))?;
            }

            // [method]thm.concl: (borrow<thm>) -> own<term>
            {
                let kernel = kernel.clone();
                api.func_wrap(
                    "[method]thm.concl",
                    move |mut cx: StoreContextMut<'_, HostState>,
                          (thm_res,): (Resource<ThmHandle>,)|
                          -> wasmtime::Result<(Resource<TermHandle>,)> {
                        let thm = cx.data().table.get(&thm_res)?.thm;
                        let concl = kernel.lock().unwrap().concl(thm);
                        let handle = TermHandle { term: concl };
                        let resource = cx.data_mut().table.push(handle)?;
                        Ok((resource,))
                    },
                )
                .map_err(|e| DecideError::LinkError(e.to_string()))?;
            }

            // --- type constructors ---

            // tyvar: (string) -> own<hol-type>
            {
                let kernel = kernel.clone();
                let names = names.clone();
                api.func_wrap(
                    "tyvar",
                    move |mut cx: StoreContextMut<'_, HostState>,
                          (name,): (String,)|
                          -> wasmtime::Result<(Resource<HolTypeHandle>,)> {
                        let name_id = names.lock().unwrap().intern_str(&name);
                        let ty = kernel.lock().unwrap().mk_tyvar(name_id);
                        let handle = HolTypeHandle { ty };
                        let resource = cx.data_mut().table.push(handle)?;
                        Ok((resource,))
                    },
                )
                .map_err(|e| DecideError::LinkError(e.to_string()))?;
            }

            // tyapp: (string, list<borrow<hol-type>>) -> own<hol-type>
            {
                let kernel = kernel.clone();
                let names = names.clone();
                api.func_new("tyapp", move |mut cx, _ty, args, results| {
                    let name = match &args[0] {
                        Val::String(s) => s.clone(),
                        _ => return Err(wasmtime::Error::msg("tyapp: expected string")),
                    };
                    let name_id = names.lock().unwrap().intern_str(&name);
                    let arg_list = match &args[1] {
                        Val::List(l) => l.clone(),
                        _ => return Err(wasmtime::Error::msg("tyapp: expected list")),
                    };
                    let mut type_args = Vec::new();
                    for arg_val in &arg_list {
                        let ra = extract_resource(arg_val)?;
                        let r = ra.try_into_resource::<HolTypeHandle>(&mut cx)?;
                        type_args.push(cx.data().table.get(&r)?.ty);
                    }
                    let result_ty = kernel
                        .lock()
                        .unwrap()
                        .mk_type_validated(name_id, type_args)
                        .map_err(|e| wasmtime::Error::msg(format!("tyapp: {e}")))?;
                    let handle = HolTypeHandle { ty: result_ty };
                    let r = cx.data_mut().table.push(handle)?;
                    results[0] = Val::Resource(ResourceAny::try_from_resource(r, &mut cx)?);
                    Ok(())
                })
                .map_err(|e| DecideError::LinkError(e.to_string()))?;
            }

            // bool-type: () -> own<hol-type>
            {
                let kernel = kernel.clone();
                api.func_wrap(
                    "bool-type",
                    move |mut cx: StoreContextMut<'_, HostState>,
                          _args: ()|
                          -> wasmtime::Result<(Resource<HolTypeHandle>,)> {
                        let ty = kernel.lock().unwrap().bool_type();
                        let handle = HolTypeHandle { ty };
                        let resource = cx.data_mut().table.push(handle)?;
                        Ok((resource,))
                    },
                )
                .map_err(|e| DecideError::LinkError(e.to_string()))?;
            }

            // fun-type: (borrow<hol-type>, borrow<hol-type>) -> own<hol-type>
            {
                let kernel = kernel.clone();
                api.func_wrap(
                    "fun-type",
                    move |mut cx: StoreContextMut<'_, HostState>,
                          (dom, cod): (Resource<HolTypeHandle>, Resource<HolTypeHandle>)|
                          -> wasmtime::Result<(Resource<HolTypeHandle>,)> {
                        let dom_ty = cx.data().table.get(&dom)?.ty;
                        let cod_ty = cx.data().table.get(&cod)?.ty;
                        let ty = kernel.lock().unwrap().fun_type(dom_ty, cod_ty);
                        let handle = HolTypeHandle { ty };
                        let resource = cx.data_mut().table.push(handle)?;
                        Ok((resource,))
                    },
                )
                .map_err(|e| DecideError::LinkError(e.to_string()))?;
            }

            // --- term constructors ---

            // mk-var: (string, borrow<hol-type>) -> own<term>
            {
                let kernel = kernel.clone();
                let names = names.clone();
                api.func_wrap(
                    "mk-var",
                    move |mut cx: StoreContextMut<'_, HostState>,
                          (name, ty_res): (String, Resource<HolTypeHandle>)|
                          -> wasmtime::Result<(Resource<TermHandle>,)> {
                        let name_id = names.lock().unwrap().intern_str(&name);
                        let ty = cx.data().table.get(&ty_res)?.ty;
                        let term = kernel.lock().unwrap().mk_var(name_id, ty);
                        let handle = TermHandle { term };
                        let resource = cx.data_mut().table.push(handle)?;
                        Ok((resource,))
                    },
                )
                .map_err(|e| DecideError::LinkError(e.to_string()))?;
            }

            // mk-const: (string, borrow<hol-type>) -> own<term>
            {
                let kernel = kernel.clone();
                let names = names.clone();
                api.func_wrap(
                    "mk-const",
                    move |mut cx: StoreContextMut<'_, HostState>,
                          (name, ty_res): (String, Resource<HolTypeHandle>)|
                          -> wasmtime::Result<(Resource<TermHandle>,)> {
                        let name_id = names.lock().unwrap().intern_str(&name);
                        let ty = cx.data().table.get(&ty_res)?.ty;
                        let term = kernel
                            .lock()
                            .unwrap()
                            .mk_const_validated(name_id, ty)
                            .map_err(|e| wasmtime::Error::msg(format!("mk-const: {e}")))?;
                        let handle = TermHandle { term };
                        let resource = cx.data_mut().table.push(handle)?;
                        Ok((resource,))
                    },
                )
                .map_err(|e| DecideError::LinkError(e.to_string()))?;
            }

            // mk-comb: (borrow<term>, borrow<term>) -> own<term>
            {
                let kernel = kernel.clone();
                api.func_wrap(
                    "mk-comb",
                    move |mut cx: StoreContextMut<'_, HostState>,
                          (f, x): (Resource<TermHandle>, Resource<TermHandle>)|
                          -> wasmtime::Result<(Resource<TermHandle>,)> {
                        let f_term = cx.data().table.get(&f)?.term;
                        let x_term = cx.data().table.get(&x)?.term;
                        let term = kernel.lock().unwrap().mk_comb(f_term, x_term);
                        let handle = TermHandle { term };
                        let resource = cx.data_mut().table.push(handle)?;
                        Ok((resource,))
                    },
                )
                .map_err(|e| DecideError::LinkError(e.to_string()))?;
            }

            // mk-abs: (borrow<term>, borrow<term>) -> own<term>
            {
                let kernel = kernel.clone();
                api.func_wrap(
                    "mk-abs",
                    move |mut cx: StoreContextMut<'_, HostState>,
                          (var, body): (Resource<TermHandle>, Resource<TermHandle>)|
                          -> wasmtime::Result<(Resource<TermHandle>,)> {
                        let var_term = cx.data().table.get(&var)?.term;
                        let body_term = cx.data().table.get(&body)?.term;
                        let term = kernel.lock().unwrap().mk_abs(var_term, body_term);
                        let handle = TermHandle { term };
                        let resource = cx.data_mut().table.push(handle)?;
                        Ok((resource,))
                    },
                )
                .map_err(|e| DecideError::LinkError(e.to_string()))?;
            }

            // mk-eq: (borrow<term>, borrow<term>) -> own<term>
            {
                let kernel = kernel.clone();
                api.func_wrap(
                    "mk-eq",
                    move |mut cx: StoreContextMut<'_, HostState>,
                          (lhs, rhs): (Resource<TermHandle>, Resource<TermHandle>)|
                          -> wasmtime::Result<(Resource<TermHandle>,)> {
                        let lhs_term = cx.data().table.get(&lhs)?.term;
                        let rhs_term = cx.data().table.get(&rhs)?.term;
                        let term = kernel.lock().unwrap().mk_eq(lhs_term, rhs_term);
                        let handle = TermHandle { term };
                        let resource = cx.data_mut().table.push(handle)?;
                        Ok((resource,))
                    },
                )
                .map_err(|e| DecideError::LinkError(e.to_string()))?;
            }

            // --- 10 inference rules ---

            // refl: (borrow<term>) -> own<thm>
            {
                let kernel = kernel.clone();
                api.func_wrap(
                    "refl",
                    move |mut cx: StoreContextMut<'_, HostState>,
                          (tm,): (Resource<TermHandle>,)|
                          -> wasmtime::Result<(Resource<ThmHandle>,)> {
                        let term = cx.data().table.get(&tm)?.term;
                        let thm = kernel
                            .lock()
                            .unwrap()
                            .refl(term)
                            .map_err(|e| wasmtime::Error::msg(format!("refl: {e}")))?;
                        let handle = ThmHandle { thm };
                        let resource = cx.data_mut().table.push(handle)?;
                        Ok((resource,))
                    },
                )
                .map_err(|e| DecideError::LinkError(e.to_string()))?;
            }

            // trans: (borrow<thm>, borrow<thm>) -> own<thm>
            {
                let kernel = kernel.clone();
                api.func_wrap(
                    "trans",
                    move |mut cx: StoreContextMut<'_, HostState>,
                          (th1, th2): (Resource<ThmHandle>, Resource<ThmHandle>)|
                          -> wasmtime::Result<(Resource<ThmHandle>,)> {
                        let thm1 = cx.data().table.get(&th1)?.thm;
                        let thm2 = cx.data().table.get(&th2)?.thm;
                        let result = kernel
                            .lock()
                            .unwrap()
                            .trans(thm1, thm2)
                            .map_err(|e| wasmtime::Error::msg(format!("trans: {e}")))?;
                        let handle = ThmHandle { thm: result };
                        let resource = cx.data_mut().table.push(handle)?;
                        Ok((resource,))
                    },
                )
                .map_err(|e| DecideError::LinkError(e.to_string()))?;
            }

            // mk-comb-rule: (borrow<thm>, borrow<thm>) -> own<thm>
            {
                let kernel = kernel.clone();
                api.func_wrap(
                    "mk-comb-rule",
                    move |mut cx: StoreContextMut<'_, HostState>,
                          (th1, th2): (Resource<ThmHandle>, Resource<ThmHandle>)|
                          -> wasmtime::Result<(Resource<ThmHandle>,)> {
                        let thm1 = cx.data().table.get(&th1)?.thm;
                        let thm2 = cx.data().table.get(&th2)?.thm;
                        let result = kernel
                            .lock()
                            .unwrap()
                            .mk_comb_rule(thm1, thm2)
                            .map_err(|e| wasmtime::Error::msg(format!("mk-comb-rule: {e}")))?;
                        let handle = ThmHandle { thm: result };
                        let resource = cx.data_mut().table.push(handle)?;
                        Ok((resource,))
                    },
                )
                .map_err(|e| DecideError::LinkError(e.to_string()))?;
            }

            // abs-rule: (borrow<term>, borrow<thm>) -> own<thm>
            {
                let kernel = kernel.clone();
                api.func_wrap(
                    "abs-rule",
                    move |mut cx: StoreContextMut<'_, HostState>,
                          (var, th): (Resource<TermHandle>, Resource<ThmHandle>)|
                          -> wasmtime::Result<(Resource<ThmHandle>,)> {
                        let var_term = cx.data().table.get(&var)?.term;
                        let thm = cx.data().table.get(&th)?.thm;
                        let result = kernel
                            .lock()
                            .unwrap()
                            .abs_rule(var_term, thm)
                            .map_err(|e| wasmtime::Error::msg(format!("abs-rule: {e}")))?;
                        let handle = ThmHandle { thm: result };
                        let resource = cx.data_mut().table.push(handle)?;
                        Ok((resource,))
                    },
                )
                .map_err(|e| DecideError::LinkError(e.to_string()))?;
            }

            // beta-conv: (borrow<term>) -> own<thm>
            {
                let kernel = kernel.clone();
                api.func_wrap(
                    "beta-conv",
                    move |mut cx: StoreContextMut<'_, HostState>,
                          (tm,): (Resource<TermHandle>,)|
                          -> wasmtime::Result<(Resource<ThmHandle>,)> {
                        let term = cx.data().table.get(&tm)?.term;
                        let thm = kernel
                            .lock()
                            .unwrap()
                            .beta_conv(term)
                            .map_err(|e| wasmtime::Error::msg(format!("beta-conv: {e}")))?;
                        let handle = ThmHandle { thm };
                        let resource = cx.data_mut().table.push(handle)?;
                        Ok((resource,))
                    },
                )
                .map_err(|e| DecideError::LinkError(e.to_string()))?;
            }

            // assume-rule: (borrow<term>) -> own<thm>
            {
                let kernel = kernel.clone();
                api.func_wrap(
                    "assume-rule",
                    move |mut cx: StoreContextMut<'_, HostState>,
                          (tm,): (Resource<TermHandle>,)|
                          -> wasmtime::Result<(Resource<ThmHandle>,)> {
                        let term = cx.data().table.get(&tm)?.term;
                        let thm = kernel
                            .lock()
                            .unwrap()
                            .assume_rule(term)
                            .map_err(|e| wasmtime::Error::msg(format!("assume-rule: {e}")))?;
                        let handle = ThmHandle { thm };
                        let resource = cx.data_mut().table.push(handle)?;
                        Ok((resource,))
                    },
                )
                .map_err(|e| DecideError::LinkError(e.to_string()))?;
            }

            // eq-mp: (borrow<thm>, borrow<thm>) -> own<thm>
            {
                let kernel = kernel.clone();
                api.func_wrap(
                    "eq-mp",
                    move |mut cx: StoreContextMut<'_, HostState>,
                          (th1, th2): (Resource<ThmHandle>, Resource<ThmHandle>)|
                          -> wasmtime::Result<(Resource<ThmHandle>,)> {
                        let thm1 = cx.data().table.get(&th1)?.thm;
                        let thm2 = cx.data().table.get(&th2)?.thm;
                        let result = kernel
                            .lock()
                            .unwrap()
                            .eq_mp(thm1, thm2)
                            .map_err(|e| wasmtime::Error::msg(format!("eq-mp: {e}")))?;
                        let handle = ThmHandle { thm: result };
                        let resource = cx.data_mut().table.push(handle)?;
                        Ok((resource,))
                    },
                )
                .map_err(|e| DecideError::LinkError(e.to_string()))?;
            }

            // deduct-antisym: (borrow<thm>, borrow<thm>) -> own<thm>
            {
                let kernel = kernel.clone();
                api.func_wrap(
                    "deduct-antisym",
                    move |mut cx: StoreContextMut<'_, HostState>,
                          (th1, th2): (Resource<ThmHandle>, Resource<ThmHandle>)|
                          -> wasmtime::Result<(Resource<ThmHandle>,)> {
                        let thm1 = cx.data().table.get(&th1)?.thm;
                        let thm2 = cx.data().table.get(&th2)?.thm;
                        let result = kernel
                            .lock()
                            .unwrap()
                            .deduct_antisym(thm1, thm2)
                            .map_err(|e| wasmtime::Error::msg(format!("deduct-antisym: {e}")))?;
                        let handle = ThmHandle { thm: result };
                        let resource = cx.data_mut().table.push(handle)?;
                        Ok((resource,))
                    },
                )
                .map_err(|e| DecideError::LinkError(e.to_string()))?;
            }

            // inst-term: (list<tuple<borrow<term>, borrow<term>>>, borrow<thm>) -> own<thm>
            {
                let kernel = kernel.clone();
                api.func_new("inst-term", move |mut cx, _ty, args, results| {
                    let pairs_list = match &args[0] {
                        Val::List(l) => l.clone(),
                        _ => return Err(wasmtime::Error::msg("inst-term: expected list")),
                    };
                    let th_ra = extract_resource(&args[1])?;
                    let th_r = th_ra.try_into_resource::<ThmHandle>(&mut cx)?;
                    let thm = cx.data().table.get(&th_r)?.thm;

                    let mut pairs = Vec::new();
                    for pair_val in &pairs_list {
                        let tuple = match pair_val {
                            Val::Tuple(t) => t,
                            _ => return Err(wasmtime::Error::msg("inst-term: expected tuple")),
                        };
                        let new_ra = extract_resource(&tuple[0])?;
                        let new_r = new_ra.try_into_resource::<TermHandle>(&mut cx)?;
                        let new_term = cx.data().table.get(&new_r)?.term;
                        let old_ra = extract_resource(&tuple[1])?;
                        let old_r = old_ra.try_into_resource::<TermHandle>(&mut cx)?;
                        let old_term = cx.data().table.get(&old_r)?.term;
                        pairs.push((new_term, old_term));
                    }

                    let result = kernel
                        .lock()
                        .unwrap()
                        .inst_rule(&pairs, thm)
                        .map_err(|e| wasmtime::Error::msg(format!("inst-term: {e}")))?;
                    let handle = ThmHandle { thm: result };
                    let r = cx.data_mut().table.push(handle)?;
                    results[0] = Val::Resource(ResourceAny::try_from_resource(r, &mut cx)?);
                    Ok(())
                })
                .map_err(|e| DecideError::LinkError(e.to_string()))?;
            }

            // inst-type-rule: (list<tuple<borrow<hol-type>, borrow<hol-type>>>, borrow<thm>) -> own<thm>
            {
                let kernel = kernel.clone();
                api.func_new("inst-type-rule", move |mut cx, _ty, args, results| {
                    let pairs_list = match &args[0] {
                        Val::List(l) => l.clone(),
                        _ => return Err(wasmtime::Error::msg("inst-type-rule: expected list")),
                    };
                    let th_ra = extract_resource(&args[1])?;
                    let th_r = th_ra.try_into_resource::<ThmHandle>(&mut cx)?;
                    let thm = cx.data().table.get(&th_r)?.thm;

                    let mut pairs = Vec::new();
                    for pair_val in &pairs_list {
                        let tuple = match pair_val {
                            Val::Tuple(t) => t,
                            _ => {
                                return Err(wasmtime::Error::msg("inst-type-rule: expected tuple"));
                            }
                        };
                        let new_ra = extract_resource(&tuple[0])?;
                        let new_r = new_ra.try_into_resource::<HolTypeHandle>(&mut cx)?;
                        let new_ty = cx.data().table.get(&new_r)?.ty;
                        let old_ra = extract_resource(&tuple[1])?;
                        let old_r = old_ra.try_into_resource::<HolTypeHandle>(&mut cx)?;
                        let old_ty = cx.data().table.get(&old_r)?.ty;
                        let k = kernel.lock().unwrap();
                        let old_name = k.dest_tyvar(old_ty).ok_or_else(|| {
                            wasmtime::Error::msg("inst-type-rule: old type must be a type variable")
                        })?;
                        drop(k);
                        pairs.push((new_ty, old_name));
                    }

                    let result = kernel
                        .lock()
                        .unwrap()
                        .inst_type_rule(&pairs, thm)
                        .map_err(|e| wasmtime::Error::msg(format!("inst-type-rule: {e}")))?;
                    let handle = ThmHandle { thm: result };
                    let r = cx.data_mut().table.push(handle)?;
                    results[0] = Val::Resource(ResourceAny::try_from_resource(r, &mut cx)?);
                    Ok(())
                })
                .map_err(|e| DecideError::LinkError(e.to_string()))?;
            }

            // --- definitions ---

            // new-axiom: (borrow<term>) -> own<thm>
            {
                let kernel = kernel.clone();
                api.func_wrap(
                    "new-axiom",
                    move |mut cx: StoreContextMut<'_, HostState>,
                          (tm,): (Resource<TermHandle>,)|
                          -> wasmtime::Result<(Resource<ThmHandle>,)> {
                        let term = cx.data().table.get(&tm)?.term;
                        let thm = kernel
                            .lock()
                            .unwrap()
                            .new_axiom(term)
                            .map_err(|e| wasmtime::Error::msg(format!("new-axiom: {e}")))?;
                        let handle = ThmHandle { thm };
                        let resource = cx.data_mut().table.push(handle)?;
                        Ok((resource,))
                    },
                )
                .map_err(|e| DecideError::LinkError(e.to_string()))?;
            }

            // new-basic-definition: (borrow<term>) -> own<thm>
            {
                let kernel = kernel.clone();
                api.func_wrap(
                    "new-basic-definition",
                    move |mut cx: StoreContextMut<'_, HostState>,
                          (tm,): (Resource<TermHandle>,)|
                          -> wasmtime::Result<(Resource<ThmHandle>,)> {
                        let term = cx.data().table.get(&tm)?.term;
                        let thm =
                            kernel
                                .lock()
                                .unwrap()
                                .new_basic_definition(term)
                                .map_err(|e| {
                                    wasmtime::Error::msg(format!("new-basic-definition: {e}"))
                                })?;
                        let handle = ThmHandle { thm };
                        let resource = cx.data_mut().table.push(handle)?;
                        Ok((resource,))
                    },
                )
                .map_err(|e| DecideError::LinkError(e.to_string()))?;
            }

            // new-basic-type-definition: (string, string, string, borrow<thm>) -> tuple<thm, thm>
            {
                let kernel = kernel.clone();
                let names = names.clone();
                api.func_new(
                    "new-basic-type-definition",
                    move |mut cx, _ty, args, results| {
                        let tyname = match &args[0] {
                            Val::String(s) => s.clone(),
                            _ => {
                                return Err(wasmtime::Error::msg(
                                    "new-basic-type-definition: expected string",
                                ));
                            }
                        };
                        let abs_name = match &args[1] {
                            Val::String(s) => s.clone(),
                            _ => {
                                return Err(wasmtime::Error::msg(
                                    "new-basic-type-definition: expected string",
                                ));
                            }
                        };
                        let rep_name = match &args[2] {
                            Val::String(s) => s.clone(),
                            _ => {
                                return Err(wasmtime::Error::msg(
                                    "new-basic-type-definition: expected string",
                                ));
                            }
                        };
                        let th_ra = extract_resource(&args[3])?;
                        let th_r = th_ra.try_into_resource::<ThmHandle>(&mut cx)?;
                        let thm = cx.data().table.get(&th_r)?.thm;

                        let mut n = names.lock().unwrap();
                        let tyname_id = n.intern_str(&tyname);
                        let abs_id = n.intern_str(&abs_name);
                        let rep_id = n.intern_str(&rep_name);
                        drop(n);

                        let mut n = names.lock().unwrap();
                        let abs_var_name = n.intern_str("a");
                        let rep_var_name = n.intern_str("r");
                        drop(n);

                        let (thm1, thm2) = kernel
                            .lock()
                            .unwrap()
                            .new_basic_type_definition(
                                tyname_id,
                                abs_id,
                                rep_id,
                                abs_var_name,
                                rep_var_name,
                                thm,
                            )
                            .map_err(|e| {
                                wasmtime::Error::msg(format!("new-basic-type-definition: {e}"))
                            })?;

                        let h1 = ThmHandle { thm: thm1 };
                        let h2 = ThmHandle { thm: thm2 };
                        let r1 = cx.data_mut().table.push(h1)?;
                        let r2 = cx.data_mut().table.push(h2)?;
                        let ra1 = ResourceAny::try_from_resource(r1, &mut cx)?;
                        let ra2 = ResourceAny::try_from_resource(r2, &mut cx)?;
                        results[0] = Val::Tuple(vec![Val::Resource(ra1), Val::Resource(ra2)]);
                        Ok(())
                    },
                )
                .map_err(|e| DecideError::LinkError(e.to_string()))?;
            }
        }
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
            ImportKind::Store => {
                let store_ty = ResourceType::host::<StoreHandle>();
                let mut root = linker.root();
                let mut inst = root
                    .instance(name)
                    .map_err(|e| DecideError::LinkError(e.to_string()))?;

                // Register resource type with destructor
                inst.resource(
                    "store",
                    store_ty,
                    |mut cx: StoreContextMut<'_, HostState>, rep| {
                        cx.data_mut()
                            .table
                            .delete(Resource::<StoreHandle>::new_own(rep))?;
                        Ok(())
                    },
                )
                .map_err(|e| DecideError::LinkError(e.to_string()))?;

                // root() -> own<store>
                let root_for_root = root_store.clone();
                inst.func_new("root", move |mut cx, _ty, _args, results| {
                    let handle = StoreHandle {
                        data: root_for_root.clone(),
                        writable: true,
                    };
                    let resource = cx.data_mut().table.push(handle)?;
                    results[0] = Val::Resource(ResourceAny::try_from_resource(resource, &mut cx)?);
                    Ok(())
                })
                .map_err(|e| DecideError::LinkError(e.to_string()))?;

                // new() -> own<store>
                inst.func_new("new", move |mut cx, _ty, _args, results| {
                    let handle = StoreHandle {
                        data: Arc::new(MemoryKvStore::new()),
                        writable: true,
                    };
                    let resource = cx.data_mut().table.push(handle)?;
                    results[0] = Val::Resource(ResourceAny::try_from_resource(resource, &mut cx)?);
                    Ok(())
                })
                .map_err(|e| DecideError::LinkError(e.to_string()))?;

                // [method]store.set(borrow<store>, key, value)
                inst.func_new("[method]store.set", move |mut cx, ty, args, _results| {
                    let resource_any = extract_resource(&args[0])?;
                    let resource = resource_any.try_into_resource::<StoreHandle>(&mut cx)?;
                    let (data, writable) = {
                        let h = cx.data().table.get(&resource)?;
                        (h.data.clone(), h.writable)
                    };
                    if !writable {
                        return Err(wasmtime::Error::msg("store is read-only"));
                    }
                    let val_tag = component_type_to_tag(&ty.params().nth(2).unwrap().1)?;
                    let mut key = serialize_store_val(&args[1], &mut cx)?;
                    let bare_key = key.clone();
                    key.push(val_tag);
                    let value = serialize_store_val(&args[2], &mut cx)?;
                    data.touch(&bare_key);
                    data.set(&key, &value);
                    Ok(())
                })
                .map_err(|e| DecideError::LinkError(e.to_string()))?;

                // [method]store.get(borrow<store>, key) -> value
                {
                    let blobs_for_get = blobs.clone();
                    inst.func_new("[method]store.get", move |mut cx, ty, args, results| {
                        let resource_any = extract_resource(&args[0])?;
                        let resource = resource_any.try_into_resource::<StoreHandle>(&mut cx)?;
                        let data = cx.data().table.get(&resource)?.data.clone();
                        let val_tag = component_type_to_tag(&ty.results().next().unwrap())?;
                        let mut key = serialize_store_val(&args[1], &mut cx)?;
                        key.push(val_tag);
                        match data.get(&key) {
                            Some(v) => {
                                results[0] = deserialize_store_val(&v, &mut cx, &blobs_for_get)?;
                                Ok(())
                            }
                            None => Err(wasmtime::Error::msg("key not found in store")),
                        }
                    })
                    .map_err(|e| DecideError::LinkError(e.to_string()))?;
                }

                // [method]store.ns(borrow<store>, key) -> own<store>
                inst.func_new("[method]store.ns", move |mut cx, ty, args, results| {
                    let resource_any = extract_resource(&args[0])?;
                    let resource = resource_any.try_into_resource::<StoreHandle>(&mut cx)?;
                    let (parent_data, parent_writable) = {
                        let h = cx.data().table.get(&resource)?;
                        (h.data.clone(), h.writable)
                    };
                    let key_tag = component_type_to_tag(&ty.params().nth(1).unwrap().1)?;
                    let mut key = serialize_store_val(&args[1], &mut cx)?;
                    key.push(key_tag);
                    let child_data = parent_data.ns(&key);
                    let child = StoreHandle {
                        data: child_data,
                        writable: parent_writable,
                    };
                    let child_resource = cx.data_mut().table.push(child)?;
                    results[0] =
                        Val::Resource(ResourceAny::try_from_resource(child_resource, &mut cx)?);
                    Ok(())
                })
                .map_err(|e| DecideError::LinkError(e.to_string()))?;

                // [method]store.clone(borrow<store>) -> own<store>
                inst.func_new("[method]store.clone", move |mut cx, _ty, args, results| {
                    let resource_any = extract_resource(&args[0])?;
                    let resource = resource_any.try_into_resource::<StoreHandle>(&mut cx)?;
                    let (data, writable) = {
                        let h = cx.data().table.get(&resource)?;
                        (h.data.clone(), h.writable)
                    };
                    let cloned = StoreHandle {
                        data: data.dup(),
                        writable,
                    };
                    let cloned_resource = cx.data_mut().table.push(cloned)?;
                    results[0] =
                        Val::Resource(ResourceAny::try_from_resource(cloned_resource, &mut cx)?);
                    Ok(())
                })
                .map_err(|e| DecideError::LinkError(e.to_string()))?;

                // [method]store.read-only(borrow<store>) -> own<store>
                inst.func_new(
                    "[method]store.read-only",
                    move |mut cx, _ty, args, results| {
                        let resource_any = extract_resource(&args[0])?;
                        let resource = resource_any.try_into_resource::<StoreHandle>(&mut cx)?;
                        let data = cx.data().table.get(&resource)?.data.clone();
                        let frozen = StoreHandle {
                            data: data.dup(),
                            writable: false,
                        };
                        let frozen_resource = cx.data_mut().table.push(frozen)?;
                        results[0] = Val::Resource(ResourceAny::try_from_resource(
                            frozen_resource,
                            &mut cx,
                        )?);
                        Ok(())
                    },
                )
                .map_err(|e| DecideError::LinkError(e.to_string()))?;

                // [method]store.try-get(borrow<store>, key) -> option<value>
                {
                    let blobs_for_try_get = blobs.clone();
                    inst.func_new("[method]store.try-get", move |mut cx, ty, args, results| {
                        let resource_any = extract_resource(&args[0])?;
                        let resource = resource_any.try_into_resource::<StoreHandle>(&mut cx)?;
                        let data = cx.data().table.get(&resource)?.data.clone();
                        let result_ty = ty.results().next().unwrap();
                        let val_tag = match &result_ty {
                            wasmtime::component::types::Type::Option(opt) => {
                                component_type_to_tag(&opt.ty())?
                            }
                            _ => {
                                return Err(wasmtime::Error::msg(
                                    "try-get: expected option result",
                                ));
                            }
                        };
                        let mut key = serialize_store_val(&args[1], &mut cx)?;
                        key.push(val_tag);
                        match data.get(&key) {
                            Some(v) => {
                                let val = deserialize_store_val(&v, &mut cx, &blobs_for_try_get)?;
                                results[0] = Val::Option(Some(Box::new(val)));
                                Ok(())
                            }
                            None => {
                                results[0] = Val::Option(None);
                                Ok(())
                            }
                        }
                    })
                    .map_err(|e| DecideError::LinkError(e.to_string()))?;
                }

                // [method]store.assert-exists(borrow<store>, key)
                inst.func_new(
                    "[method]store.assert-exists",
                    move |mut cx, _ty, args, _results| {
                        let resource_any = extract_resource(&args[0])?;
                        let resource = resource_any.try_into_resource::<StoreHandle>(&mut cx)?;
                        let data = cx.data().table.get(&resource)?.data.clone();
                        let key = serialize_store_val(&args[1], &mut cx)?;
                        if !data.touched(&key) {
                            return Err(wasmtime::Error::msg("key does not exist in store"));
                        }
                        Ok(())
                    },
                )
                .map_err(|e| DecideError::LinkError(e.to_string()))?;

                // [method]store.try-exists(borrow<store>, key) -> bool
                inst.func_new(
                    "[method]store.try-exists",
                    move |mut cx, _ty, args, results| {
                        let resource_any = extract_resource(&args[0])?;
                        let resource = resource_any.try_into_resource::<StoreHandle>(&mut cx)?;
                        let data = cx.data().table.get(&resource)?.data.clone();
                        let key = serialize_store_val(&args[1], &mut cx)?;
                        results[0] = Val::Bool(data.touched(&key));
                        Ok(())
                    },
                )
                .map_err(|e| DecideError::LinkError(e.to_string()))?;
            }
            ImportKind::SignInterface => {
                // Already registered above.
            }
            ImportKind::GenerateSigner => {
                linker
                    .root()
                    .func_wrap(
                        name,
                        |mut cx: StoreContextMut<'_, HostState>,
                         _args: ()|
                         -> wasmtime::Result<(Resource<SignerHandle>,)> {
                            let key = covalence_sig::SigningKey::generate(
                                &mut covalence_sig::dalek_rand_core::OsRng,
                            );
                            let handle = SignerHandle { key };
                            let resource = cx.data_mut().table.push(handle)?;
                            Ok((resource,))
                        },
                    )
                    .map_err(|e| DecideError::LinkError(e.to_string()))?;
            }
            #[cfg(feature = "hol")]
            ImportKind::HolKernelInterface => {
                // Already registered above.
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
#[derive(Clone)]
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
    /// - `"store"`: a hierarchical key-value store resource with `root()`,
    ///   `new()`, `set(borrow, key, value)`, `get(borrow, key) → value`,
    ///   `try-get(borrow, key) → option<value>`,
    ///   `assert-exists(borrow, key)`, `try-exists(borrow, key) → option<()>`,
    ///   `ns(borrow, key) → own`, `clone(borrow) → own`, and
    ///   `read-only(borrow) → own`. Shared within a container (via `root`),
    ///   isolated across prove-dep boundaries. Strictly typed: each
    ///   (key\_type, value\_type) combination is disjoint.
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

impl crate::Evaluator<BlobStore<O256>> for WasmEngine {
    fn decide(
        &self,
        bytes: &[u8],
        store: &BlobStore<O256>,
    ) -> Result<DecideOutput, crate::KernelError> {
        self.decide(bytes, store)
            .map_err(|e| crate::KernelError::Engine(format!("{e}")))
    }
}
