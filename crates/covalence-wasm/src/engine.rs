use std::collections::{HashMap, HashSet};
use std::fmt;

use covalence_hash::O256;
use covalence_store::ContentStore;
use wasmtime::component::{Component, Func, Linker};
use wasmtime::{Engine, Module, Store};

use crate::parse::{ComponentInfo, ModuleInfo};

/// Host state threaded through wasmtime's Store.
struct HostState {
    attested: bool,
}

/// Result of deciding a proposition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PropResult {
    /// The proposition called `attest()` during startup — decidably true.
    True,
    /// The proposition imports `attest()` but did not call it during startup.
    /// It might still be provable by calling exported functions with the right arguments.
    Unknown,
    /// The proposition does not import `attest()` at all — statically false.
    /// (No sequence of calls can ever cause it to attest.)
    False,
}

impl fmt::Display for PropResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PropResult::True => write!(f, "true"),
            PropResult::Unknown => write!(f, "unknown"),
            PropResult::False => write!(f, "false"),
        }
    }
}

/// Categorized import from a proposition component.
#[derive(Debug)]
enum ImportKind {
    /// The `attest()` function.
    Attest,
    /// A blob by hash: "blob-{hex}".
    Blob(O256),
    /// A WASM module by hash: "module-{hex}".
    Module(O256),
    /// A component instance by hash: "component-{hash}".
    Component(O256),
    /// Unknown import name.
    Unknown(String),
}

fn categorize_import(name: &str) -> ImportKind {
    if name == "attest" {
        return ImportKind::Attest;
    }
    if let Some(hex) = name.strip_prefix("blob-") {
        if let Some(hash) = O256::from_hex(hex) {
            return ImportKind::Blob(hash);
        }
    }
    if let Some(hex) = name.strip_prefix("module-") {
        if let Some(hash) = O256::from_hex(hex) {
            return ImportKind::Module(hash);
        }
    }
    if let Some(hex) = name.strip_prefix("component-") {
        if let Some(hash) = O256::from_hex(hex) {
            return ImportKind::Component(hash);
        }
    }
    ImportKind::Unknown(name.to_string())
}

/// WASM engine backed by wasmtime.
pub struct WasmEngine {
    engine: Engine,
}

impl WasmEngine {
    pub fn new() -> Result<Self, wasmtime::Error> {
        let engine = Engine::default();
        Ok(WasmEngine { engine })
    }

    /// Validate bytes as a core WASM module and return info about it.
    pub fn parse_module(&self, bytes: &[u8]) -> Result<ModuleInfo, wasmtime::Error> {
        let module = Module::new(&self.engine, bytes)?;
        let imports = module
            .imports()
            .map(|i| (i.module().to_string(), i.name().to_string()))
            .collect();
        let exports = module.exports().map(|e| e.name().to_string()).collect();
        Ok(ModuleInfo { imports, exports })
    }

    /// Validate bytes as a WASM component and return info about it.
    pub fn parse_component(&self, bytes: &[u8]) -> Result<ComponentInfo, wasmtime::Error> {
        let component = Component::new(&self.engine, bytes)?;
        let ty = component.component_type();
        let imports = ty
            .imports(&self.engine)
            .map(|(name, _)| name.to_string())
            .collect();
        let exports = ty
            .exports(&self.engine)
            .map(|(name, _)| name.to_string())
            .collect();
        Ok(ComponentInfo { imports, exports })
    }

    /// Decide if a proposition (WASM component) is true,
    /// i.e. whether its start function calls `attest()`.
    ///
    /// The component may import:
    /// - `"attest"`: a function that marks the proposition as true
    /// - `"blob-{hash}"`: a blob from the store (lazy — traps if data unavailable)
    /// - `"module-{hash}"`: a core WASM module from the store
    /// - `"component-{hash}"`: a component instance (linked recursively)
    ///
    /// Instance imports are resolved eagerly from the store.
    pub fn decide(
        &self,
        bytes: &[u8],
        blobs: &dyn ContentStore<O256>,
    ) -> Result<PropResult, PropError> {
        let component = Component::new(&self.engine, bytes)
            .map_err(|e| PropError::InvalidComponent(e.to_string()))?;

        let ty = component.component_type();

        // Classify all imports and collect dep hashes
        let mut imports_attest = false;
        let mut import_deps: Vec<O256> = Vec::new();
        for (name, _) in ty.imports(&self.engine) {
            match categorize_import(name) {
                ImportKind::Attest => imports_attest = true,
                ImportKind::Component(hash) => {
                    import_deps.push(hash);
                }
                _ => {}
            }
        }

        // Pre-check: if attest is not imported AND there are no deps that
        // could transitively attest, this prop is statically false
        if !imports_attest && import_deps.is_empty() {
            return Ok(PropResult::False);
        }

        let mut store = Store::new(&self.engine, HostState { attested: false });
        let mut instance_cache: HashMap<O256, Vec<(String, Func)>> = HashMap::new();
        let mut resolving: HashSet<O256> = HashSet::new();

        // Pre-resolve all import deps (instantiate them into the store)
        for dep_hash in &import_deps {
            self.resolve_import(
                dep_hash,
                blobs,
                &mut store,
                &mut instance_cache,
                &mut resolving,
            )?;
        }

        let linker = self.build_linker(&component, blobs, &instance_cache)?;

        // Instantiate the component — this runs the start function.
        // A trap during instantiation means the start function didn't complete;
        // if attest was already called before the trap, result is True,
        // otherwise Unknown (we can't determine the result).
        let instantiation = linker.instantiate(&mut store, &component);

        if instantiation.is_err() {
            return Ok(if store.data().attested {
                PropResult::True
            } else {
                PropResult::Unknown
            });
        }

        Ok(if store.data().attested {
            PropResult::True
        } else if imports_attest {
            // Imported attest but didn't call it during startup
            PropResult::Unknown
        } else {
            // No attest import, deps didn't transitively attest
            PropResult::False
        })
    }

    /// Build a linker for a component, wiring up attest, blob, and component imports.
    fn build_linker(
        &self,
        component: &Component,
        blobs: &dyn ContentStore<O256>,
        instance_cache: &HashMap<O256, Vec<(String, Func)>>,
    ) -> Result<Linker<HostState>, PropError> {
        let ty = component.component_type();
        let mut linker: Linker<HostState> = Linker::new(&self.engine);

        for (name, _) in ty.imports(&self.engine) {
            match categorize_import(name) {
                ImportKind::Attest => {
                    linker
                        .root()
                        .func_wrap(
                            name,
                            |mut cx: wasmtime::StoreContextMut<'_, HostState>, _args: ()| {
                                cx.data_mut().attested = true;
                                Ok(())
                            },
                        )
                        .map_err(|e| PropError::LinkError(e.to_string()))?;
                }
                ImportKind::Blob(hash) => {
                    let data = blobs.get(&hash);
                    linker
                        .root()
                        .func_wrap(
                            name,
                            move |_cx: wasmtime::StoreContextMut<'_, HostState>,
                                  _args: ()|
                                  -> wasmtime::Result<(Vec<u8>,)> {
                                match &data {
                                    Some(d) => Ok((d.clone(),)),
                                    None => Err(wasmtime::Error::msg("blob data not available")),
                                }
                            },
                        )
                        .map_err(|e| PropError::LinkError(e.to_string()))?;
                }
                ImportKind::Module(_hash) => {
                    // Module linking is complex — left unlinked.
                }
                ImportKind::Component(hash) => {
                    let exports = instance_cache.get(&hash).cloned().unwrap_or_default();

                    let mut root = linker.root();
                    let mut li = root
                        .instance(name)
                        .map_err(|e| PropError::LinkError(e.to_string()))?;

                    for (export_name, export_func) in exports {
                        li.func_new(&export_name, move |mut cx, _ty, args, results| {
                            export_func.call(&mut cx, args, results)?;
                            Ok(())
                        })
                        .map_err(|e| PropError::LinkError(e.to_string()))?;
                    }
                }
                ImportKind::Unknown(_) => {}
            }
        }

        Ok(linker)
    }

    /// Resolve a `component-{hash}` import: load, compile, and
    /// instantiate the dep component (recursively resolving its own deps).
    /// Caches instances by hash and detects cycles.
    fn resolve_import(
        &self,
        dep_hash: &O256,
        blobs: &dyn ContentStore<O256>,
        store: &mut Store<HostState>,
        instance_cache: &mut HashMap<O256, Vec<(String, Func)>>,
        resolving: &mut HashSet<O256>,
    ) -> Result<(), PropError> {
        // Check cache first
        if instance_cache.contains_key(dep_hash) {
            return Ok(());
        }

        // Cycle detection
        if !resolving.insert(*dep_hash) {
            return Err(PropError::CycleDetected(format!(
                "cycle detected resolving: {}",
                dep_hash
            )));
        }

        // Load bytes from store
        let dep_bytes = blobs
            .get(dep_hash)
            .ok_or_else(|| PropError::MissingDep(format!("blob not found: {}", dep_hash)))?;

        let dep_component = Component::new(&self.engine, &dep_bytes)
            .map_err(|e| PropError::InvalidComponent(format!("dep {}: {e}", dep_hash)))?;

        let dep_ty = dep_component.component_type();

        // Collect this dep's own import deps first (recursive resolution)
        let mut sub_deps: Vec<O256> = Vec::new();
        for (name, _) in dep_ty.imports(&self.engine) {
            if let ImportKind::Component(hash) = categorize_import(name) {
                sub_deps.push(hash);
            }
        }
        for sub_hash in &sub_deps {
            self.resolve_import(sub_hash, blobs, store, instance_cache, resolving)?;
        }

        let dep_linker = self.build_linker(&dep_component, blobs, instance_cache)?;

        // Instantiate the dep
        let instance = dep_linker
            .instantiate(&mut *store, &dep_component)
            .map_err(|e| PropError::InstantiationError(format!("dep {}: {e}", dep_hash)))?;

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
}

/// Errors from proposition deciding.
#[derive(Debug, thiserror::Error)]
pub enum PropError {
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
