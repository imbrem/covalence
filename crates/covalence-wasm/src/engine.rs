use std::fmt;

use covalence_object::O256;
use wasmtime::component::{Component, Linker};
use wasmtime::{Engine, Module, Store};

/// Trait for looking up blobs by hash. Implemented by blob stores.
pub trait BlobLookup {
    /// Get blob data by hash. Returns None if hash is unknown or data unavailable.
    fn get_blob(&self, hash: &O256) -> Option<&[u8]>;
    /// Check if a hash is known (either with or without data).
    fn contains_blob(&self, hash: &O256) -> bool;
}

/// Host state threaded through wasmtime's Store.
struct HostState {
    attested: bool,
}

/// Result of checking a proposition.
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

/// Summary of a parsed WASM module's imports and exports.
#[derive(Debug)]
pub struct ModuleInfo {
    pub imports: Vec<(String, String)>,
    pub exports: Vec<String>,
}

impl fmt::Display for ModuleInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "module: {} imports, {} exports",
            self.imports.len(),
            self.exports.len()
        )?;
        for (module, name) in &self.imports {
            write!(f, "\n  import {module}::{name}")?;
        }
        for name in &self.exports {
            write!(f, "\n  export {name}")?;
        }
        Ok(())
    }
}

/// Summary of a parsed WASM component's imports and exports.
#[derive(Debug)]
pub struct ComponentInfo {
    pub imports: Vec<String>,
    pub exports: Vec<String>,
}

impl fmt::Display for ComponentInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "component: {} imports, {} exports",
            self.imports.len(),
            self.exports.len()
        )?;
        for name in &self.imports {
            write!(f, "\n  import {name}")?;
        }
        for name in &self.exports {
            write!(f, "\n  export {name}")?;
        }
        Ok(())
    }
}

/// Categorized import from a proposition component.
#[derive(Debug)]
enum ImportKind {
    /// The `attest()` function.
    Attest,
    /// A blob by hash: "blob/{hex}".
    Blob(O256),
    /// A WASM module by hash: "module/{hex}".
    Module(O256),
    /// A component by hash: "component/{hex}".
    Component(O256),
    /// A proposition by hash: "prop/{hex}".
    Prop(O256),
    /// Unknown import name.
    Unknown(String),
}

fn categorize_import(name: &str) -> ImportKind {
    if name == "attest" {
        return ImportKind::Attest;
    }
    if let Some(hex) = name.strip_prefix("blob/") {
        if let Some(hash) = O256::from_hex(hex) {
            return ImportKind::Blob(hash);
        }
    }
    if let Some(hex) = name.strip_prefix("module/") {
        if let Some(hash) = O256::from_hex(hex) {
            return ImportKind::Module(hash);
        }
    }
    if let Some(hex) = name.strip_prefix("component/") {
        if let Some(hash) = O256::from_hex(hex) {
            return ImportKind::Component(hash);
        }
    }
    if let Some(hex) = name.strip_prefix("prop/") {
        if let Some(hash) = O256::from_hex(hex) {
            return ImportKind::Prop(hash);
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

    /// Check if a proposition (WASM component) is decidably true,
    /// i.e. whether its start function calls `attest()`.
    ///
    /// The component may import:
    /// - `"attest"`: a function that marks the proposition as true
    /// - `"blob/{hash}"`: a blob from the store (lazy — traps if data unavailable)
    /// - `"module/{hash}"`: a core WASM module from the store
    /// - `"component/{hash}"`: a component from the store
    /// - `"prop/{hash}"`: another proposition (always lazy — unresolved become traps)
    ///
    /// When `lazy` is true, unknown component imports also become traps rather
    /// than failing eagerly. Prop imports are always lazy regardless of this flag.
    pub fn check_prop(
        &self,
        bytes: &[u8],
        blobs: &dyn BlobLookup,
    ) -> Result<PropResult, PropError> {
        self.check_prop_inner(bytes, blobs, true)
    }

    /// Like [`check_prop`](Self::check_prop) but with eager component resolution:
    /// unknown component imports produce an immediate error.
    pub fn check_prop_eager(
        &self,
        bytes: &[u8],
        blobs: &dyn BlobLookup,
    ) -> Result<PropResult, PropError> {
        self.check_prop_inner(bytes, blobs, false)
    }

    fn check_prop_inner(
        &self,
        bytes: &[u8],
        blobs: &dyn BlobLookup,
        lazy: bool,
    ) -> Result<PropResult, PropError> {
        let component = Component::new(&self.engine, bytes)
            .map_err(|e| PropError::InvalidComponent(e.to_string()))?;

        let ty = component.component_type();

        // Classify all imports
        let mut imports_attest = false;
        for (name, _) in ty.imports(&self.engine) {
            match categorize_import(name) {
                ImportKind::Attest => imports_attest = true,
                ImportKind::Component(hash) => {
                    // In eager mode, components must be known
                    if !lazy && !blobs.contains_blob(&hash) {
                        return Err(PropError::UnknownImport(name.to_string()));
                    }
                }
                _ => {}
            }
        }

        // If attest is not imported at all, this prop is statically false
        if !imports_attest {
            return Ok(PropResult::False);
        }

        let mut linker: Linker<HostState> = Linker::new(&self.engine);

        // Provide host implementations for each import
        for (name, _ty) in ty.imports(&self.engine) {
            let import_kind = categorize_import(name);
            match import_kind {
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
                    let data = blobs.get_blob(&hash).map(|d| d.to_vec());
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
                    // For MVP: module linking is complex.
                    // Unknown modules left unlinked — instantiation will fail if used.
                }
                ImportKind::Component(_hash) | ImportKind::Prop(_hash) => {
                    // Prop imports are always lazy. Component imports are lazy
                    // when `lazy` is true, otherwise already validated above.
                    // Provide an unconditional trap for unresolved imports.
                    let import_name = name.to_string();
                    linker
                        .root()
                        .func_wrap(
                            name,
                            move |_cx: wasmtime::StoreContextMut<'_, HostState>, _args: ()| {
                                Err::<(), _>(wasmtime::Error::msg(format!(
                                    "unresolved import: {import_name}"
                                )))
                            },
                        )
                        .map_err(|e| PropError::LinkError(e.to_string()))?;
                }
                ImportKind::Unknown(ref _name) => {
                    // Unknown import pattern — leave unlinked, instantiation will fail
                }
            }
        }

        let host = HostState { attested: false };
        let mut store = Store::new(&self.engine, host);

        // Instantiate the component — this runs the start function
        let _instance = linker
            .instantiate(&mut store, &component)
            .map_err(|e| PropError::InstantiationError(e.to_string()))?;

        Ok(if store.data().attested {
            PropResult::True
        } else {
            // Imported attest but didn't call it during startup
            PropResult::Unknown
        })
    }
}

/// Errors from proposition checking.
#[derive(Debug, thiserror::Error)]
pub enum PropError {
    #[error("invalid component: {0}")]
    InvalidComponent(String),
    #[error("unknown import: {0}")]
    UnknownImport(String),
    #[error("link error: {0}")]
    LinkError(String),
    #[error("instantiation error: {0}")]
    InstantiationError(String),
}
