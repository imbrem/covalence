//! Arena + state for the `ContainerBuilder` / `ComponentBuilder` /
//! `ModuleBuilder` Python triple.
//!
//! The Python builders are all named handles into a shared `SlotMap`
//! arena (one `SystemBuilder` per top-level builder root). Each handle
//! is a `(Arc<Mutex<SystemBuilder>>, <slotmap-key>)` pair, so multiple
//! Python objects pointing at the same node mutate one piece of state.
//!
//! Module *encoding* is delegated to
//! [`covalence_wasm::build::ModuleBuilder`] — the Python layer keeps
//! only the bookkeeping the Rust builder doesn't expose (imports
//! indexed by name for the container-chain `attest` / `prove` / `link`
//! / `copy` flows; container-level `InstanceImport`s; the choice
//! between an explicit `start` and a synthesised `start` that fires a
//! list of calls). The component-wrapping step (`(component (core
//! module $m …))` plus canonical-ABI lift/lower for the container's
//! attest + per-instance imports) is still emitted as WAT text; the
//! embedded core module is freshly decompiled from the Rust builder's
//! bytes, so there is no parallel WAT instruction generator.

use pyo3::exceptions::{PyTypeError, PyValueError};
use pyo3::prelude::*;
use slotmap::SlotMap;

use covalence_wasm::build::{self as cwb, FuncIdx, ValType};

use crate::component::Component;
use crate::container::Container;
use crate::hash::O256;

// ---------------------------------------------------------------------------
// Slotmap keys
// ---------------------------------------------------------------------------

slotmap::new_key_type! {
    pub struct ContainerId;
    pub struct ComponentId;
    pub struct ModuleId;
    pub struct FuncId;
}

// ---------------------------------------------------------------------------
// Data types stored in the arena
// ---------------------------------------------------------------------------

pub struct ContainerData {
    pub component: Option<ComponentId>,
    pub link_hash: Option<covalence_hash::O256>,
    pub instance_imports: Vec<InstanceImport>,
    pub has_attest: bool,
    pub built_hash: Option<covalence_hash::O256>,
}

pub struct ComponentData {
    pub container: Option<ContainerId>,
    pub module: Option<ModuleId>,
}

pub struct ModuleData {
    pub component: Option<ComponentId>,
    /// The actual encoder. Imports / memories / globals / exports get
    /// pushed straight through; functions are allocated via
    /// `builder.func()` and their `FuncBody` lives in `funcs` until
    /// finalize.
    pub builder: cwb::ModuleBuilder,
    /// Parallel list of `(module, name)` for every import we've made,
    /// kept so `attest()` / `call(inst, name)` can look up an import's
    /// `FuncIdx` by name. Order matches the Rust builder.
    pub imports: Vec<ImportedFunc>,
    /// Open `FuncBody` handles in allocation order. Finalized
    /// in-order at snapshot time so the code section matches the
    /// function section.
    pub funcs: Vec<FuncId>,
    pub exports: Vec<ExportEntry>,
    /// Functions to call from a synthesized start. Populated by
    /// `attest()` and `call(inst, name)`. Realized at snapshot time as
    /// a `(start)` function appended after all user funcs.
    pub start_calls: Vec<FuncIdx>,
    /// User-set explicit start. Takes precedence over `start_calls`.
    pub explicit_start: Option<FuncIdx>,
}

pub struct FuncData {
    /// The Rust function body. Mutated by every `FuncBuilder`
    /// instruction call; cloned and finished into the snapshot
    /// `ModuleBuilder` at build / WAT time.
    pub body: cwb::FuncBody,
}

#[derive(Clone)]
pub struct ImportedFunc {
    pub module: String,
    pub name: String,
}

#[derive(Clone)]
pub enum ExportEntry {
    /// Empty placeholder function exported under `name`. Used by
    /// container chains where you only need the symbol present at the
    /// component boundary (no body to run on the host side).
    NoOp(String),
    /// Real exported function `name` → core-func index `FuncIdx`.
    Explicit(String, FuncIdx),
}

#[derive(Clone)]
pub struct InstanceImport {
    pub import_name: String,
    pub exports: Vec<String>,
}

// ---------------------------------------------------------------------------
// Val-type parsing
// ---------------------------------------------------------------------------

/// Map a Python-side val-type string (`"i32"`, `"i64"`, `"f32"`, `"f64"`,
/// `"v128"`, `"externref"`, `"funcref"`) to a `wasm_encoder::ValType`.
pub fn parse_val_type(s: &str) -> PyResult<ValType> {
    match s {
        "i32" => Ok(ValType::I32),
        "i64" => Ok(ValType::I64),
        "f32" => Ok(ValType::F32),
        "f64" => Ok(ValType::F64),
        "v128" => Ok(ValType::V128),
        "externref" => Ok(ValType::EXTERNREF),
        "funcref" => Ok(ValType::FUNCREF),
        other => Err(PyValueError::new_err(format!(
            "unknown val type: '{other}'; expected i32 / i64 / f32 / f64 / v128 / externref / funcref"
        ))),
    }
}

pub fn parse_val_types(items: &[String]) -> PyResult<Vec<ValType>> {
    items.iter().map(|s| parse_val_type(s)).collect()
}

// ---------------------------------------------------------------------------
// Arena
// ---------------------------------------------------------------------------

pub struct SystemBuilder {
    pub containers: SlotMap<ContainerId, ContainerData>,
    pub components: SlotMap<ComponentId, ComponentData>,
    pub modules: SlotMap<ModuleId, ModuleData>,
    pub funcs: SlotMap<FuncId, FuncData>,
}

impl SystemBuilder {
    pub fn new() -> Self {
        SystemBuilder {
            containers: SlotMap::with_key(),
            components: SlotMap::with_key(),
            modules: SlotMap::with_key(),
            funcs: SlotMap::with_key(),
        }
    }

    pub fn new_module_data(component: Option<ComponentId>) -> ModuleData {
        ModuleData {
            component,
            builder: cwb::ModuleBuilder::new(),
            imports: Vec::new(),
            funcs: Vec::new(),
            exports: Vec::new(),
            start_calls: Vec::new(),
            explicit_start: None,
        }
    }

    /// Resolve an import's position in the function index space by
    /// `(module, name)`. Returns `None` if no such import exists.
    pub fn find_import(&self, module_id: ModuleId, module: &str, name: &str) -> Option<FuncIdx> {
        self.modules[module_id]
            .imports
            .iter()
            .position(|i| i.module == module && i.name == name)
            .map(|pos| FuncIdx(pos as u32))
    }

    // -----------------------------------------------------------------------
    // Snapshot: core module bytes
    // -----------------------------------------------------------------------

    /// Snapshot the current state of a module into a fresh, finalized
    /// wasm byte vector. Non-consuming: clones the builder + all open
    /// `FuncBody`s, finishes them in allocation order, then synthesises
    /// the start function if any. The original arena is untouched.
    pub fn snapshot_module_bytes(&self, module_id: ModuleId) -> Vec<u8> {
        let md = &self.modules[module_id];
        let mut builder = md.builder.clone();

        // Finalize user funcs in allocation order so the code section
        // entries line up 1:1 with the function section entries the
        // original builder allocated.
        for &func_id in &md.funcs {
            self.funcs[func_id].body.clone().finish(&mut builder);
        }

        // Realize start: explicit wins; otherwise synthesise from
        // `start_calls` if any.
        if let Some(start) = md.explicit_start {
            builder.start(start);
        } else if !md.start_calls.is_empty() {
            let mut sf = builder.func(&[], &[]);
            for &fidx in &md.start_calls {
                sf.call(fidx);
            }
            let sidx = sf.finish(&mut builder);
            builder.start(sidx);
        }

        // Emit noop exports as zero-arity empty functions. We allocate
        // these AFTER user funcs + synthesised start so the user's
        // FuncIdx values stay stable.
        for entry in &md.exports {
            match entry {
                ExportEntry::Explicit(name, idx) => {
                    builder.export_func(name, *idx);
                }
                ExportEntry::NoOp(name) => {
                    let noop = builder.func(&[], &[]);
                    let noop_idx = noop.finish(&mut builder);
                    builder.export_func(name, noop_idx);
                }
            }
        }

        builder.finish()
    }

    /// Decompile the module snapshot to WAT text. Used by the
    /// component-wrapping step below and by `ModuleBuilder.wat`.
    pub fn generate_module_wat(&self, module_id: ModuleId) -> String {
        let bytes = self.snapshot_module_bytes(module_id);
        covalence_wasm::wasm_to_wat(&bytes).unwrap_or_else(|e| {
            // The snapshot is the output of our own builder, so a
            // decompile failure is a programmer error rather than user
            // input gone wrong. Surface it as text so it shows up in
            // the WAT and the tests fail loud.
            format!(";; wasm_to_wat failed: {e}")
        })
    }

    // -----------------------------------------------------------------------
    // WAT generation: container (component wrapping module)
    // -----------------------------------------------------------------------

    pub fn generate_container_wat(&self, container_id: ContainerId) -> PyResult<String> {
        let cd = &self.containers[container_id];

        if cd.link_hash.is_some() {
            return Err(PyValueError::new_err(
                "link-mode ContainerBuilder cannot be built as WAT",
            ));
        }

        let comp_id = cd
            .component
            .ok_or_else(|| PyValueError::new_err("no root component"))?;
        let comp = &self.components[comp_id];

        let module_id = match comp.module {
            Some(mid) => mid,
            None => return Ok("(component)".to_string()),
        };

        let module_wat = self.generate_module_wat(module_id);
        let md = &self.modules[module_id];

        let mut lines = vec!["(component".to_string()];

        // 1. Container imports
        if cd.has_attest {
            lines.push("  (import \"attest\" (func $attest))".to_string());
        }
        for (i, inst) in cd.instance_imports.iter().enumerate() {
            if inst.exports.is_empty() {
                lines.push(format!(
                    "  (import \"{}\" (instance $inst{i}))",
                    inst.import_name
                ));
            } else {
                let export_decls: Vec<String> = inst
                    .exports
                    .iter()
                    .map(|name| format!("(export \"{name}\" (func))"))
                    .collect();
                lines.push(format!(
                    "  (import \"{}\" (instance $inst{i} {}))",
                    inst.import_name,
                    export_decls.join(" ")
                ));
            }
        }

        // 2. Alias instance exports
        for (i, inst) in cd.instance_imports.iter().enumerate() {
            for name in &inst.exports {
                lines.push(format!(
                    "  (alias export $inst{i} \"{name}\" (func $inst{i}__{name}))"
                ));
            }
        }

        // 3. Core module
        push_core_module(&mut lines, &module_wat);

        // 4. Canon lower
        if cd.has_attest {
            lines.push("  (core func $attest_lowered (canon lower (func $attest)))".to_string());
        }
        for (i, inst) in cd.instance_imports.iter().enumerate() {
            for name in &inst.exports {
                lines.push(format!(
                    "  (core func $inst{i}__{name}_lowered (canon lower (func $inst{i}__{name})))"
                ));
            }
        }

        // 5. Core instance
        let mut with_clauses = Vec::new();

        // "env" namespace
        let mut env_exports = Vec::new();
        if cd.has_attest {
            env_exports.push("      (export \"attest\" (func $attest_lowered))".to_string());
        }
        if !env_exports.is_empty() {
            with_clauses.push(format!(
                "    (with \"env\" (instance\n{}\n    ))",
                env_exports.join("\n")
            ));
        }

        // Instance namespace imports
        for (i, inst) in cd.instance_imports.iter().enumerate() {
            if !inst.exports.is_empty() {
                let ns = format!("inst{i}");
                let inst_exports: Vec<String> = inst
                    .exports
                    .iter()
                    .map(|name| {
                        format!("      (export \"{name}\" (func $inst{i}__{name}_lowered))")
                    })
                    .collect();
                with_clauses.push(format!(
                    "    (with \"{ns}\" (instance\n{}\n    ))",
                    inst_exports.join("\n")
                ));
            }
        }

        if with_clauses.is_empty() {
            lines.push("  (core instance $i (instantiate $m))".to_string());
        } else {
            lines.push(format!(
                "  (core instance $i (instantiate $m\n{}\n  ))",
                with_clauses.join("\n")
            ));
        }

        // 6. Component exports (lifted) — name only; the actual core
        // func is whatever the module exported under that name (real
        // or noop placeholder).
        for entry in &md.exports {
            let name = match entry {
                ExportEntry::NoOp(name) => name,
                ExportEntry::Explicit(name, _) => name,
            };
            lines.push(format!(
                "  (func ${name}_lifted (canon lift (core func $i \"{name}\")))"
            ));
            lines.push(format!("  (export \"{name}\" (func ${name}_lifted))"));
        }

        lines.push(")".to_string());
        Ok(lines.join("\n"))
    }

    // -----------------------------------------------------------------------
    // WAT generation: standalone component (wraps module in component)
    // -----------------------------------------------------------------------

    pub fn build_component_wat(&self, component_id: ComponentId) -> String {
        let comp = &self.components[component_id];
        let module_id = match comp.module {
            Some(mid) => mid,
            None => return "(component)".to_string(),
        };

        let module_wat = self.generate_module_wat(module_id);
        let mut lines = vec!["(component".to_string()];
        push_core_module(&mut lines, &module_wat);
        lines.push("  (core instance $i (instantiate $m))".to_string());
        lines.push(")".to_string());
        lines.join("\n")
    }
}

/// Embed a `(module …)` WAT fragment as a `(core module $m …)` inside a
/// component WAT. The decompiled inner module is multi-line; we rewrite
/// only the first line and re-indent the rest.
fn push_core_module(lines: &mut Vec<String>, module_wat: &str) {
    let inner_lines: Vec<&str> = module_wat.lines().collect();
    if inner_lines.len() <= 1 {
        lines.push(format!("  (core module $m {module_wat})"));
        return;
    }
    let first = inner_lines[0].replace("(module", "(core module $m");
    lines.push(format!("  {first}"));
    for line in &inner_lines[1..] {
        lines.push(format!("  {line}"));
    }
}

// ---------------------------------------------------------------------------
// Hash extraction helpers
// ---------------------------------------------------------------------------

/// Resolve a Python value to an `O256` hash. Accepts (in order) an
/// `O256`, a 64-char hex string, a `Container`, a `Component`, and —
/// when `allow_container_builder` is true — a built `ContainerBuilder`.
///
/// The flag distinguishes the two call sites: `ModuleBuilder.prove/link/copy`
/// must accept a (possibly not-yet-built) sibling `ContainerBuilder` (the
/// caller's intent: forward-reference a peer in the same arena), while
/// `ContainerBuilder::from_link` must reject builders to avoid an
/// arena-handoff hazard.
pub fn extract_hash_with(
    obj: &Bound<'_, PyAny>,
    allow_container_builder: bool,
) -> PyResult<covalence_hash::O256> {
    if let Ok(o) = obj.extract::<PyRef<O256>>() {
        return Ok(o.0);
    }
    if let Ok(hex) = obj.extract::<String>() {
        return covalence_hash::O256::from_hex(&hex)
            .ok_or_else(|| PyValueError::new_err("invalid hex hash (expected 64 hex chars)"));
    }
    if let Ok(c) = obj.extract::<PyRef<Container>>() {
        return Ok(c.content_hash());
    }
    if let Ok(c) = obj.extract::<PyRef<Component>>() {
        return Ok(c.content_hash());
    }
    if allow_container_builder
        && let Ok(cb) = obj.extract::<PyRef<crate::container_builder::ContainerBuilder>>()
    {
        let sys = cb.system.lock().unwrap();
        let hash = sys.containers[cb.id].built_hash.ok_or_else(|| {
            PyValueError::new_err("ContainerBuilder must be built before use as hash")
        })?;
        return Ok(hash);
    }
    Err(PyTypeError::new_err(if allow_container_builder {
        "expected O256, hex string, Container, Component, or ContainerBuilder"
    } else {
        "expected O256, hex string, Container, or Component"
    }))
}

#[inline]
pub fn extract_hash(obj: &Bound<'_, PyAny>) -> PyResult<covalence_hash::O256> {
    extract_hash_with(obj, true)
}

#[inline]
pub fn extract_hash_for_container(obj: &Bound<'_, PyAny>) -> PyResult<covalence_hash::O256> {
    extract_hash_with(obj, false)
}
