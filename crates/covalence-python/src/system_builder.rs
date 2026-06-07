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

use covalence_wasm::build::wasm_encoder::{
    CanonicalOption, ComponentBuilder as WeComponentBuilder, ComponentExportKind,
    ComponentTypeRef, ComponentValType, ExportKind, InstanceType, ModuleArg,
};
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
    // Snapshot: container component bytes
    // -----------------------------------------------------------------------

    /// Snapshot a container as a fully-assembled WASM component
    /// binary. Wraps the inner core module bytes in the
    /// component-model frame the kernel expects:
    ///
    /// 1. Optional `attest` component-level func import.
    /// 2. Per-`InstanceImport` component-level instance import, with a
    ///    fresh empty-func instance type listing each declared export.
    /// 3. Alias each instance export up to a top-level component func.
    /// 4. Embed the core module bytes via
    ///    [`ComponentBuilder::core_module_raw`].
    /// 5. Canon-lower each imported component func into a core func.
    /// 6. Build one core-instance-of-exports per `with` namespace
    ///    (`env` for `attest`, `inst{N}` per instance import).
    /// 7. Core-instantiate the inner module with those `with` args.
    /// 8. For each module export, alias the core export, canon-lift it
    ///    back to a component func, and export it.
    ///
    /// **Type signature limitation.** Every imported / exported
    /// component-level func is typed `() -> ()`. The current Python
    /// builder API doesn't model component-level value types, so all
    /// container-style exports are noop in practice — extending this
    /// requires picking concrete `ComponentValType`s for each core
    /// `i32`/`i64`/etc., which the WAT-text generator dodged by
    /// relying on the WAT compiler's inference.
    pub fn build_container_bytes(&self, container_id: ContainerId) -> PyResult<Vec<u8>> {
        let cd = &self.containers[container_id];

        if cd.link_hash.is_some() {
            return Err(PyValueError::new_err(
                "link-mode ContainerBuilder cannot be built as a component",
            ));
        }

        let comp_id = cd
            .component
            .ok_or_else(|| PyValueError::new_err("no root component"))?;
        let comp = &self.components[comp_id];

        let module_id = match comp.module {
            Some(mid) => mid,
            None => return Ok(empty_component_bytes()),
        };

        let module_bytes = self.snapshot_module_bytes(module_id);
        let md = &self.modules[module_id];

        let mut cb = WeComponentBuilder::default();

        // 1. Empty `() -> ()` component func type — reused everywhere.
        let empty_func_ty_idx = cb.func_type_empty();

        // 2. `attest` import.
        let attest_func_idx = cd
            .has_attest
            .then(|| cb.import("attest", ComponentTypeRef::Func(empty_func_ty_idx)));

        // 3. Per-instance imports + alias-up of each export. We track
        //    the resulting top-level component func indices for the
        //    canon-lower step below.
        let mut instance_aliased: Vec<Vec<u32>> = Vec::with_capacity(cd.instance_imports.len());
        for inst in &cd.instance_imports {
            let inst_ty_idx = cb.instance_type_of_empty_funcs(&inst.exports);
            let inst_idx = cb.import(
                inst.import_name.as_str(),
                ComponentTypeRef::Instance(inst_ty_idx),
            );

            let mut aliased = Vec::with_capacity(inst.exports.len());
            for name in &inst.exports {
                let func_idx =
                    cb.alias_export(inst_idx, name.as_str(), ComponentExportKind::Func);
                aliased.push(func_idx);
            }
            instance_aliased.push(aliased);
        }

        // 4. Embed the inner core module.
        let core_module_idx = cb.core_module_raw(None, &module_bytes);

        // 5. Canon-lower each component func into a core func.
        let attest_lowered = attest_func_idx
            .map(|f| cb.lower_func(None, f, std::iter::empty::<CanonicalOption>()));
        let instance_lowered: Vec<Vec<u32>> = instance_aliased
            .iter()
            .map(|aliased| {
                aliased
                    .iter()
                    .map(|&f| cb.lower_func(None, f, std::iter::empty::<CanonicalOption>()))
                    .collect()
            })
            .collect();

        // 6. Build a core instance-of-exports per `with` namespace.
        let mut with_args: Vec<(String, u32)> = Vec::new();

        if let Some(att) = attest_lowered {
            let env_inst = cb.core_instantiate_exports(
                None,
                [("attest", ExportKind::Func, att)],
            );
            with_args.push(("env".to_string(), env_inst));
        }

        for (i, lowered) in instance_lowered.iter().enumerate() {
            if lowered.is_empty() {
                continue;
            }
            let exports: Vec<(&str, ExportKind, u32)> = cd.instance_imports[i]
                .exports
                .iter()
                .zip(lowered.iter())
                .map(|(name, &core_idx)| (name.as_str(), ExportKind::Func, core_idx))
                .collect();
            let inst = cb.core_instantiate_exports(None, exports);
            with_args.push((format!("inst{i}"), inst));
        }

        // 7. Instantiate the core module with the `with` args.
        let main_core_inst = {
            let module_args: Vec<(&str, ModuleArg)> = with_args
                .iter()
                .map(|(name, idx)| (name.as_str(), ModuleArg::Instance(*idx)))
                .collect();
            cb.core_instantiate(None, core_module_idx, module_args)
        };

        // 8. Lift each module export to the component layer.
        for entry in &md.exports {
            let name = match entry {
                ExportEntry::NoOp(n) | ExportEntry::Explicit(n, _) => n.as_str(),
            };
            let core_func_idx =
                cb.core_alias_export(None, main_core_inst, name, ExportKind::Func);
            let lifted = cb.lift_func(
                None,
                core_func_idx,
                empty_func_ty_idx,
                std::iter::empty::<CanonicalOption>(),
            );
            cb.export(name, ComponentExportKind::Func, lifted, None);
        }

        Ok(cb.finish())
    }

    /// Decompile the assembled container component to WAT. Used by the
    /// `ContainerBuilder.wat` property.
    pub fn container_wat(&self, container_id: ContainerId) -> PyResult<String> {
        let bytes = self.build_container_bytes(container_id)?;
        covalence_wasm::wasm_to_wat(&bytes).map_err(|e| PyValueError::new_err(e.to_string()))
    }

    // -----------------------------------------------------------------------
    // Snapshot: standalone component bytes
    // -----------------------------------------------------------------------

    /// Snapshot a standalone component as bytes: the inner core module
    /// wrapped in a component with a single core instance, no
    /// container-style imports/exports.
    pub fn build_component_bytes(&self, component_id: ComponentId) -> Vec<u8> {
        let comp = &self.components[component_id];
        let module_id = match comp.module {
            Some(mid) => mid,
            None => return empty_component_bytes(),
        };

        let module_bytes = self.snapshot_module_bytes(module_id);
        let mut cb = WeComponentBuilder::default();
        let core_module_idx = cb.core_module_raw(None, &module_bytes);
        let _ = cb.core_instantiate::<[(&str, ModuleArg); 0]>(None, core_module_idx, []);
        cb.finish()
    }
}

/// Encode an empty `(component)`. `ComponentBuilder::default().finish()`
/// produces the same shape; pulled into a helper because we hit it from
/// two snapshot paths.
fn empty_component_bytes() -> Vec<u8> {
    WeComponentBuilder::default().finish()
}

/// Extension hooks that paper over a couple of `wasm_encoder`
/// ergonomic gaps: the empty `() -> ()` func type and an instance type
/// whose exports are all empty funcs are spelled out in many places
/// otherwise.
trait WeComponentBuilderExt {
    fn func_type_empty(&mut self) -> u32;
    fn instance_type_of_empty_funcs(&mut self, exports: &[String]) -> u32;
}

impl WeComponentBuilderExt for WeComponentBuilder {
    fn func_type_empty(&mut self) -> u32 {
        let (idx, enc) = self.ty(None);
        enc.function()
            .params(std::iter::empty::<(&str, ComponentValType)>())
            .result(None);
        idx
    }

    fn instance_type_of_empty_funcs(&mut self, exports: &[String]) -> u32 {
        let mut inst_ty = InstanceType::new();
        if !exports.is_empty() {
            // Each instance type has its own private type space; the
            // empty-func type goes in at index 0.
            inst_ty
                .ty()
                .function()
                .params(std::iter::empty::<(&str, ComponentValType)>())
                .result(None);
            for name in exports {
                inst_ty.export(name.as_str(), ComponentTypeRef::Func(0));
            }
        }
        self.type_instance(None, &inst_ty)
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
