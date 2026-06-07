//! Python-facing `ModuleBuilder` + `FuncBuilder`.
//!
//! Every method delegates to [`covalence_wasm::build`] — the Python
//! layer holds a `cwb::ModuleBuilder` per Python `ModuleBuilder` and a
//! `cwb::FuncBody` per open `FuncBuilder`. No parallel WAT-string
//! generator: bytes flow straight from the Rust encoder, and `m.wat`
//! decompiles a snapshot via `wasm_to_wat`.
//!
//! Methods that don't take a function argument trap if there is no
//! container chain (see `attest` / `prove` / `link` / `copy`) — these
//! are the kernel-side composition hooks that only make sense under a
//! `ContainerBuilder` parent.

use std::sync::{Arc, Mutex};

use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;

use covalence_wasm::build::{self as cwb, FuncIdx};

use crate::component_builder::ComponentBuilder;
use crate::module::Module;
use crate::system_builder::{
    ContainerId, ExportEntry, FuncData, FuncId, ImportedFunc, InstanceImport, ModuleData,
    ModuleId, SystemBuilder, extract_hash, parse_val_type, parse_val_types,
};

// ---------------------------------------------------------------------------
// FuncRef — opaque reference to an imported function
// ---------------------------------------------------------------------------

#[pyclass(frozen, from_py_object)]
#[derive(Clone)]
pub struct FuncRef {
    /// Index in the (shared) function index space — imports come
    /// before locally-defined functions, so `index` may refer to
    /// either, but `FuncRef` is only constructed by `import_func`.
    pub(crate) index: u32,
}

#[pymethods]
impl FuncRef {
    fn __repr__(&self) -> String {
        format!("FuncRef({})", self.index)
    }
}

// ---------------------------------------------------------------------------
// InstanceRef — opaque reference to a proved / linked / copied instance
// ---------------------------------------------------------------------------

#[pyclass(frozen, from_py_object)]
#[derive(Clone)]
pub struct InstanceRef {
    pub(crate) index: usize,
    #[allow(dead_code)]
    pub(crate) exports: Vec<String>,
}

#[pymethods]
impl InstanceRef {
    fn __repr__(&self) -> String {
        format!("InstanceRef(inst{})", self.index)
    }
}

// ---------------------------------------------------------------------------
// FuncBuilder
// ---------------------------------------------------------------------------

#[pyclass]
pub struct FuncBuilder {
    pub(crate) system: Arc<Mutex<SystemBuilder>>,
    pub(crate) id: FuncId,
}

/// Target for `FuncBuilder::call` — either an imported func (`FuncRef`)
/// or a sibling defined function (`FuncBuilder`).
#[derive(FromPyObject)]
enum CallTarget<'py> {
    Ref(FuncRef),
    Builder(Bound<'py, FuncBuilder>),
}

#[pymethods]
impl FuncBuilder {
    fn call(&self, target: CallTarget<'_>) {
        let idx = match target {
            CallTarget::Ref(f) => FuncIdx(f.index),
            CallTarget::Builder(fb) => {
                let fb = fb.borrow();
                let sys = fb.system.lock().unwrap();
                sys.funcs[fb.id].body.idx()
            }
        };
        self.with_body(|b| {
            b.call(idx);
        });
    }

    fn local(&self, ty: &str) -> PyResult<u32> {
        let val_ty = parse_val_type(ty)?;
        let mut sys = self.system.lock().unwrap();
        Ok(sys.funcs[self.id].body.local(val_ty))
    }

    // -- Locals --
    fn local_get(&self, i: u32) { self.with_body(|b| { b.local_get(i); }); }
    fn local_set(&self, i: u32) { self.with_body(|b| { b.local_set(i); }); }
    fn local_tee(&self, i: u32) { self.with_body(|b| { b.local_tee(i); }); }

    // -- i32 ops --
    fn i32_const(&self, v: i32) { self.with_body(|b| { b.i32_const(v); }); }
    fn i32_add(&self) { self.with_body(|b| { b.i32_add(); }); }
    fn i32_sub(&self) { self.with_body(|b| { b.i32_sub(); }); }
    fn i32_mul(&self) { self.with_body(|b| { b.i32_mul(); }); }
    fn i32_eq(&self) { self.with_body(|b| { b.i32_eq(); }); }
    fn i32_ne(&self) { self.with_body(|b| { b.i32_ne(); }); }
    fn i32_eqz(&self) { self.with_body(|b| { b.i32_eqz(); }); }

    // -- i64 ops --
    fn i64_const(&self, v: i64) { self.with_body(|b| { b.i64_const(v); }); }
    fn i64_add(&self) { self.with_body(|b| { b.i64_add(); }); }
    fn i64_sub(&self) { self.with_body(|b| { b.i64_sub(); }); }
    fn i64_mul(&self) { self.with_body(|b| { b.i64_mul(); }); }

    // -- Control flow / stack --
    fn drop_(&self) { self.with_body(|b| { b.drop(); }); }
    fn return_(&self) { self.with_body(|b| { b.return_(); }); }
    fn unreachable_(&self) { self.with_body(|b| { b.unreachable(); }); }

    fn __repr__(&self) -> String {
        let sys = self.system.lock().unwrap();
        format!("FuncBuilder(f{})", sys.funcs[self.id].body.idx().0)
    }
}

impl FuncBuilder {
    /// Lock the arena, hand the open `FuncBody` to `f`, drop the lock.
    /// All the instruction shims funnel through this so the locking
    /// pattern lives in one place.
    fn with_body<R>(&self, f: impl FnOnce(&mut cwb::FuncBody) -> R) -> R {
        let mut sys = self.system.lock().unwrap();
        f(&mut sys.funcs[self.id].body)
    }
}

// ---------------------------------------------------------------------------
// ModuleBuilder
// ---------------------------------------------------------------------------

#[pyclass]
pub struct ModuleBuilder {
    pub(crate) system: Arc<Mutex<SystemBuilder>>,
    pub(crate) id: ModuleId,
}

#[pymethods]
impl ModuleBuilder {
    #[new]
    pub fn new() -> Self {
        let mut sys = SystemBuilder::new();
        let module_id = sys.modules.insert(SystemBuilder::new_module_data(None));
        ModuleBuilder {
            system: Arc::new(Mutex::new(sys)),
            id: module_id,
        }
    }

    #[getter]
    fn component(&self) -> Option<ComponentBuilder> {
        let sys = self.system.lock().unwrap();
        let comp_id = sys.modules[self.id].component?;
        Some(ComponentBuilder {
            system: Arc::clone(&self.system),
            id: comp_id,
        })
    }

    #[pyo3(signature = (module, name, params=None, results=None))]
    fn import_func(
        &self,
        module: &str,
        name: &str,
        params: Option<Vec<String>>,
        results: Option<Vec<String>>,
    ) -> PyResult<FuncRef> {
        let params = parse_val_types(&params.unwrap_or_default())?;
        let results = parse_val_types(&results.unwrap_or_default())?;
        let mut sys = self.system.lock().unwrap();
        let idx = push_import(&mut sys.modules[self.id], module, name, &params, &results);
        Ok(FuncRef { index: idx.0 })
    }

    #[pyo3(signature = (params=None, results=None))]
    fn func(
        &self,
        params: Option<Vec<String>>,
        results: Option<Vec<String>>,
    ) -> PyResult<FuncBuilder> {
        let params = parse_val_types(&params.unwrap_or_default())?;
        let results = parse_val_types(&results.unwrap_or_default())?;
        let mut sys = self.system.lock().unwrap();
        let body = sys.modules[self.id].builder.func(&params, &results);
        let func_id = sys.funcs.insert(FuncData { body });
        sys.modules[self.id].funcs.push(func_id);
        Ok(FuncBuilder {
            system: Arc::clone(&self.system),
            id: func_id,
        })
    }

    #[pyo3(signature = (f))]
    fn start(&self, f: &FuncBuilder) {
        let mut sys = self.system.lock().unwrap();
        let idx = sys.funcs[f.id].body.idx();
        sys.modules[self.id].explicit_start = Some(idx);
    }

    #[pyo3(signature = (name, f=None))]
    fn export_func(&self, name: &str, f: Option<&FuncBuilder>) {
        let mut sys = self.system.lock().unwrap();
        let entry = match f {
            Some(fb) => {
                let idx = sys.funcs[fb.id].body.idx();
                ExportEntry::Explicit(name.to_string(), idx)
            }
            None => ExportEntry::NoOp(name.to_string()),
        };
        sys.modules[self.id].exports.push(entry);
    }

    // -- Kernel methods (require container chain) --

    fn attest(&self) -> PyResult<()> {
        let mut sys = self.system.lock().unwrap();
        let container_id = Self::require_container_id(&sys, self.id)?;
        sys.containers[container_id].has_attest = true;

        let attest_idx = match sys.find_import(self.id, "env", "attest") {
            Some(idx) => idx,
            None => push_import(&mut sys.modules[self.id], "env", "attest", &[], &[]),
        };
        sys.modules[self.id].start_calls.push(attest_idx);
        Ok(())
    }

    fn prove(
        &self,
        target: &Bound<'_, PyAny>,
        exports: Option<Vec<String>>,
    ) -> PyResult<InstanceRef> {
        self.add_dep_import("prove", target, exports)
    }

    fn link(
        &self,
        target: &Bound<'_, PyAny>,
        exports: Option<Vec<String>>,
    ) -> PyResult<InstanceRef> {
        self.add_dep_import("link", target, exports)
    }

    fn copy(
        &self,
        target: &Bound<'_, PyAny>,
        exports: Option<Vec<String>>,
    ) -> PyResult<InstanceRef> {
        self.add_dep_import("copy", target, exports)
    }

    #[pyo3(signature = (inst, func_name))]
    fn call(&self, inst: &InstanceRef, func_name: &str) -> PyResult<()> {
        let module_ns = format!("inst{}", inst.index);
        let mut sys = self.system.lock().unwrap();
        let import_idx = sys.find_import(self.id, &module_ns, func_name).ok_or_else(|| {
            PyValueError::new_err(format!(
                "no import for instance {} export '{func_name}'",
                inst.index
            ))
        })?;
        sys.modules[self.id].start_calls.push(import_idx);
        Ok(())
    }

    #[getter]
    fn wat(&self) -> String {
        let sys = self.system.lock().unwrap();
        sys.generate_module_wat(self.id)
    }

    fn build(&self) -> PyResult<Module> {
        let bytes = {
            let sys = self.system.lock().unwrap();
            sys.snapshot_module_bytes(self.id)
        };
        Module::from_bytes_internal(bytes)
    }
}

impl ModuleBuilder {
    fn require_container_id(sys: &SystemBuilder, module_id: ModuleId) -> PyResult<ContainerId> {
        let comp_id = sys.modules[module_id].component.ok_or_else(|| {
            PyValueError::new_err(
                "kernel methods require a container chain (use ContainerBuilder or ComponentBuilder)",
            )
        })?;
        sys.components[comp_id].container.ok_or_else(|| {
            PyValueError::new_err("kernel methods require a container chain (use ContainerBuilder)")
        })
    }

    fn add_dep_import(
        &self,
        kind: &str,
        target: &Bound<'_, PyAny>,
        exports: Option<Vec<String>>,
    ) -> PyResult<InstanceRef> {
        // Extract hash first (may lock a different system via ContainerBuilder).
        let hash = extract_hash(target)?;
        let hex = hash.to_string();
        let export_names = exports.unwrap_or_default();

        let mut sys = self.system.lock().unwrap();
        let container_id = Self::require_container_id(&sys, self.id)?;

        let inst_index = {
            let cd = &mut sys.containers[container_id];
            let inst_index = cd.instance_imports.len();
            cd.instance_imports.push(InstanceImport {
                import_name: format!("{kind}-{hex}"),
                exports: export_names.clone(),
            });
            inst_index
        };

        let ns = format!("inst{inst_index}");
        for name in &export_names {
            push_import(&mut sys.modules[self.id], &ns, name, &[], &[]);
        }

        Ok(InstanceRef {
            index: inst_index,
            exports: export_names,
        })
    }
}

/// Push a `(module, name)` import onto both the Rust builder and the
/// Python-side `imports` bookkeeping. Returns the assigned `FuncIdx`.
fn push_import(
    md: &mut ModuleData,
    module: &str,
    name: &str,
    params: &[cwb::ValType],
    results: &[cwb::ValType],
) -> FuncIdx {
    let idx = md.builder.import_func(module, name, params, results);
    md.imports.push(ImportedFunc {
        module: module.to_string(),
        name: name.to_string(),
    });
    idx
}
