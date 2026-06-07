use std::sync::{Arc, Mutex};

use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;

use crate::component_builder::ComponentBuilder;
use crate::module::Module;
use crate::system_builder::{
    ContainerId, ExportEntry, FuncData, FuncId, ImportedFunc, InstanceImport, ModuleId,
    SystemBuilder, extract_hash,
};

// ---------------------------------------------------------------------------
// FuncRef — opaque reference to an imported function
// ---------------------------------------------------------------------------

#[pyclass(frozen, from_py_object)]
#[derive(Clone)]
pub struct FuncRef {
    pub(crate) index: usize,
}

#[pymethods]
impl FuncRef {
    fn __repr__(&self) -> String {
        format!("FuncRef({})", self.index)
    }
}

// ---------------------------------------------------------------------------
// InstanceRef — opaque reference to a proved/linked/copied instance
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

/// Target for FuncBuilder::call — either an imported func or a defined func.
#[derive(FromPyObject)]
enum CallTarget<'py> {
    Ref(FuncRef),
    Builder(Bound<'py, FuncBuilder>),
}

#[pymethods]
impl FuncBuilder {
    fn call(&self, target: CallTarget<'_>) {
        let idx = match target {
            CallTarget::Ref(f) => f.index,
            CallTarget::Builder(fb) => {
                let fb = fb.borrow();
                let sys = fb.system.lock().unwrap();
                sys.funcs[fb.id].index
            }
        };
        let mut sys = self.system.lock().unwrap();
        sys.funcs[self.id].body.push(format!("(call $f{idx})"));
    }

    fn local(&self, ty: &str) -> usize {
        let mut sys = self.system.lock().unwrap();
        let fd = &mut sys.funcs[self.id];
        let idx = fd.params.len() + fd.locals.len();
        fd.locals.push(ty.to_string());
        idx
    }

    fn local_get(&self, i: usize) {
        self.push_instr(format!("(local.get {i})"));
    }

    fn local_set(&self, i: usize) {
        self.push_instr(format!("(local.set {i})"));
    }

    fn local_tee(&self, i: usize) {
        self.push_instr(format!("(local.tee {i})"));
    }

    fn i32_const(&self, v: i32) {
        self.push_instr(format!("(i32.const {v})"));
    }

    fn i64_const(&self, v: i64) {
        self.push_instr(format!("(i64.const {v})"));
    }

    fn i32_add(&self) {
        self.push_op("i32.add");
    }

    fn i32_sub(&self) {
        self.push_op("i32.sub");
    }

    fn i32_mul(&self) {
        self.push_op("i32.mul");
    }

    fn i32_eq(&self) {
        self.push_op("i32.eq");
    }

    fn i32_ne(&self) {
        self.push_op("i32.ne");
    }

    fn i32_eqz(&self) {
        self.push_op("i32.eqz");
    }

    fn drop_(&self) {
        self.push_op("drop");
    }

    fn return_(&self) {
        self.push_op("return");
    }

    fn unreachable_(&self) {
        self.push_op("unreachable");
    }

    fn __repr__(&self) -> String {
        let sys = self.system.lock().unwrap();
        format!("FuncBuilder(f{})", sys.funcs[self.id].index)
    }
}

impl FuncBuilder {
    fn push_instr(&self, instr: String) {
        let mut sys = self.system.lock().unwrap();
        sys.funcs[self.id].body.push(instr);
    }

    fn push_op(&self, op: &str) {
        self.push_instr(op.to_string());
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
    ) -> FuncRef {
        let mut sys = self.system.lock().unwrap();
        let md = &mut sys.modules[self.id];
        let index = md.imports.len();
        md.imports.push(ImportedFunc {
            module: module.to_string(),
            name: name.to_string(),
            params: params.unwrap_or_default(),
            results: results.unwrap_or_default(),
        });
        FuncRef { index }
    }

    #[pyo3(signature = (params=None, results=None))]
    fn func(&self, params: Option<Vec<String>>, results: Option<Vec<String>>) -> FuncBuilder {
        let mut sys = self.system.lock().unwrap();
        let md = &sys.modules[self.id];
        let index = md.imports.len() + md.funcs.len();
        let func_id = sys.funcs.insert(FuncData {
            index,
            params: params.unwrap_or_default(),
            results: results.unwrap_or_default(),
            locals: Vec::new(),
            body: Vec::new(),
        });
        sys.modules[self.id].funcs.push(func_id);
        FuncBuilder {
            system: Arc::clone(&self.system),
            id: func_id,
        }
    }

    #[pyo3(signature = (f))]
    fn start(&self, f: &FuncBuilder) {
        let mut sys = self.system.lock().unwrap();
        let idx = sys.funcs[f.id].index;
        sys.modules[self.id].explicit_start = Some(idx);
    }

    #[pyo3(signature = (name, f=None))]
    fn export_func(&self, name: &str, f: Option<&FuncBuilder>) {
        let mut sys = self.system.lock().unwrap();
        match f {
            Some(fb) => {
                let idx = sys.funcs[fb.id].index;
                sys.modules[self.id]
                    .exports
                    .push(ExportEntry::Explicit(name.to_string(), idx));
            }
            None => {
                sys.modules[self.id]
                    .exports
                    .push(ExportEntry::NoOp(name.to_string()));
            }
        }
    }

    // -- Kernel methods (require container chain) --

    fn attest(&self) -> PyResult<()> {
        let mut sys = self.system.lock().unwrap();

        let container_id = Self::require_container_id(&sys, self.id)?;

        sys.containers[container_id].has_attest = true;

        let md = &mut sys.modules[self.id];
        let already = md
            .imports
            .iter()
            .any(|i| i.module == "env" && i.name == "attest");
        if !already {
            md.imports.push(ImportedFunc {
                module: "env".to_string(),
                name: "attest".to_string(),
                params: Vec::new(),
                results: Vec::new(),
            });
        }

        let attest_idx = md
            .imports
            .iter()
            .position(|i| i.module == "env" && i.name == "attest")
            .unwrap();
        md.start_calls.push(format!("(call $f{attest_idx})"));
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
        let mut sys = self.system.lock().unwrap();
        let md = &sys.modules[self.id];
        let module_ns = format!("inst{}", inst.index);
        let import_idx = md
            .imports
            .iter()
            .position(|i| i.module == module_ns && i.name == func_name)
            .ok_or_else(|| {
                PyValueError::new_err(format!(
                    "no import for instance {} export '{func_name}'",
                    inst.index
                ))
            })?;
        sys.modules[self.id]
            .start_calls
            .push(format!("(call $f{import_idx})"));
        Ok(())
    }

    #[getter]
    fn wat(&self) -> String {
        let sys = self.system.lock().unwrap();
        sys.generate_module_wat(self.id)
    }

    fn build(&self) -> PyResult<Module> {
        let wat = {
            let sys = self.system.lock().unwrap();
            sys.generate_module_wat(self.id)
        };
        Module::from_wat(&wat)
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
        // Extract hash first (may lock a different system via ContainerBuilder)
        let hash = extract_hash(target)?;
        let hex = hash.to_string();
        let export_names = exports.unwrap_or_default();

        let mut sys = self.system.lock().unwrap();

        let container_id = Self::require_container_id(&sys, self.id)?;

        let cd = &mut sys.containers[container_id];
        let inst_index = cd.instance_imports.len();
        cd.instance_imports.push(InstanceImport {
            import_name: format!("{kind}-{hex}"),
            exports: export_names.clone(),
        });

        let md = &mut sys.modules[self.id];
        for name in &export_names {
            md.imports.push(ImportedFunc {
                module: format!("inst{inst_index}"),
                name: name.clone(),
                params: Vec::new(),
                results: Vec::new(),
            });
        }

        Ok(InstanceRef {
            index: inst_index,
            exports: export_names,
        })
    }
}
