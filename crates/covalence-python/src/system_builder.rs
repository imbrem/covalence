use pyo3::exceptions::{PyTypeError, PyValueError};
use pyo3::prelude::*;
use slotmap::SlotMap;

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
    pub imports: Vec<ImportedFunc>,
    pub funcs: Vec<FuncId>,
    pub exports: Vec<ExportEntry>,
    pub start_calls: Vec<String>,
    pub explicit_start: Option<usize>,
}

pub struct FuncData {
    pub index: usize,
    pub params: Vec<String>,
    pub results: Vec<String>,
    pub locals: Vec<String>,
    pub body: Vec<String>,
}

#[derive(Clone)]
pub struct ImportedFunc {
    pub module: String,
    pub name: String,
    pub params: Vec<String>,
    pub results: Vec<String>,
}

#[derive(Clone)]
pub enum ExportEntry {
    NoOp(String),
    Explicit(String, usize),
}

#[derive(Clone)]
pub struct InstanceImport {
    pub import_name: String,
    pub exports: Vec<String>,
}

// ---------------------------------------------------------------------------
// Arena — Python-owned via #[pyclass], shared via Py<SystemBuilder>
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
            imports: Vec::new(),
            funcs: Vec::new(),
            exports: Vec::new(),
            start_calls: Vec::new(),
            explicit_start: None,
        }
    }

    // -----------------------------------------------------------------------
    // WAT generation: core module
    // -----------------------------------------------------------------------

    pub fn generate_module_wat(&self, module_id: ModuleId) -> String {
        let md = &self.modules[module_id];
        let mut lines = Vec::new();
        lines.push("(module".to_string());

        // Imports
        for (i, imp) in md.imports.iter().enumerate() {
            let params = if imp.params.is_empty() {
                String::new()
            } else {
                format!(" (param {})", imp.params.join(" "))
            };
            let results = if imp.results.is_empty() {
                String::new()
            } else {
                format!(" (result {})", imp.results.join(" "))
            };
            lines.push(format!(
                "  (import \"{}\" \"{}\" (func $f{i}{params}{results}))",
                imp.module, imp.name
            ));
        }

        // Defined functions
        for &func_id in &md.funcs {
            let fb = &self.funcs[func_id];
            let params = if fb.params.is_empty() {
                String::new()
            } else {
                format!(" (param {})", fb.params.join(" "))
            };
            let results = if fb.results.is_empty() {
                String::new()
            } else {
                format!(" (result {})", fb.results.join(" "))
            };
            let locals = if fb.locals.is_empty() {
                String::new()
            } else {
                let local_decls: Vec<String> =
                    fb.locals.iter().map(|t| format!("(local {t})")).collect();
                format!(" {}", local_decls.join(" "))
            };
            let body = if fb.body.is_empty() {
                String::new()
            } else {
                format!(" {}", fb.body.join(" "))
            };
            lines.push(format!(
                "  (func $f{}{params}{results}{locals}{body})",
                fb.index
            ));
        }

        // Start function
        if let Some(start_idx) = md.explicit_start {
            lines.push(format!("  (start $f{start_idx})"));
        } else if !md.start_calls.is_empty() {
            let start_idx = md.imports.len() + md.funcs.len();
            let calls = md.start_calls.join(" ");
            lines.push(format!("  (func $f{start_idx} {calls})"));
            lines.push(format!("  (start $f{start_idx})"));
        }

        // Exports
        for entry in &md.exports {
            match entry {
                ExportEntry::NoOp(name) => {
                    lines.push(format!("  (func $export__{name} (export \"{name}\"))"));
                }
                ExportEntry::Explicit(name, func_idx) => {
                    lines.push(format!("  (export \"{name}\" (func $f{func_idx}))"));
                }
            }
        }

        lines.push(")".to_string());
        lines.join("\n")
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

        let mut lines = Vec::new();
        lines.push("(component".to_string());

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
        let inner_lines: Vec<&str> = module_wat.lines().collect();
        if inner_lines.len() <= 1 {
            lines.push(format!("  (core module $m {module_wat})"));
        } else {
            let first = inner_lines[0].replace("(module", "(core module $m");
            lines.push(format!("  {first}"));
            for line in &inner_lines[1..] {
                lines.push(format!("  {line}"));
            }
        }

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

        // 6. Component exports (lifted)
        for entry in &md.exports {
            match entry {
                ExportEntry::NoOp(name) => {
                    lines.push(format!(
                        "  (func $export__{name}_lifted (canon lift (core func $i \"{name}\")))"
                    ));
                    lines.push(format!(
                        "  (export \"{name}\" (func $export__{name}_lifted))"
                    ));
                }
                ExportEntry::Explicit(name, _) => {
                    lines.push(format!(
                        "  (func ${name}_lifted (canon lift (core func $i \"{name}\")))"
                    ));
                    lines.push(format!("  (export \"{name}\" (func ${name}_lifted))"));
                }
            }
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
        let inner_lines: Vec<&str> = module_wat.lines().collect();
        let mut lines = vec!["(component".to_string()];
        let first = inner_lines[0].replace("(module", "(core module $m");
        lines.push(format!("  {first}"));
        for line in &inner_lines[1..] {
            lines.push(format!("  {line}"));
        }
        lines.push("  (core instance $i (instantiate $m))".to_string());
        lines.push(")".to_string());
        lines.join("\n")
    }
}

// ---------------------------------------------------------------------------
// Hash extraction helpers
// ---------------------------------------------------------------------------

pub fn extract_hash(obj: &Bound<'_, PyAny>) -> PyResult<covalence_hash::O256> {
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
    // ContainerBuilder: read its built_hash
    if let Ok(cb) = obj.extract::<PyRef<crate::container_builder::ContainerBuilder>>() {
        let sys = cb.system.lock().unwrap();
        let hash = sys.containers[cb.id].built_hash.ok_or_else(|| {
            PyValueError::new_err("ContainerBuilder must be built before use as hash")
        })?;
        return Ok(hash);
    }
    Err(PyTypeError::new_err(
        "expected O256, hex string, Container, Component, or ContainerBuilder",
    ))
}

pub fn extract_hash_for_container(obj: &Bound<'_, PyAny>) -> PyResult<covalence_hash::O256> {
    if let Ok(o) = obj.extract::<PyRef<O256>>() {
        return Ok(o.0);
    }
    if let Ok(hex) = obj.extract::<String>() {
        return covalence_hash::O256::from_hex(&hex)
            .ok_or_else(|| PyValueError::new_err("invalid hex hash"));
    }
    if let Ok(c) = obj.extract::<PyRef<Container>>() {
        return Ok(c.content_hash());
    }
    if let Ok(c) = obj.extract::<PyRef<Component>>() {
        return Ok(c.content_hash());
    }
    Err(PyTypeError::new_err(
        "expected O256, hex string, Container, or Component",
    ))
}
