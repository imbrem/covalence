use std::fmt;

use wasmparser::{Parser, Payload};

use crate::WasmError;

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

/// Parse a WASM module and extract import/export info using wasmparser.
pub fn parse_module(bytes: &[u8]) -> Result<ModuleInfo, WasmError> {
    let parser = Parser::new(0);
    let mut imports = Vec::new();
    let mut exports = Vec::new();

    for payload in parser.parse_all(bytes) {
        let payload = payload.map_err(|e| WasmError::InvalidModule(e.to_string()))?;
        match payload {
            Payload::ImportSection(reader) => {
                for imports_group in reader {
                    let imports_group =
                        imports_group.map_err(|e| WasmError::InvalidModule(e.to_string()))?;
                    for item in imports_group {
                        let (_offset, import) =
                            item.map_err(|e| WasmError::InvalidModule(e.to_string()))?;
                        imports.push((import.module.to_string(), import.name.to_string()));
                    }
                }
            }
            Payload::ExportSection(reader) => {
                for export in reader {
                    let export = export.map_err(|e| WasmError::InvalidModule(e.to_string()))?;
                    exports.push(export.name.to_string());
                }
            }
            _ => {}
        }
    }

    Ok(ModuleInfo { imports, exports })
}

/// Parse a WASM component and extract import/export info using wasmparser.
pub fn parse_component(bytes: &[u8]) -> Result<ComponentInfo, WasmError> {
    let parser = Parser::new(0);
    let mut imports = Vec::new();
    let mut exports = Vec::new();

    for payload in parser.parse_all(bytes) {
        let payload = payload.map_err(|e| WasmError::InvalidComponent(e.to_string()))?;
        match payload {
            Payload::ComponentImportSection(reader) => {
                for import in reader {
                    let import = import.map_err(|e| WasmError::InvalidComponent(e.to_string()))?;
                    imports.push(import.name.name.to_string());
                }
            }
            Payload::ComponentExportSection(reader) => {
                for export in reader {
                    let export = export.map_err(|e| WasmError::InvalidComponent(e.to_string()))?;
                    exports.push(export.name.name.to_string());
                }
            }
            _ => {}
        }
    }

    Ok(ComponentInfo { imports, exports })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_empty_module() {
        let wasm = wat::parse_str("(module)").unwrap();
        let info = parse_module(&wasm).unwrap();
        assert!(info.imports.is_empty());
        assert!(info.exports.is_empty());
    }

    #[test]
    fn parse_module_with_export() {
        let wasm = wat::parse_str(
            r#"(module (func (export "add") (param i32 i32) (result i32) local.get 0 local.get 1 i32.add))"#,
        )
        .unwrap();
        let info = parse_module(&wasm).unwrap();
        assert!(info.imports.is_empty());
        assert_eq!(info.exports, vec!["add"]);
    }

    #[test]
    fn parse_empty_component() {
        let wasm = wat::parse_str("(component)").unwrap();
        let info = parse_component(&wasm).unwrap();
        assert!(info.imports.is_empty());
        assert!(info.exports.is_empty());
    }

    #[test]
    fn invalid_bytes() {
        assert!(parse_module(b"not wasm").is_err());
        assert!(parse_component(b"not wasm").is_err());
    }
}
