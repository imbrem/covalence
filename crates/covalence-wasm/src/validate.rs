use crate::WasmError;

/// Parse WAT text and compile to WASM binary.
///
/// Returns the compiled WASM bytes on success, or a `WasmError::Wat`
/// (which includes line/column info from the `wat` crate) on failure.
pub fn validate_wat(text: &str) -> Result<Vec<u8>, WasmError> {
    wat::parse_str(text)
        .map(|cow| cow.to_vec())
        .map_err(|e| WasmError::Wat(e.to_string()))
}

/// Decompile WASM binary to WAT text.
pub fn wasm_to_wat(bytes: &[u8]) -> Result<String, WasmError> {
    wasmprinter::print_bytes(bytes).map_err(|e| WasmError::Decompile(e.to_string()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn valid_module() {
        let wat = "(module)";
        assert!(validate_wat(wat).is_ok());
    }

    #[test]
    fn valid_component() {
        let wat = "(component)";
        assert!(validate_wat(wat).is_ok());
    }

    #[test]
    fn valid_module_with_func() {
        let wat = r#"(module (func (export "add") (param i32 i32) (result i32) local.get 0 local.get 1 i32.add))"#;
        assert!(validate_wat(wat).is_ok());
    }

    #[test]
    fn invalid_wat_syntax() {
        let wat = "(module (func (invalid_instruction))";
        assert!(validate_wat(wat).is_err());
    }

    #[test]
    fn empty_input() {
        assert!(validate_wat("").is_err());
    }

    #[test]
    fn plain_text_is_invalid() {
        assert!(validate_wat("hello world").is_err());
    }
}
