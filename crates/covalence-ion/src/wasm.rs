//! WAT / WASM parsing and serialization.
//!
//! Treats WebAssembly as a subset of Ion's S-expression format:
//! - Parse `.wat` text files
//! - Decode binary `.wasm` to WAT text (preserving custom sections)
//! - Re-encode WAT text back to binary `.wasm`

use std::fmt;

use wasm_encoder::reencode::Reencode;

/// Errors produced by WAT/WASM operations.
#[derive(Debug)]
pub enum WasmError {
    /// WAT parse error (text -> binary).
    Wat(wat::Error),
    /// WASM binary -> WAT print error.
    Print(anyhow::Error),
    /// WASM binary parse/validation error.
    Parser(wasmparser::BinaryReaderError),
    /// WASM encoding error.
    Encode(wasm_encoder::reencode::Error),
}

impl fmt::Display for WasmError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            WasmError::Wat(e) => write!(f, "WAT parse error: {e}"),
            WasmError::Print(e) => write!(f, "WASM print error: {e}"),
            WasmError::Parser(e) => write!(f, "WASM parse error: {e}"),
            WasmError::Encode(e) => write!(f, "WASM encode error: {e}"),
        }
    }
}

impl std::error::Error for WasmError {}

impl From<wat::Error> for WasmError {
    fn from(e: wat::Error) -> Self {
        WasmError::Wat(e)
    }
}

impl From<wasmparser::BinaryReaderError> for WasmError {
    fn from(e: wasmparser::BinaryReaderError) -> Self {
        WasmError::Parser(e)
    }
}

impl From<wasm_encoder::reencode::Error> for WasmError {
    fn from(e: wasm_encoder::reencode::Error) -> Self {
        WasmError::Encode(e)
    }
}

/// Parse a WAT text string into binary WASM bytes.
///
/// Supports both core modules and component model syntax.
pub fn wat_to_wasm(wat_text: &str) -> Result<Vec<u8>, WasmError> {
    Ok(wat::parse_str(wat_text)?)
}

/// Convert binary WASM bytes to WAT text.
///
/// Custom sections are preserved as `(@custom ...)` annotations.
/// Supports both core modules and components.
pub fn wasm_to_wat(wasm_bytes: &[u8]) -> Result<String, WasmError> {
    wasmprinter::print_bytes(wasm_bytes).map_err(WasmError::Print)
}

/// Parse a WAT text file, returning binary WASM.
///
/// This is a convenience wrapper around [`wat_to_wasm`].
pub fn parse_wat(wat_text: &str) -> Result<Vec<u8>, WasmError> {
    wat_to_wasm(wat_text)
}

/// Parse binary WASM and return WAT text.
///
/// This is a convenience wrapper around [`wasm_to_wat`].
pub fn parse_wasm(wasm_bytes: &[u8]) -> Result<String, WasmError> {
    wasm_to_wat(wasm_bytes)
}

/// Roundtrip: decode binary WASM to WAT, then re-encode to binary WASM.
///
/// This is the operation used when saving a modified WAT view of a `.wasm`
/// file: the modified WAT text is parsed back to binary.
pub fn wat_roundtrip(wasm_bytes: &[u8]) -> Result<Vec<u8>, WasmError> {
    let wat_text = wasm_to_wat(wasm_bytes)?;
    wat_to_wasm(&wat_text)
}

/// Re-encode WASM binary through `wasm-encoder`, preserving all sections
/// including custom sections exactly as-is.
///
/// This is useful for normalizing or re-serializing a module without going
/// through the text format.
pub fn reencode_wasm(wasm_bytes: &[u8]) -> Result<Vec<u8>, WasmError> {
    let parser = wasmparser::Parser::new(0);
    let mut module = wasm_encoder::Module::new();
    let mut encoder = wasm_encoder::reencode::RoundtripReencoder;
    encoder.parse_core_module(&mut module, parser, wasm_bytes)?;
    Ok(module.finish())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_minimal_wat() {
        let wat = "(module)";
        let wasm = wat_to_wasm(wat).unwrap();
        assert!(wasm.starts_with(b"\0asm"));
    }

    #[test]
    fn roundtrip_minimal() {
        let wat = "(module)";
        let wasm = wat_to_wasm(wat).unwrap();
        let wat2 = wasm_to_wat(&wasm).unwrap();
        assert!(wat2.contains("module"));
        let wasm2 = wat_to_wasm(&wat2).unwrap();
        assert_eq!(wasm, wasm2);
    }

    #[test]
    fn roundtrip_with_function() {
        let wat = r#"
            (module
                (func $add (param $a i32) (param $b i32) (result i32)
                    local.get $a
                    local.get $b
                    i32.add)
                (export "add" (func $add)))
        "#;
        let wasm = wat_to_wasm(wat).unwrap();
        let wat2 = wasm_to_wat(&wasm).unwrap();
        assert!(wat2.contains("i32.add"));
        assert!(wat2.contains("\"add\""));
        let wasm2 = wat_to_wasm(&wat2).unwrap();
        assert_eq!(wasm, wasm2);
    }

    #[test]
    fn roundtrip_with_memory_and_data() {
        let wat = r#"
            (module
                (memory 1)
                (data (i32.const 0) "hello"))
        "#;
        let wasm = wat_to_wasm(wat).unwrap();
        let wat2 = wasm_to_wat(&wasm).unwrap();
        assert!(wat2.contains("memory"));
        assert!(wat2.contains("hello"));
        let wasm2 = wat_to_wasm(&wat2).unwrap();
        assert_eq!(wasm, wasm2);
    }

    #[test]
    fn custom_section_preserved_through_text_roundtrip() {
        let mut module = wasm_encoder::Module::new();
        module.section(&wasm_encoder::CustomSection {
            name: "my-custom".into(),
            data: b"payload data".into(),
        });
        let wasm = module.finish();

        let wat = wasm_to_wat(&wasm).unwrap();
        assert!(
            wat.contains("my-custom"),
            "custom section name in WAT: {wat}"
        );

        let wasm2 = wat_to_wasm(&wat).unwrap();
        let wat2 = wasm_to_wat(&wasm2).unwrap();
        assert!(
            wat2.contains("my-custom"),
            "custom section preserved after roundtrip: {wat2}"
        );
    }

    #[test]
    fn custom_section_preserved_through_reencode() {
        let mut module = wasm_encoder::Module::new();
        module.section(&wasm_encoder::TypeSection::new());
        module.section(&wasm_encoder::CustomSection {
            name: "test-section".into(),
            data: b"\x01\x02\x03".into(),
        });
        let wasm = module.finish();

        let reencoded = reencode_wasm(&wasm).unwrap();
        let wat = wasm_to_wat(&reencoded).unwrap();
        assert!(
            wat.contains("test-section"),
            "custom section preserved through reencode: {wat}"
        );
    }

    #[test]
    fn invalid_wat_returns_error() {
        let result = wat_to_wasm("(not valid wasm at all)");
        assert!(result.is_err());
    }

    #[test]
    fn invalid_wasm_bytes_returns_error() {
        let result = wasm_to_wat(b"not wasm");
        assert!(result.is_err());
    }

    #[test]
    fn roundtrip_globals_and_tables() {
        let wat = r#"
            (module
                (global $g (mut i32) (i32.const 42))
                (table 1 funcref)
                (func $f (result i32) global.get $g)
                (export "f" (func $f)))
        "#;
        let wasm = wat_to_wasm(wat).unwrap();
        let wat2 = wasm_to_wat(&wasm).unwrap();
        assert!(wat2.contains("global"));
        assert!(wat2.contains("table"));
        let wasm2 = wat_to_wasm(&wat2).unwrap();
        assert_eq!(wasm, wasm2);
    }

    #[test]
    fn roundtrip_imports() {
        let wat = r#"
            (module
                (import "env" "log" (func $log (param i32))))
        "#;
        let wasm = wat_to_wasm(wat).unwrap();
        let wat2 = wasm_to_wat(&wasm).unwrap();
        assert!(wat2.contains("\"env\""));
        assert!(wat2.contains("\"log\""));
        let wasm2 = wat_to_wasm(&wat2).unwrap();
        assert_eq!(wasm, wasm2);
    }

    #[test]
    fn multiple_custom_sections() {
        let mut module = wasm_encoder::Module::new();
        module.section(&wasm_encoder::CustomSection {
            name: "first".into(),
            data: b"aaa".into(),
        });
        module.section(&wasm_encoder::TypeSection::new());
        module.section(&wasm_encoder::CustomSection {
            name: "second".into(),
            data: b"bbb".into(),
        });
        let wasm = module.finish();

        let wat = wasm_to_wat(&wasm).unwrap();
        assert!(wat.contains("first"));
        assert!(wat.contains("second"));

        let wasm2 = wat_to_wasm(&wat).unwrap();
        let wat2 = wasm_to_wat(&wasm2).unwrap();
        assert!(wat2.contains("first"));
        assert!(wat2.contains("second"));
    }
}
