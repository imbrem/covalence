//! Integration tests for WAT/WASM parsing and serialization.
//!
//! Tests use both text (.wat) fixture files and programmatically-generated
//! binary (.wasm) files to verify roundtripping, custom section preservation,
//! and error handling.

use std::fs;
use std::path::PathBuf;

use covalence_wasm::{validate_wat, wasm_to_wat};

fn fixture_path(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join(name)
}

// ---------------------------------------------------------------------------
// WAT text file parsing
// ---------------------------------------------------------------------------

#[test]
fn parse_add_wat_file() {
    let wat = fs::read_to_string(fixture_path("add.wat")).unwrap();
    let wasm = validate_wat(&wat).unwrap();
    assert!(wasm.starts_with(b"\0asm"), "valid WASM header");
    assert!(wasm.len() > 8, "non-trivial module");
}

#[test]
fn parse_imports_wat_file() {
    let wat = fs::read_to_string(fixture_path("imports.wat")).unwrap();
    let wasm = validate_wat(&wat).unwrap();
    assert!(wasm.starts_with(b"\0asm"));
}

#[test]
fn parse_tables_wat_file() {
    let wat = fs::read_to_string(fixture_path("tables.wat")).unwrap();
    let wasm = validate_wat(&wat).unwrap();
    assert!(wasm.starts_with(b"\0asm"));
}

// ---------------------------------------------------------------------------
// Binary WASM → WAT → binary roundtrip
// ---------------------------------------------------------------------------

#[test]
fn roundtrip_add_module() {
    let wat = fs::read_to_string(fixture_path("add.wat")).unwrap();
    let wasm1 = validate_wat(&wat).unwrap();
    let wat2 = wasm_to_wat(&wasm1).unwrap();

    // WAT output should contain key identifiers
    assert!(wat2.contains("\"add\""), "export name present");
    assert!(wat2.contains("\"sub\""), "export name present");
    assert!(wat2.contains("\"increment\""), "export name present");
    assert!(wat2.contains("i32.add"), "instruction present");

    // Re-parse WAT back to binary and verify functional equivalence via WAT
    let wasm2 = validate_wat(&wat2).unwrap();
    let wat3 = wasm_to_wat(&wasm2).unwrap();
    assert_eq!(wat2, wat3, "WAT roundtrip is stable");
}

#[test]
fn roundtrip_imports_module() {
    let wat = fs::read_to_string(fixture_path("imports.wat")).unwrap();
    let wasm1 = validate_wat(&wat).unwrap();
    let wat2 = wasm_to_wat(&wasm1).unwrap();

    assert!(wat2.contains("\"env\""), "import module present");
    assert!(wat2.contains("\"log\""), "import name present");
    assert!(wat2.contains("Hello, WebAssembly!"), "data segment present");

    let wasm2 = validate_wat(&wat2).unwrap();
    let wat3 = wasm_to_wat(&wasm2).unwrap();
    assert_eq!(wat2, wat3, "WAT roundtrip is stable");
}

#[test]
fn roundtrip_tables_module() {
    let wat = fs::read_to_string(fixture_path("tables.wat")).unwrap();
    let wasm1 = validate_wat(&wat).unwrap();
    let wat2 = wasm_to_wat(&wasm1).unwrap();

    assert!(wat2.contains("call_indirect"), "call_indirect present");

    let wasm2 = validate_wat(&wat2).unwrap();
    let wat3 = wasm_to_wat(&wasm2).unwrap();
    assert_eq!(wat2, wat3, "WAT roundtrip is stable");
}

// ---------------------------------------------------------------------------
// Custom section preservation
// ---------------------------------------------------------------------------

#[test]
fn custom_section_preserved_in_add_module() {
    let wat = fs::read_to_string(fixture_path("add.wat")).unwrap();
    let wasm = validate_wat(&wat).unwrap();
    let wat2 = wasm_to_wat(&wasm).unwrap();
    assert!(
        wat2.contains("build-info"),
        "custom section 'build-info' preserved in WAT output: {wat2}"
    );

    // Roundtrip again — still present
    let wasm2 = validate_wat(&wat2).unwrap();
    let wat3 = wasm_to_wat(&wasm2).unwrap();
    assert!(
        wat3.contains("build-info"),
        "custom section preserved through double roundtrip"
    );
}

#[test]
fn custom_section_preserved_in_imports_module() {
    let wat = fs::read_to_string(fixture_path("imports.wat")).unwrap();
    let wasm = validate_wat(&wat).unwrap();
    let wat2 = wasm_to_wat(&wasm).unwrap();
    assert!(
        wat2.contains("source-map"),
        "custom section 'source-map' preserved: {wat2}"
    );
}

#[test]
fn custom_section_with_binary_payload() {
    let mut module = wasm_encoder::Module::new();
    module.section(&wasm_encoder::CustomSection {
        name: "debug-data".into(),
        data: vec![0x00, 0xFF, 0x42, 0x80, 0xFE].into(),
    });
    let wasm = module.finish();

    let wat = wasm_to_wat(&wasm).unwrap();
    assert!(wat.contains("debug-data"));

    let wasm2 = validate_wat(&wat).unwrap();
    let wat2 = wasm_to_wat(&wasm2).unwrap();
    assert!(
        wat2.contains("debug-data"),
        "binary custom section survives roundtrip"
    );
}

// ---------------------------------------------------------------------------
// Binary WASM generation & decoding (no WAT fixture files)
// ---------------------------------------------------------------------------

#[test]
fn decode_programmatic_wasm_binary() {
    let mut module = wasm_encoder::Module::new();

    let mut types = wasm_encoder::TypeSection::new();
    types.ty().function(
        vec![wasm_encoder::ValType::I32],
        vec![wasm_encoder::ValType::I32],
    );
    module.section(&types);

    let mut funcs = wasm_encoder::FunctionSection::new();
    funcs.function(0);
    module.section(&funcs);

    let mut exports = wasm_encoder::ExportSection::new();
    exports.export("double", wasm_encoder::ExportKind::Func, 0);
    module.section(&exports);

    let mut code = wasm_encoder::CodeSection::new();
    let mut f = wasm_encoder::Function::new(vec![]);
    f.instruction(&wasm_encoder::Instruction::LocalGet(0));
    f.instruction(&wasm_encoder::Instruction::LocalGet(0));
    f.instruction(&wasm_encoder::Instruction::I32Add);
    f.instruction(&wasm_encoder::Instruction::End);
    code.function(&f);
    module.section(&code);

    module.section(&wasm_encoder::CustomSection {
        name: "produced-by".into(),
        data: b"covalence-tests".into(),
    });

    let wasm = module.finish();

    // Decode to WAT
    let wat = wasm_to_wat(&wasm).unwrap();
    assert!(wat.contains("\"double\""));
    assert!(wat.contains("i32.add"));
    assert!(wat.contains("produced-by"));

    // Roundtrip back
    let wasm2 = validate_wat(&wat).unwrap();
    assert_eq!(wasm, wasm2);
}

// ---------------------------------------------------------------------------
// Save-modified-WAT workflow (simulating editing a .wasm file's WAT view)
// ---------------------------------------------------------------------------

#[test]
fn save_modified_wat_view() {
    let original_wat = fs::read_to_string(fixture_path("add.wat")).unwrap();
    let original_wasm = validate_wat(&original_wat).unwrap();

    let wat_view = wasm_to_wat(&original_wasm).unwrap();
    assert!(wat_view.contains("i32.add"));

    // "Edit" the WAT: change add to multiply
    let modified_wat = wat_view.replace("i32.add", "i32.mul");
    assert!(modified_wat.contains("i32.mul"));
    assert!(!modified_wat.contains("i32.add"));

    // Re-serialize to binary
    let modified_wasm = validate_wat(&modified_wat).unwrap();
    assert!(modified_wasm.starts_with(b"\0asm"));
    assert_ne!(original_wasm, modified_wasm, "binary changed after edit");

    // Verify the modification stuck
    let verify_wat = wasm_to_wat(&modified_wasm).unwrap();
    assert!(verify_wat.contains("i32.mul"));
    assert!(!verify_wat.contains("i32.add"));
}

#[test]
fn save_modified_wat_preserves_custom_sections() {
    let original_wat = fs::read_to_string(fixture_path("add.wat")).unwrap();
    let original_wasm = validate_wat(&original_wat).unwrap();
    let wat_view = wasm_to_wat(&original_wasm).unwrap();

    let modified_wat = wat_view.replace("i32.sub", "i32.xor");
    let modified_wasm = validate_wat(&modified_wat).unwrap();
    let verify_wat = wasm_to_wat(&modified_wasm).unwrap();

    assert!(verify_wat.contains("i32.xor"), "edit preserved");
    assert!(
        verify_wat.contains("build-info"),
        "custom section preserved after edit"
    );
}

// ---------------------------------------------------------------------------
// Error handling
// ---------------------------------------------------------------------------

#[test]
fn error_on_invalid_wat() {
    let result = validate_wat("(module (func (invalid-instruction)))");
    assert!(result.is_err());
}

#[test]
fn error_on_invalid_wasm_binary() {
    let result = wasm_to_wat(b"\x00\x01\x02\x03");
    assert!(result.is_err());
}

#[test]
fn error_on_truncated_wasm() {
    let result = wasm_to_wat(b"\0asm\x01\x00\x00\x00\x01");
    assert!(result.is_err());
}

#[test]
fn error_on_empty_input() {
    assert!(validate_wat("").is_err());
    assert!(wasm_to_wat(b"").is_err());
}
