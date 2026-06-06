//! Wrap a core WASM module as a component model component against a WIT world.
//!
//! Driven by [`wit_parser::Resolve`] + [`wit_component::ComponentEncoder`].
//! The general recipe is:
//!
//! 1. Parse the WIT text into a `Resolve` and pick the (only) world.
//! 2. Embed a `component-type` custom section into the core wasm so that
//!    `wit-component` knows which world the core module targets.
//! 3. Run `ComponentEncoder::default().module(...).encode()` to produce the
//!    final component binary, wiring the canonical ABI lift/lower glue.
//!
//! The core wasm must export functions using the Legacy mangling that the
//! component encoder recognises: world-level functions are exported by their
//! kebab-case names directly. Resources/lists need a `cabi_realloc` export.

use std::path::Path;

use wit_component::{ComponentEncoder, StringEncoding, embed_component_metadata};
use wit_parser::Resolve;

use crate::WasmError;

/// Wrap a core WASM module as a component, targeting the world described by
/// `wit_world`.
///
/// `wit_world` is the textual WIT source defining the package and world.
/// There must be exactly one world; this picks it automatically.
///
/// The returned bytes are a fully validated component binary.
pub fn encode_core_as_component(
    core_wasm: &[u8],
    wit_world: &str,
) -> Result<Vec<u8>, WasmError> {
    let mut resolve = Resolve::default();
    let pkg = resolve
        .push_str(Path::new("inline.wit"), wit_world)
        .map_err(|e| WasmError::Wit(e.to_string()))?;
    let world = resolve
        .select_world(&[pkg], None)
        .map_err(|e| WasmError::Wit(e.to_string()))?;

    let mut module_bytes = core_wasm.to_vec();
    embed_component_metadata(&mut module_bytes, &resolve, world, StringEncoding::UTF8)
        .map_err(|e| WasmError::Encode(e.to_string()))?;

    let mut encoder = ComponentEncoder::default().validate(true);
    encoder = encoder
        .module(&module_bytes)
        .map_err(|e| WasmError::Encode(e.to_string()))?;
    encoder
        .encode()
        .map_err(|e| WasmError::Encode(e.to_string()))
}

#[cfg(test)]
mod tests {
    use super::*;

    // A trivial core wasm exporting a kebab-case `noop` function that matches
    // a single-world WIT.
    #[test]
    fn encode_trivial_component() {
        let wat = r#"
            (module
              (func (export "noop"))
            )
        "#;
        let core = crate::compile_wat(wat).unwrap();
        let wit = r#"
            package cov:test@0.1.0;
            world test {
              export noop: func();
            }
        "#;
        let comp = encode_core_as_component(&core, wit).unwrap();
        // Magic "\0asm" + component-model layer/version.
        assert_eq!(&comp[..4], b"\0asm");
    }

    #[test]
    fn encode_rejects_bad_wit() {
        let core = crate::compile_wat("(module)").unwrap();
        let err = encode_core_as_component(&core, "not valid wit").unwrap_err();
        assert!(matches!(err, WasmError::Wit(_)));
    }
}
