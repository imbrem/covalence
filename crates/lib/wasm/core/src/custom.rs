//! Read and append WASM custom sections.
//!
//! Custom sections are id-0 sections with a user-chosen name and an
//! opaque payload. They survive validation, do not affect execution,
//! and may appear at any position in a module or component. We use
//! them to carry covalence-specific metadata (store manifests, build
//! provenance) inside the component binary so the binary's content
//! hash also pins the metadata.
//!
//! Both helpers work on modules and components: the section encoding
//! is identical in both layers (id 0, LEB128 size, LEB128 name length,
//! name bytes, data).

use wasm_encoder::{Component, CustomSection, Module};
use wasmparser::{Parser, Payload};

use crate::{PREAMBLE_LEN, WasmError, is_component};

/// Append a custom section to a WASM module or component binary.
///
/// The returned vec is the original bytes followed by a fully framed
/// `(id 0)` section carrying `name` and `data` (section id + LEB128
/// size + LEB128 name length + name + data). Appending is valid
/// because custom sections may appear at any section position; the
/// resulting binary is byte-identical to the input aside from the
/// appended bytes, so a deterministic builder calling this with the
/// same inputs yields the same output hash.
pub fn append_custom_section(bytes: &[u8], name: &str, data: &[u8]) -> Vec<u8> {
    let section = CustomSection {
        name: name.into(),
        data: data.into(),
    };
    let framed = framed_custom_section(&section, is_component(bytes));
    let mut out = Vec::with_capacity(bytes.len() + framed.len());
    out.extend_from_slice(bytes);
    out.extend_from_slice(&framed);
    out
}

/// Emit a fully framed custom section by piggy-backing on
/// `wasm-encoder`'s module/component section wrapper, then stripping
/// the synthetic preamble. This avoids hand-rolling the LEB128 size
/// header. Both module and component preambles are [`PREAMBLE_LEN`]
/// bytes.
fn framed_custom_section(section: &CustomSection<'_>, component: bool) -> Vec<u8> {
    let bytes = if component {
        let mut comp = Component::new();
        comp.section(section);
        comp.finish()
    } else {
        let mut module = Module::new();
        module.section(section);
        module.finish()
    };
    bytes[PREAMBLE_LEN..].to_vec()
}

/// Find the first custom section whose name equals `name`, returning
/// its payload bytes. Searches both module-level and component-level
/// custom sections.
///
/// Returns `Ok(None)` if no section matches. Returns `Err` if the
/// binary itself fails to parse.
pub fn find_custom_section(bytes: &[u8], name: &str) -> Result<Option<Vec<u8>>, WasmError> {
    for payload in Parser::new(0).parse_all(bytes) {
        let payload = payload.map_err(|e| WasmError::InvalidComponent(e.to_string()))?;
        if let Payload::CustomSection(reader) = payload {
            if reader.name() == name {
                return Ok(Some(reader.data().to_vec()));
            }
        }
    }
    Ok(None)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip_module_custom_section() {
        let wasm = wat::parse_str("(module)").unwrap();
        let with = append_custom_section(&wasm, "cov:test", b"hello");
        let got = find_custom_section(&with, "cov:test").unwrap();
        assert_eq!(got.as_deref(), Some(&b"hello"[..]));
    }

    #[test]
    fn roundtrip_component_custom_section() {
        let wasm = wat::parse_str("(component)").unwrap();
        let with = append_custom_section(&wasm, "cov:test/manifest", b"{}");
        let got = find_custom_section(&with, "cov:test/manifest").unwrap();
        assert_eq!(got.as_deref(), Some(&b"{}"[..]));
    }

    #[test]
    fn missing_section_returns_none() {
        let wasm = wat::parse_str("(component)").unwrap();
        assert!(find_custom_section(&wasm, "cov:absent").unwrap().is_none());
    }

    #[test]
    fn first_match_wins() {
        let wasm = wat::parse_str("(component)").unwrap();
        let a = append_custom_section(&wasm, "cov:dup", b"first");
        let b = append_custom_section(&a, "cov:dup", b"second");
        assert_eq!(
            find_custom_section(&b, "cov:dup").unwrap().as_deref(),
            Some(&b"first"[..])
        );
    }

    #[test]
    fn appending_preserves_existing_validity() {
        // After appending, the binary is still a valid component
        // (re-parsable by parse_component without error).
        let wasm = wat::parse_str("(component)").unwrap();
        let with = append_custom_section(&wasm, "cov:test", b"data");
        crate::parse_component(&with).unwrap();
    }
}
