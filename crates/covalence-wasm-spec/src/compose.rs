//! Derive a one-shot `hash` export from a streaming hasher implementation.
//!
//! Hand-written `.wat` files for hash algorithms implement the
//! streaming primitives only — `compress` plus either a resource shape
//! (`[constructor]hasher` / `[method]hasher.update` /
//! `[method]hasher.finalize`) or a stateful shape (`init` / `update` /
//! `finalize`). The one-shot `hash` is mechanically the sequence
//! `(new) → (update _ data) → (finalize _)`, so we synthesise it at
//! WAT level by injecting a new `(func (export "hash") ...)` body just
//! before the closing `)` of the top-level `(module ...)`.
//!
//! All exports go through a single `api` interface so resource methods
//! are host-callable; the kebab-case names are prefixed with
//! `covalence:hash/api@0.1.0#` to land in the interface's export
//! namespace as required by the canonical ABI.
//!
//! Working at WAT level (rather than re-emitting binary) keeps the
//! committed artefacts auditable: a reviewer can diff the original
//! `.wat` against the composed one and see only the wrapper.

use thiserror::Error;

/// Errors from [`compose_one_shot`].
#[derive(Debug, Error)]
pub enum ComposeError {
    #[error("streaming WAT is missing required export `{0}`")]
    MissingExport(&'static str),
    #[error("could not locate the closing paren of (module ...) in WAT source")]
    NoModuleClose,
    #[error("WAT does not match any known streaming shape (resource or stateful)")]
    UnknownShape,
}

/// Which streaming shape does the source implement?
///
/// `compose_one_shot` auto-detects by scanning for export markers; callers
/// (e.g. `rebuild`) can pre-classify by the target WIT for clearer errors,
/// but the detection is unambiguous since the export sets are disjoint.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Shape {
    /// Canonical-ABI resource exports: `[constructor]hasher`,
    /// `[method]hasher.update`, `[method]hasher.finalize`.
    Resource,
    /// World-level exports: `init`, `update`, `finalize`.
    Stateful,
}

/// Append a one-shot `hash` export to a streaming-hasher WAT source.
///
/// The augmented WAT exports an extra `hash(data: list<u8>) -> list<u8>`
/// that internally calls the right streaming sequence for the detected
/// shape. The streaming exports must already be present — we don't
/// synthesise them.
///
/// `compress` must also be present (the unifying primitive across all
/// hash worlds) — we don't strictly need it for the wrapper, but its
/// absence almost always indicates a malformed source so we reject.
pub fn compose_one_shot(streaming_wat: &str) -> Result<String, ComposeError> {
    let shape = detect_shape(streaming_wat)?;
    compose_one_shot_with(streaming_wat, shape)
}

/// Like [`compose_one_shot`] but with an explicit shape hint.
pub fn compose_one_shot_with(
    streaming_wat: &str,
    shape: Shape,
) -> Result<String, ComposeError> {
    require_compress(streaming_wat)?;
    match shape {
        Shape::Resource => require_resource_exports(streaming_wat)?,
        Shape::Stateful => require_stateful_exports(streaming_wat)?,
    }

    let trimmed = streaming_wat.trim_end();
    let close_idx = trimmed
        .rfind(')')
        .ok_or(ComposeError::NoModuleClose)?;
    let head = &trimmed[..close_idx];
    let tail = &trimmed[close_idx..];
    let wrapper = match shape {
        Shape::Resource => RESOURCE_WRAPPER,
        Shape::Stateful => STATEFUL_WRAPPER,
    };

    let mut out = String::with_capacity(streaming_wat.len() + wrapper.len() + 64);
    out.push_str(head);
    out.push('\n');
    out.push_str(wrapper);
    out.push('\n');
    out.push_str(tail);
    out.push('\n');
    Ok(out)
}

/// Prefix every interface-level export gets in the core WAT. Matches
/// the canonical-ABI Legacy mangling for an interface named `api` in
/// package `covalence:hash@0.1.0`.
const PREFIX: &str = "covalence:hash/api@0.1.0#";

fn export_marker(name: &str) -> String {
    format!("(export \"{PREFIX}{name}\"")
}

/// Auto-detect the streaming shape by scanning exports. The resource
/// and stateful shapes are disjoint, so detection is unambiguous when
/// one of them is fully present.
pub fn detect_shape(wat: &str) -> Result<Shape, ComposeError> {
    let has_resource = wat.contains(&export_marker("[constructor]hasher"));
    let has_stateful = wat.contains(&export_marker("init"));
    match (has_resource, has_stateful) {
        (true, false) => Ok(Shape::Resource),
        (false, true) => Ok(Shape::Stateful),
        _ => Err(ComposeError::UnknownShape),
    }
}

fn require_compress(wat: &str) -> Result<(), ComposeError> {
    if !wat.contains(&export_marker("compress")) {
        return Err(ComposeError::MissingExport("compress"));
    }
    Ok(())
}

fn require_resource_exports(wat: &str) -> Result<(), ComposeError> {
    if !wat.contains(&export_marker("[constructor]hasher")) {
        return Err(ComposeError::MissingExport("[constructor]hasher"));
    }
    if !wat.contains(&export_marker("[method]hasher.update")) {
        return Err(ComposeError::MissingExport("[method]hasher.update"));
    }
    if !wat.contains(&export_marker("[method]hasher.finalize")) {
        return Err(ComposeError::MissingExport("[method]hasher.finalize"));
    }
    Ok(())
}

fn require_stateful_exports(wat: &str) -> Result<(), ComposeError> {
    if !wat.contains(&export_marker("init")) {
        return Err(ComposeError::MissingExport("init"));
    }
    if !wat.contains(&export_marker("update")) {
        return Err(ComposeError::MissingExport("update"));
    }
    if !wat.contains(&export_marker("finalize")) {
        return Err(ComposeError::MissingExport("finalize"));
    }
    Ok(())
}

/// Resource-shape wrapper.
///
/// Core-ABI signature for `hash: func(data: list<u8>) -> list<u8>`:
///   `(param $data_ptr i32) (param $data_len i32) (result i32)`
/// The result is a return-area pointer to `{ ptr: i32, len: i32 }`.
///
/// The contract with hand-written WATs is that the kebab-case body
/// functions are also exposed under `$`-internal names:
///   `[constructor]hasher` body  →  `$new_hasher_impl: () -> i32`
///   `[method]hasher.update` body → `$update_impl: (i32 i32 i32)`
///   `[method]hasher.finalize` body → `$finalize_impl: (i32) -> i32`
const RESOURCE_WRAPPER: &str = r#"
  ;; ─── Composed by covalence-wasm-spec::compose_one_shot ───────────────
  ;; One-shot `hash` = [constructor]hasher → update → finalize.
  (func (export "covalence:hash/api@0.1.0#hash") (param $data_ptr i32) (param $data_len i32) (result i32)
    (local $h i32)
    (local.set $h (call $new_hasher_impl))
    (call $update_impl (local.get $h) (local.get $data_ptr) (local.get $data_len))
    (call $finalize_impl (local.get $h)))
"#;

/// Stateful-shape wrapper.
///
/// The body functions are exposed under `$init_impl` / `$update_impl` /
/// `$finalize_impl`. We do not reset the bump allocator here — `init`
/// handles that, so a stateful component that opens with `hash(data)`
/// and then calls `hash(data2)` won't accumulate garbage.
const STATEFUL_WRAPPER: &str = r#"
  ;; ─── Composed by covalence-wasm-spec::compose_one_shot ───────────────
  ;; One-shot `hash` = init → update → finalize.
  (func (export "covalence:hash/api@0.1.0#hash") (param $data_ptr i32) (param $data_len i32) (result i32)
    (call $init_impl)
    (call $update_impl (local.get $data_ptr) (local.get $data_len))
    (call $finalize_impl))
"#;

#[cfg(test)]
mod tests {
    use super::*;

    const RESOURCE_STUB: &str = r#"(module
        (func $new_hasher_impl (result i32) i32.const 0)
        (func $update_impl (param i32 i32 i32))
        (func $finalize_impl (param i32) (result i32) i32.const 0)
        (func (export "covalence:hash/api@0.1.0#[constructor]hasher") (result i32) (call $new_hasher_impl))
        (func (export "covalence:hash/api@0.1.0#[method]hasher.update") (param i32 i32 i32) (call $update_impl (local.get 0) (local.get 1) (local.get 2)))
        (func (export "covalence:hash/api@0.1.0#[method]hasher.finalize") (param i32) (result i32) (call $finalize_impl (local.get 0)))
        (func (export "covalence:hash/api@0.1.0#compress") (param i32 i32 i32 i32) (result i32) i32.const 0)
    )"#;

    const STATEFUL_STUB: &str = r#"(module
        (func $init_impl)
        (func $update_impl (param i32 i32))
        (func $finalize_impl (result i32) i32.const 0)
        (func (export "covalence:hash/api@0.1.0#init") (call $init_impl))
        (func (export "covalence:hash/api@0.1.0#update") (param i32 i32) (call $update_impl (local.get 0) (local.get 1)))
        (func (export "covalence:hash/api@0.1.0#finalize") (result i32) (call $finalize_impl))
        (func (export "covalence:hash/api@0.1.0#compress") (param i32 i32 i32 i32) (result i32) i32.const 0)
    )"#;

    #[test]
    fn detect_resource() {
        assert_eq!(detect_shape(RESOURCE_STUB).unwrap(), Shape::Resource);
    }

    #[test]
    fn detect_stateful() {
        assert_eq!(detect_shape(STATEFUL_STUB).unwrap(), Shape::Stateful);
    }

    #[test]
    fn detect_unknown() {
        assert!(matches!(
            detect_shape("(module)").unwrap_err(),
            ComposeError::UnknownShape
        ));
    }

    #[test]
    fn injects_hash_resource() {
        let out = compose_one_shot(RESOURCE_STUB).unwrap();
        assert!(out.contains("covalence:hash/api@0.1.0#hash"));
        assert!(out.contains("covalence:hash/api@0.1.0#[constructor]hasher"));
    }

    #[test]
    fn injects_hash_stateful() {
        let out = compose_one_shot(STATEFUL_STUB).unwrap();
        assert!(out.contains("covalence:hash/api@0.1.0#hash"));
        assert!(out.contains("covalence:hash/api@0.1.0#init"));
    }

    #[test]
    fn rejects_missing_compress() {
        let wat = r#"(module
            (func (export "covalence:hash/api@0.1.0#[constructor]hasher") (result i32) i32.const 0)
            (func (export "covalence:hash/api@0.1.0#[method]hasher.update") (param i32 i32 i32))
            (func (export "covalence:hash/api@0.1.0#[method]hasher.finalize") (param i32) (result i32) i32.const 0)
        )"#;
        let err = compose_one_shot(wat).unwrap_err();
        assert!(matches!(err, ComposeError::MissingExport("compress")));
    }
}
