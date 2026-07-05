//! Single-blob example component: knows one (hash → bytes) pair from
//! data segments, returns the bytes on a hash hit, and reports
//! "absent" for every other key.
//!
//! Used as the round-trip exemplar for the [`WasmStore`](crate::WasmStore)
//! adapter — small enough to inspect by hand, exercises every export
//! in `cov:store/api@0.1.0`, and demonstrates the WAT-level wrapper
//! that the canonical ABI expects.
//!
//! The hash and blob are committed as `(data ...)` segments at known
//! offsets in the component's linear memory; the read path compares
//! the incoming `key` byte-for-byte against the embedded hash and
//! either returns `Some(blob)` or `None`. No allocation, no
//! cabi_realloc usage beyond the canonical-ABI return areas.

use covalence_store::StoreManifest;
use covalence_wasm::{WasmError, compile_wat, encode_core_as_component_for};

use crate::manifest::{ManifestError, embed_manifest};

const STORE_WIT: &str = include_str!("../../core/wit/store.wit");

/// The WIT package text that single-blob components target.
///
/// Re-exposed so consumers (tests, fuzzers, alternative implementers)
/// can hand it to [`encode_core_as_component`](covalence_wasm::encode_core_as_component) without rediscovering
/// the path.
pub fn store_wit() -> &'static str {
    STORE_WIT
}

/// Generate the WAT source for a single-blob store containing
/// exactly one (hash → blob) entry.
///
/// Targets the `leaf` world from `cov:store@0.1.0` — exports a
/// `store` resource (singleton, `rep = 0`) plus an `open()` factory
/// that hands a fresh handle to the host. The resource methods
/// receive the handle as their first parameter and ignore it (the
/// store has no per-handle state).
pub fn single_blob_wat(hash: &[u8], blob: &[u8]) -> String {
    // Layout — first segment is the hash at offset 0; blob follows at
    // offset 256 to leave headroom for tiny canonical-ABI return
    // areas if we ever stop allocating them via cabi_realloc. The
    // bump heap starts well past both, page-aligned.
    let hash_off: u32 = 0;
    let blob_off: u32 = 256;
    let bump_start: u32 = align_up(blob_off + blob.len() as u32 + 256, 16);
    // memory.size is measured in 64KiB pages; cover both data + a
    // little scratch for the canonical-ABI return areas.
    let needed_bytes = bump_start + 4096;
    let pages = needed_bytes.div_ceil(65536).max(1);

    let hash_data = wat_escape_bytes(hash);
    let blob_data = wat_escape_bytes(blob);
    let hash_len = hash.len() as u32;
    let blob_len = blob.len() as u32;

    format!(
        r#"(module
  ;; Imported intrinsic for the exported `store` resource: wraps a
  ;; rep (i32) as a handle (i32). wit-component synthesises the
  ;; implementation; the [export]<iface> prefix marks the import as
  ;; provided by the host's runtime, not by another component.
  (import "[export]cov:store/api@0.1.0" "[resource-new]store"
    (func $resource_new_store (param i32) (result i32)))

  (memory (export "memory") {pages})

  ;; Embedded hash and blob at fixed offsets.
  (data (i32.const {hash_off}) "{hash_data}")
  (data (i32.const {blob_off}) "{blob_data}")

  (global $HASH_OFF i32 (i32.const {hash_off}))
  (global $HASH_LEN i32 (i32.const {hash_len}))
  (global $BLOB_OFF i32 (i32.const {blob_off}))
  (global $BLOB_LEN i32 (i32.const {blob_len}))
  (global $BUMP_PTR (mut i32) (i32.const {bump_start}))

  ;; ─── Byte-equality probe ─────────────────────────────────────────────
  ;; Returns 1 iff (key_ptr, key_len) byte-equals the embedded hash.
  (func $matches (param $key_ptr i32) (param $key_len i32) (result i32)
    (local $i i32)
    (if (i32.ne (local.get $key_len) (global.get $HASH_LEN))
      (then (return (i32.const 0))))
    (local.set $i (i32.const 0))
    (block $done
      (loop $lp
        (br_if $done (i32.ge_u (local.get $i) (global.get $HASH_LEN)))
        (if (i32.ne
              (i32.load8_u (i32.add (local.get $key_ptr) (local.get $i)))
              (i32.load8_u (i32.add (global.get $HASH_OFF) (local.get $i))))
          (then (return (i32.const 0))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $lp)))
    (i32.const 1))

  ;; ─── open() -> store ─────────────────────────────────────────────────
  ;; The store is a singleton; rep = 0 is the only valid value. The
  ;; imported `[resource-new]store` wraps it as a fresh handle.
  (func (export "cov:store/api@0.1.0#open") (result i32)
    (call $resource_new_store (i32.const 0)))

  ;; ─── store.get(key) -> option<list<u8>> ──────────────────────────────
  ;; First param is the resource handle (rep = 0, ignored). Return
  ;; area layout (4-byte aligned): [tag:1][pad:3][ptr:4][len:4].
  (func (export "cov:store/api@0.1.0#[method]store.get")
    (param $self i32) (param $key_ptr i32) (param $key_len i32) (result i32)
    (local $ra i32)
    (local.set $ra
      (call $cabi_realloc (i32.const 0) (i32.const 0) (i32.const 4) (i32.const 12)))
    (if (call $matches (local.get $key_ptr) (local.get $key_len))
      (then
        (i32.store8 (local.get $ra) (i32.const 1))
        (i32.store offset=4 (local.get $ra) (global.get $BLOB_OFF))
        (i32.store offset=8 (local.get $ra) (global.get $BLOB_LEN)))
      (else
        (i32.store8 (local.get $ra) (i32.const 0))))
    (local.get $ra))

  ;; ─── store.contains(key) -> bool ─────────────────────────────────────
  (func (export "cov:store/api@0.1.0#[method]store.contains")
    (param $self i32) (param $key_ptr i32) (param $key_len i32) (result i32)
    (call $matches (local.get $key_ptr) (local.get $key_len)))

  ;; ─── store.head(key) -> option<blob-info> ────────────────────────────
  ;; option<record{{size:u64}}> RA (8-byte aligned): [tag:1][pad:7][size:8].
  (func (export "cov:store/api@0.1.0#[method]store.head")
    (param $self i32) (param $key_ptr i32) (param $key_len i32) (result i32)
    (local $ra i32)
    (local.set $ra
      (call $cabi_realloc (i32.const 0) (i32.const 0) (i32.const 8) (i32.const 16)))
    (if (call $matches (local.get $key_ptr) (local.get $key_len))
      (then
        (i32.store8 (local.get $ra) (i32.const 1))
        (i64.store offset=8 (local.get $ra)
          (i64.extend_i32_u (global.get $BLOB_LEN))))
      (else
        (i32.store8 (local.get $ra) (i32.const 0))))
    (local.get $ra))

  ;; ─── cabi_realloc: bump allocator + memory growth ────────────────────
  (func $cabi_realloc
    (param $orig_ptr i32) (param $orig_size i32)
    (param $align i32) (param $new_size i32) (result i32)
    (local $bump i32) (local $mask i32) (local $aligned i32)
    (local $end i32) (local $cur_bytes i32) (local $need_pages i32)
    (if (i32.ne (local.get $orig_ptr) (i32.const 0)) (then (unreachable)))
    (local.set $bump (global.get $BUMP_PTR))
    (local.set $mask (i32.sub (local.get $align) (i32.const 1)))
    (local.set $aligned
      (i32.and
        (i32.add (local.get $bump) (local.get $mask))
        (i32.xor (local.get $mask) (i32.const -1))))
    (local.set $end (i32.add (local.get $aligned) (local.get $new_size)))
    (local.set $cur_bytes (i32.shl (memory.size) (i32.const 16)))
    (if (i32.gt_u (local.get $end) (local.get $cur_bytes))
      (then
        (local.set $need_pages
          (i32.shr_u
            (i32.add (i32.sub (local.get $end) (local.get $cur_bytes)) (i32.const 0xFFFF))
            (i32.const 16)))
        (if (i32.eq (memory.grow (local.get $need_pages)) (i32.const -1))
          (then (unreachable)))))
    (global.set $BUMP_PTR (local.get $end))
    (local.get $aligned))

  (func (export "cabi_realloc")
    (param i32) (param i32) (param i32) (param i32) (result i32)
    (call $cabi_realloc (local.get 0) (local.get 1) (local.get 2) (local.get 3)))
)
"#
    )
}

/// Errors from [`build_component`].
#[derive(Debug, thiserror::Error)]
pub enum BuildError {
    #[error("wasm: {0}")]
    Wasm(#[from] WasmError),
    #[error("manifest: {0}")]
    Manifest(#[from] ManifestError),
}

/// Build a fully validated component binary that knows one
/// (hash → blob) pair and rejects everything else. Combines the WAT
/// from [`single_blob_wat`] with the `cov:store@0.1.0` `leaf` world
/// via [`encode_core_as_component_for`].
///
/// If `manifest` is provided, it is JSON-encoded and appended as a
/// `cov:store/manifest` custom section, making the component
/// self-describing — the output binary's content hash then pins both
/// the code and the metadata.
pub fn build_component(
    hash: &[u8],
    blob: &[u8],
    manifest: Option<&StoreManifest>,
) -> Result<Vec<u8>, BuildError> {
    let wat = single_blob_wat(hash, blob);
    let core = compile_wat(&wat)?;
    let component = encode_core_as_component_for(&core, STORE_WIT, "leaf")?;
    Ok(match manifest {
        Some(m) => embed_manifest(&component, m)?,
        None => component,
    })
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn align_up(v: u32, align: u32) -> u32 {
    (v + align - 1) & !(align - 1)
}

/// Render bytes as a WAT data-segment string literal. Every byte is
/// emitted as `\xx` to avoid encoding surprises.
fn wat_escape_bytes(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 4);
    for &b in bytes {
        out.push_str(&format!("\\{b:02x}"));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wat_escapes_bytes_lowercase_hex() {
        assert_eq!(wat_escape_bytes(b""), "");
        assert_eq!(wat_escape_bytes(&[0, 0xab, 0xff]), "\\00\\ab\\ff");
    }

    #[test]
    fn align_up_rounds() {
        assert_eq!(align_up(0, 16), 0);
        assert_eq!(align_up(1, 16), 16);
        assert_eq!(align_up(16, 16), 16);
        assert_eq!(align_up(17, 16), 32);
    }

    #[test]
    fn builds_component_for_tiny_blob() {
        let hash = [0xAB; 32];
        let blob = b"hello world".as_slice();
        let bytes = build_component(&hash, blob, None).expect("component build");
        assert_eq!(&bytes[..4], b"\0asm");
    }

    #[test]
    fn manifest_changes_component_hash() {
        let hash = [0xCD; 32];
        let blob = b"some data".as_slice();
        let bare = build_component(&hash, blob, None).unwrap();
        let with_a = build_component(
            &hash,
            blob,
            Some(&StoreManifest::new("instance-a", "single-blob")),
        )
        .unwrap();
        let with_b = build_component(
            &hash,
            blob,
            Some(&StoreManifest::new("instance-b", "single-blob")),
        )
        .unwrap();
        assert_ne!(bare, with_a);
        assert_ne!(with_a, with_b);
    }
}
