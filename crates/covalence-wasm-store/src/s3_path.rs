//! Composer example: an "S3 path" store that routes reads by
//! constructing `prefix + hex(key)` and forwarding to an upstream
//! store.
//!
//! The prefix is embedded as a data segment at build time, so each
//! `(prefix, build) → component bytes` mapping is deterministic and
//! the component's content hash pins the prefix. Same identity
//! contract as `single_blob` and `merge`.
//!
//! For the MVP the upstream is a regular `cov:store/upstream` —
//! the composer treats it as if it were a string-keyed store, and
//! whatever backs it (in-memory test, a real S3 KV adapter, …) just
//! has to interpret the lowered `list<u8>` key as a UTF-8 path.
//! Once `covalence-wasm-kv` lands, this composer becomes the natural
//! first user of `cov:kv/upstream` instead.
//!
//! Memory layout (single page initially; cabi_realloc grows it):
//!   `[   0, PREFIX_LEN)`   — embedded prefix bytes
//!   `[ 256,        512)`   — backings handle array (up to 64 × i32)
//!   `[ 512,        516)`   — backings count
//!   `[1024,         ∞)`    — cabi_realloc bump heap (path buffers,
//!                            return areas)

use covalence_wasm::{WasmError, compile_wat, encode_core_as_component_for};

const STORE_WIT: &str = include_str!("../../covalence-wasm/wit/store.wit");

/// Errors from [`build_component`].
#[derive(Debug, thiserror::Error)]
pub enum BuildError {
    #[error("wasm: {0}")]
    Wasm(#[from] WasmError),
    /// Prefix can't share data-segment offset 0 with the backings
    /// array at offset 256 — keep prefixes well under that to stay
    /// in the cheap fixed layout. Realistic S3-style prefixes are
    /// tens of bytes; anything bigger is almost certainly a bug.
    #[error("prefix too long: {0} bytes (max 256)")]
    PrefixTooLong(usize),
}

/// Generate the WAT source for an s3-path composer with the given
/// `prefix`. The prefix is embedded as a data segment; the resulting
/// component routes `store.get(key) → upstream.get(prefix + hex(key))`.
pub fn s3_path_wat(prefix: &str) -> Result<String, BuildError> {
    let prefix_bytes = prefix.as_bytes();
    if prefix_bytes.len() >= 256 {
        return Err(BuildError::PrefixTooLong(prefix_bytes.len()));
    }
    let prefix_data = wat_escape_bytes(prefix_bytes);
    let prefix_len = prefix_bytes.len() as u32;

    Ok(format!(
        r#"(module
  ;; Imports from upstream api.
  (import "cov:store/upstream@0.1.0" "[method]store.contains"
    (func $upstream_contains (param i32 i32 i32) (result i32)))
  (import "cov:store/upstream@0.1.0" "[method]store.get"
    (func $upstream_get (param i32 i32 i32 i32)))
  (import "cov:store/upstream@0.1.0" "[method]store.head"
    (func $upstream_head (param i32 i32 i32 i32)))

  ;; Synthesised by wit-component for our exported `store` resource.
  (import "[export]cov:store/api@0.1.0" "[resource-new]store"
    (func $resource_new_store (param i32) (result i32)))

  (memory (export "memory") 1)

  ;; Embedded prefix at offset 0.
  (data (i32.const 0) "{prefix_data}")

  (global $PREFIX_OFF i32 (i32.const 0))
  (global $PREFIX_LEN i32 (i32.const {prefix_len}))
  (global $BACKINGS_ARR i32 (i32.const 256))
  (global $BACKINGS_CNT i32 (i32.const 512))
  (global $BUMP_PTR (mut i32) (i32.const 1024))

  ;; ─── Hex helpers ─────────────────────────────────────────────────────
  ;; 0..15 -> '0'..'9' or 'a'..'f' (lowercase).
  (func $hex_digit (param $n i32) (result i32)
    (if (i32.lt_u (local.get $n) (i32.const 10))
      (then (return (i32.add (local.get $n) (i32.const 48)))))
    (i32.add (local.get $n) (i32.const 87)))

  ;; Write 2 hex chars for $byte at $out. Returns out + 2.
  (func $write_hex (param $out i32) (param $byte i32) (result i32)
    (i32.store8 (local.get $out)
      (call $hex_digit (i32.shr_u (local.get $byte) (i32.const 4))))
    (i32.store8 (i32.add (local.get $out) (i32.const 1))
      (call $hex_digit (i32.and (local.get $byte) (i32.const 15))))
    (i32.add (local.get $out) (i32.const 2)))

  ;; ─── Build path = prefix + hex(key) at $out. Returns total length. ───
  (func $build_path
    (param $out i32) (param $key_ptr i32) (param $key_len i32) (result i32)
    (local $i i32) (local $cur i32)
    (local.set $i (i32.const 0))
    (block $brk_pfx
      (loop $lp_pfx
        (br_if $brk_pfx (i32.ge_u (local.get $i) (global.get $PREFIX_LEN)))
        (i32.store8
          (i32.add (local.get $out) (local.get $i))
          (i32.load8_u (i32.add (global.get $PREFIX_OFF) (local.get $i))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $lp_pfx)))
    (local.set $cur (i32.add (local.get $out) (global.get $PREFIX_LEN)))
    (local.set $i (i32.const 0))
    (block $brk_hex
      (loop $lp_hex
        (br_if $brk_hex (i32.ge_u (local.get $i) (local.get $key_len)))
        (local.set $cur
          (call $write_hex
            (local.get $cur)
            (i32.load8_u (i32.add (local.get $key_ptr) (local.get $i)))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $lp_hex)))
    (i32.sub (local.get $cur) (local.get $out)))

  ;; ─── Allocate a path buffer and fill it with prefix + hex(key). ──────
  ;; Returns (path_ptr, path_len) via stashing path_len at $LEN_OUT.
  (global $LEN_OUT (mut i32) (i32.const 0))
  (func $alloc_and_build_path
    (param $key_ptr i32) (param $key_len i32) (result i32)
    (local $path_len i32) (local $path_ptr i32)
    (local.set $path_len
      (i32.add (global.get $PREFIX_LEN)
               (i32.shl (local.get $key_len) (i32.const 1))))
    (local.set $path_ptr
      (call $cabi_realloc
        (i32.const 0) (i32.const 0) (i32.const 1) (local.get $path_len)))
    (drop (call $build_path
      (local.get $path_ptr) (local.get $key_ptr) (local.get $key_len)))
    (global.set $LEN_OUT (local.get $path_len))
    (local.get $path_ptr))

  ;; ─── compose.build(backings: list<store>) ────────────────────────────
  (func (export "cov:store/compose@0.1.0#build")
    (param $list_ptr i32) (param $list_len i32)
    (local $i i32) (local $src i32) (local $dst i32)
    (if (i32.gt_u (local.get $list_len) (i32.const 64)) (then (unreachable)))
    (i32.store (global.get $BACKINGS_CNT) (local.get $list_len))
    (local.set $i (i32.const 0))
    (block $brk
      (loop $lp
        (br_if $brk (i32.ge_u (local.get $i) (local.get $list_len)))
        (local.set $src
          (i32.add (local.get $list_ptr) (i32.shl (local.get $i) (i32.const 2))))
        (local.set $dst
          (i32.add (global.get $BACKINGS_ARR) (i32.shl (local.get $i) (i32.const 2))))
        (i32.store (local.get $dst) (i32.load (local.get $src)))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $lp))))

  ;; ─── api.open() -> store ─────────────────────────────────────────────
  (func (export "cov:store/api@0.1.0#open") (result i32)
    (call $resource_new_store (i32.const 0)))

  ;; ─── api.store.contains(self, key) -> bool ───────────────────────────
  (func (export "cov:store/api@0.1.0#[method]store.contains")
    (param $self i32) (param $key_ptr i32) (param $key_len i32) (result i32)
    (local $i i32) (local $n i32) (local $h i32)
    (local $path_ptr i32) (local $path_len i32)
    (local.set $path_ptr
      (call $alloc_and_build_path (local.get $key_ptr) (local.get $key_len)))
    (local.set $path_len (global.get $LEN_OUT))
    (local.set $n (i32.load (global.get $BACKINGS_CNT)))
    (local.set $i (i32.const 0))
    (block $brk
      (loop $lp
        (br_if $brk (i32.ge_u (local.get $i) (local.get $n)))
        (local.set $h
          (i32.load
            (i32.add (global.get $BACKINGS_ARR) (i32.shl (local.get $i) (i32.const 2)))))
        (if (call $upstream_contains
              (local.get $h) (local.get $path_ptr) (local.get $path_len))
          (then (return (i32.const 1))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $lp)))
    (i32.const 0))

  ;; ─── api.store.get(self, key) -> option<list<u8>> ────────────────────
  (func (export "cov:store/api@0.1.0#[method]store.get")
    (param $self i32) (param $key_ptr i32) (param $key_len i32) (result i32)
    (local $i i32) (local $n i32) (local $h i32)
    (local $path_ptr i32) (local $path_len i32)
    (local $up_ra i32) (local $my_ra i32)
    (local.set $my_ra
      (call $cabi_realloc (i32.const 0) (i32.const 0) (i32.const 4) (i32.const 12)))
    (local.set $path_ptr
      (call $alloc_and_build_path (local.get $key_ptr) (local.get $key_len)))
    (local.set $path_len (global.get $LEN_OUT))
    (local.set $n (i32.load (global.get $BACKINGS_CNT)))
    (local.set $i (i32.const 0))
    (block $done
      (loop $lp
        (br_if $done (i32.ge_u (local.get $i) (local.get $n)))
        (local.set $h
          (i32.load
            (i32.add (global.get $BACKINGS_ARR) (i32.shl (local.get $i) (i32.const 2)))))
        (local.set $up_ra
          (call $cabi_realloc (i32.const 0) (i32.const 0) (i32.const 4) (i32.const 12)))
        (call $upstream_get
          (local.get $h) (local.get $path_ptr) (local.get $path_len) (local.get $up_ra))
        (if (i32.eq (i32.load8_u (local.get $up_ra)) (i32.const 1))
          (then
            (i32.store8 (local.get $my_ra) (i32.const 1))
            (i32.store offset=4 (local.get $my_ra)
              (i32.load offset=4 (local.get $up_ra)))
            (i32.store offset=8 (local.get $my_ra)
              (i32.load offset=8 (local.get $up_ra)))
            (return (local.get $my_ra))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $lp)))
    (i32.store8 (local.get $my_ra) (i32.const 0))
    (local.get $my_ra))

  ;; ─── api.store.head(self, key) -> option<blob-info> ──────────────────
  (func (export "cov:store/api@0.1.0#[method]store.head")
    (param $self i32) (param $key_ptr i32) (param $key_len i32) (result i32)
    (local $i i32) (local $n i32) (local $h i32)
    (local $path_ptr i32) (local $path_len i32)
    (local $up_ra i32) (local $my_ra i32)
    (local.set $my_ra
      (call $cabi_realloc (i32.const 0) (i32.const 0) (i32.const 8) (i32.const 16)))
    (local.set $path_ptr
      (call $alloc_and_build_path (local.get $key_ptr) (local.get $key_len)))
    (local.set $path_len (global.get $LEN_OUT))
    (local.set $n (i32.load (global.get $BACKINGS_CNT)))
    (local.set $i (i32.const 0))
    (block $done
      (loop $lp
        (br_if $done (i32.ge_u (local.get $i) (local.get $n)))
        (local.set $h
          (i32.load
            (i32.add (global.get $BACKINGS_ARR) (i32.shl (local.get $i) (i32.const 2)))))
        (local.set $up_ra
          (call $cabi_realloc (i32.const 0) (i32.const 0) (i32.const 8) (i32.const 16)))
        (call $upstream_head
          (local.get $h) (local.get $path_ptr) (local.get $path_len) (local.get $up_ra))
        (if (i32.eq (i32.load8_u (local.get $up_ra)) (i32.const 1))
          (then
            (i32.store8 (local.get $my_ra) (i32.const 1))
            (i64.store offset=8 (local.get $my_ra)
              (i64.load offset=8 (local.get $up_ra)))
            (return (local.get $my_ra))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $lp)))
    (i32.store8 (local.get $my_ra) (i32.const 0))
    (local.get $my_ra))

  ;; ─── cabi_realloc — bump allocator + memory growth ───────────────────
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
    ))
}

/// Build a fully validated s3-path composer component.
///
/// The result implements `cov:store/api` via routing
/// `key → upstream.get(prefix + hex(key))`. Use [`WasmStore::compose`]
/// to instantiate with N upstream stores (typically N = 1 for the
/// S3 case).
pub fn build_component(prefix: &str) -> Result<Vec<u8>, BuildError> {
    let wat = s3_path_wat(prefix)?;
    let core = compile_wat(&wat).map_err(BuildError::Wasm)?;
    encode_core_as_component_for(&core, STORE_WIT, "composer").map_err(BuildError::Wasm)
}

/// Hex-encode bytes the same way the composer does. Useful for
/// tests building stub upstream stores keyed by the encoded path.
pub fn hex_encode(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    for &b in bytes {
        out.push_str(&format!("{b:02x}"));
    }
    out
}

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
    fn builds_component_for_simple_prefix() {
        let bytes = build_component("blobs/").expect("build");
        assert_eq!(&bytes[..4], b"\0asm");
    }

    #[test]
    fn rejects_oversize_prefix() {
        let huge = "x".repeat(300);
        let err = build_component(&huge).unwrap_err();
        assert!(matches!(err, BuildError::PrefixTooLong(_)));
    }

    #[test]
    fn hex_encode_round() {
        assert_eq!(hex_encode(&[]), "");
        assert_eq!(hex_encode(&[0x00, 0xab, 0xff]), "00abff");
    }

    #[test]
    fn distinct_prefix_distinct_bytes() {
        // The prefix is data-segment-embedded, so each prefix
        // produces a distinct component binary — the identity
        // contract still holds.
        let a = build_component("a/").unwrap();
        let b = build_component("b/").unwrap();
        assert_ne!(a, b);
    }
}
