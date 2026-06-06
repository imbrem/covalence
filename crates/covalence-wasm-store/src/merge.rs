//! Composer example: a "merge" store that forwards every read to
//! its backings.
//!
//! Routing policy:
//! * `contains` — OR across all backings.
//! * `get` — first backing returning `some(blob)` wins.
//! * `head` — first backing returning `some(blob-info)` wins.
//!
//! Exercises the full read-path canonical ABI in both directions:
//!
//! * Exported `store` resource + `open` factory.
//! * Imported `store` resource (the upstream backings) — including
//!   the import-side return-area convention for `option<list<u8>>`
//!   and `option<blob-info>`: non-flat-fitting results are returned
//!   via an extra final i32 param `ret_ptr` that the caller (us)
//!   allocates via its own `cabi_realloc`.
//!
//! Memory layout (single page is plenty for this example):
//!   `[   0,  256)` — bump scratch
//!   `[ 256,  512)` — backings handle array (up to 64 × i32)
//!   `[ 512,  516)` — backings count (u32)
//!   `[1024, ...)`  — cabi_realloc bump heap

use covalence_wasm::{WasmError, compile_wat, encode_core_as_component_for};

const WAT: &str = r#"(module
  ;; Imports from upstream api.
  ;; contains is flat-fitting (1 i32 result, the bool).
  (import "cov:store/upstream@0.1.0" "[method]store.contains"
    (func $upstream_contains (param i32 i32 i32) (result i32)))
  ;; get / head return option<list<u8>> / option<blob-info>: not
  ;; flat-fitting, so the caller passes ret_ptr as a final extra
  ;; param and the import writes into [ret_ptr, ret_ptr + size).
  (import "cov:store/upstream@0.1.0" "[method]store.get"
    (func $upstream_get (param i32 i32 i32 i32)))
  (import "cov:store/upstream@0.1.0" "[method]store.head"
    (func $upstream_head (param i32 i32 i32 i32)))

  ;; Synthesised by wit-component for our exported `store` resource.
  (import "[export]cov:store/api@0.1.0" "[resource-new]store"
    (func $resource_new_store (param i32) (result i32)))

  (memory (export "memory") 1)

  (global $BACKINGS_ARR i32 (i32.const 256))
  (global $BACKINGS_CNT i32 (i32.const 512))
  (global $BUMP_PTR (mut i32) (i32.const 1024))

  ;; ─── compose.build(backings: list<store>) ────────────────────────────
  ;; The list is lowered into our memory as (ptr, len) of i32 handles.
  ;; Copy the handle array into BACKINGS_ARR for later use.
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
  ;; The composed store is a singleton (rep = 0).
  (func (export "cov:store/api@0.1.0#open") (result i32)
    (call $resource_new_store (i32.const 0)))

  ;; ─── api.store.contains(self, key) -> bool ───────────────────────────
  ;; OR over every backing's `contains`.
  (func (export "cov:store/api@0.1.0#[method]store.contains")
    (param $self i32) (param $key_ptr i32) (param $key_len i32) (result i32)
    (local $i i32) (local $n i32) (local $h i32)
    (local.set $n (i32.load (global.get $BACKINGS_CNT)))
    (local.set $i (i32.const 0))
    (block $brk
      (loop $lp
        (br_if $brk (i32.ge_u (local.get $i) (local.get $n)))
        (local.set $h
          (i32.load
            (i32.add (global.get $BACKINGS_ARR) (i32.shl (local.get $i) (i32.const 2)))))
        (if (call $upstream_contains
              (local.get $h) (local.get $key_ptr) (local.get $key_len))
          (then (return (i32.const 1))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $lp)))
    (i32.const 0))

  ;; ─── api.store.get(self, key) -> option<list<u8>> ────────────────────
  ;; First backing returning Some wins; otherwise None.
  ;;
  ;; Both the upstream-call return area ($up_ra, 12 bytes, 4-byte
  ;; aligned) and our own export return area ($my_ra, same shape)
  ;; come from cabi_realloc. After upstream returns Some, the blob
  ;; bytes live in our memory at the ptr the upstream wrote; we just
  ;; forward (ptr, len) — no copy needed.
  (func (export "cov:store/api@0.1.0#[method]store.get")
    (param $self i32) (param $key_ptr i32) (param $key_len i32) (result i32)
    (local $i i32) (local $n i32) (local $h i32)
    (local $up_ra i32) (local $my_ra i32)
    (local.set $n (i32.load (global.get $BACKINGS_CNT)))
    (local.set $my_ra
      (call $cabi_realloc (i32.const 0) (i32.const 0) (i32.const 4) (i32.const 12)))
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
          (local.get $h) (local.get $key_ptr) (local.get $key_len) (local.get $up_ra))
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
  ;; option<record{size:u64}> RA: [tag:1][pad:7][size:8], 8-byte aligned.
  (func (export "cov:store/api@0.1.0#[method]store.head")
    (param $self i32) (param $key_ptr i32) (param $key_len i32) (result i32)
    (local $i i32) (local $n i32) (local $h i32)
    (local $up_ra i32) (local $my_ra i32)
    (local.set $n (i32.load (global.get $BACKINGS_CNT)))
    (local.set $my_ra
      (call $cabi_realloc (i32.const 0) (i32.const 0) (i32.const 8) (i32.const 16)))
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
          (local.get $h) (local.get $key_ptr) (local.get $key_len) (local.get $up_ra))
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
"#;

const STORE_WIT: &str = include_str!("../../covalence-wasm/wit/store.wit");

/// Build a fully validated composer component implementing the
/// "merge" policy on `contains`.
pub fn build_component() -> Result<Vec<u8>, WasmError> {
    let core = compile_wat(WAT)?;
    encode_core_as_component_for(&core, STORE_WIT, "composer")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn merge_composer_builds() {
        let bytes = build_component().expect("build merge composer");
        assert_eq!(&bytes[..4], b"\0asm");
    }
}
