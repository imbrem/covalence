;; SHA-1 (FIPS PUB 180-4 §6.1) — hand-written WAT, resource-shape world.
;;
;; Implements the canonical-ABI streaming hasher resource defined in
;; `sha1.wit`:
;;   resource hasher { constructor; update; finalize }
;; Plus the `compress` block primitive. The one-shot `hash` is added by
;; `compose_one_shot` during rebuild.
;;
;; Resource ABI (Legacy mangling, sync):
;;   `[constructor]hasher  : () -> i32`    (returns the rep — slot index)
;;   `[method]hasher.update: (i32 ptr i32 len i32)`  → no result
;;   `[method]hasher.finalize: (i32) -> i32`         → ret-area ptr
;; The component encoder lifts these into a `resource hasher` with the
;; canonical handle table. We deliberately do NOT export a destructor;
;; `finalize` consumes the resource (drops the handle on the host side)
;; and freeing the slot is done in-band. If a client drops a handle
;; without calling finalize, the slot leaks until the module instance
;; is gone — acceptable for a reference implementation.
;;
;; Memory layout (single page, 64 KiB):
;;   [    0, 1024) — scratch: W[0..79] message schedule (320 B) + return area
;;   [ 1024, 2048) — 8 hasher slots × 128 B each (see below)
;;   [ 2048,65536) — cabi_realloc bump heap (62 KiB)
;;
;; Hasher slot layout (128 B per slot):
;;   +  0  i32  in_use (0 = free, 1 = active)
;;   +  4  i32×5  H[0..5] (running state, native-endian)
;;   + 24  i32  pending_bytes (count of bytes in pending buffer, 0..64)
;;   + 28  i32  total_len_lo (low 32 bits of total bytes hashed)
;;   + 32  i32  total_len_hi (high 32 bits of total bytes hashed)
;;   + 36 i8×64  pending buffer (incomplete block awaiting more data)
;;
;; The 8-slot cap is a v0 limitation — overflow traps. The stateful
;; variant (`handwritten-stateful`) demonstrates the alternative single-
;; instance-per-hasher model with no handle table at all.

(module
  ;; Canonical-ABI intrinsics for the exported `hasher` resource.
  ;; `[resource-new]hasher` takes a rep (i32) and returns a handle (i32).
  ;; `[resource-rep]hasher` is its inverse — used in methods if you need
  ;; to recover the rep from a borrowed handle (we don't — methods are
  ;; lowered with the rep already substituted).
  (import "[export]covalence:hash/api@0.1.0" "[resource-new]hasher"
    (func $resource_new_hasher (param i32) (result i32)))

  (memory (export "memory") 1)

  ;; ─── Helpers ─────────────────────────────────────────────────────────

  ;; Big-endian i32 load: byte b0 b1 b2 b3 → (b0<<24)|(b1<<16)|(b2<<8)|b3.
  (func $load_be32 (param $ptr i32) (result i32)
    (i32.or
      (i32.or
        (i32.shl (i32.load8_u (local.get $ptr)) (i32.const 24))
        (i32.shl (i32.load8_u (i32.add (local.get $ptr) (i32.const 1))) (i32.const 16)))
      (i32.or
        (i32.shl (i32.load8_u (i32.add (local.get $ptr) (i32.const 2))) (i32.const 8))
        (i32.load8_u (i32.add (local.get $ptr) (i32.const 3))))))

  ;; Big-endian i32 store.
  (func $store_be32 (param $ptr i32) (param $v i32)
    (i32.store8 (local.get $ptr)
      (i32.shr_u (local.get $v) (i32.const 24)))
    (i32.store8 (i32.add (local.get $ptr) (i32.const 1))
      (i32.shr_u (local.get $v) (i32.const 16)))
    (i32.store8 (i32.add (local.get $ptr) (i32.const 2))
      (i32.shr_u (local.get $v) (i32.const 8)))
    (i32.store8 (i32.add (local.get $ptr) (i32.const 3))
      (local.get $v)))

  ;; ─── Core compress (FIPS §6.1.2) ─────────────────────────────────────
  ;;
  ;; state_ptr: 5 native-endian i32 words of running state.
  ;; block_ptr: 64 bytes of input block (BE byte stream).
  ;; out_ptr:   20-byte output (new state, native-endian).
  ;; W[] scratch lives at offset 0; we re-use it for every block.
  (func $compress_block
    (param $state_ptr i32) (param $block_ptr i32) (param $out_ptr i32)
    (local $t i32)
    (local $a i32) (local $b i32) (local $c i32) (local $d i32) (local $e i32)
    (local $h0 i32) (local $h1 i32) (local $h2 i32) (local $h3 i32) (local $h4 i32)
    (local $w_t i32) (local $tmp i32) (local $f i32) (local $k i32)

    (local.set $h0 (i32.load (local.get $state_ptr)))
    (local.set $h1 (i32.load (i32.add (local.get $state_ptr) (i32.const 4))))
    (local.set $h2 (i32.load (i32.add (local.get $state_ptr) (i32.const 8))))
    (local.set $h3 (i32.load (i32.add (local.get $state_ptr) (i32.const 12))))
    (local.set $h4 (i32.load (i32.add (local.get $state_ptr) (i32.const 16))))

    ;; W[0..15] from block (FIPS §6.1.2 step 1).
    (local.set $t (i32.const 0))
    (block $break_init
      (loop $loop_init
        (br_if $break_init (i32.ge_s (local.get $t) (i32.const 16)))
        (i32.store
          (i32.shl (local.get $t) (i32.const 2))
          (call $load_be32
            (i32.add (local.get $block_ptr) (i32.shl (local.get $t) (i32.const 2)))))
        (local.set $t (i32.add (local.get $t) (i32.const 1)))
        (br $loop_init)))

    ;; W[16..79] = ROTL1(W[t-3] ^ W[t-8] ^ W[t-14] ^ W[t-16]).
    (local.set $t (i32.const 16))
    (block $break_ext
      (loop $loop_ext
        (br_if $break_ext (i32.ge_s (local.get $t) (i32.const 80)))
        (local.set $w_t
          (i32.rotl
            (i32.xor
              (i32.xor
                (i32.load (i32.shl (i32.sub (local.get $t) (i32.const 3)) (i32.const 2)))
                (i32.load (i32.shl (i32.sub (local.get $t) (i32.const 8)) (i32.const 2))))
              (i32.xor
                (i32.load (i32.shl (i32.sub (local.get $t) (i32.const 14)) (i32.const 2)))
                (i32.load (i32.shl (i32.sub (local.get $t) (i32.const 16)) (i32.const 2)))))
            (i32.const 1)))
        (i32.store
          (i32.shl (local.get $t) (i32.const 2))
          (local.get $w_t))
        (local.set $t (i32.add (local.get $t) (i32.const 1)))
        (br $loop_ext)))

    ;; Working vars (FIPS §6.1.2 step 2).
    (local.set $a (local.get $h0))
    (local.set $b (local.get $h1))
    (local.set $c (local.get $h2))
    (local.set $d (local.get $h3))
    (local.set $e (local.get $h4))

    ;; 80-round main loop (FIPS §6.1.2 step 3).
    (local.set $t (i32.const 0))
    (block $break_main
      (loop $loop_main
        (br_if $break_main (i32.ge_s (local.get $t) (i32.const 80)))

        (if (i32.lt_s (local.get $t) (i32.const 20))
          (then
            ;; Ch
            (local.set $f
              (i32.or
                (i32.and (local.get $b) (local.get $c))
                (i32.and (i32.xor (local.get $b) (i32.const -1)) (local.get $d))))
            (local.set $k (i32.const 0x5A827999)))
          (else
            (if (i32.lt_s (local.get $t) (i32.const 40))
              (then
                (local.set $f
                  (i32.xor (i32.xor (local.get $b) (local.get $c)) (local.get $d)))
                (local.set $k (i32.const 0x6ED9EBA1)))
              (else
                (if (i32.lt_s (local.get $t) (i32.const 60))
                  (then
                    ;; Maj
                    (local.set $f
                      (i32.or
                        (i32.or
                          (i32.and (local.get $b) (local.get $c))
                          (i32.and (local.get $b) (local.get $d)))
                        (i32.and (local.get $c) (local.get $d))))
                    (local.set $k (i32.const 0x8F1BBCDC)))
                  (else
                    (local.set $f
                      (i32.xor (i32.xor (local.get $b) (local.get $c)) (local.get $d)))
                    (local.set $k (i32.const 0xCA62C1D6))))))))

        ;; T = ROTL5(A) + f + E + K + W[t]
        (local.set $tmp
          (i32.add
            (i32.add
              (i32.add (i32.rotl (local.get $a) (i32.const 5)) (local.get $f))
              (i32.add (local.get $e) (local.get $k)))
            (i32.load (i32.shl (local.get $t) (i32.const 2)))))

        (local.set $e (local.get $d))
        (local.set $d (local.get $c))
        (local.set $c (i32.rotl (local.get $b) (i32.const 30)))
        (local.set $b (local.get $a))
        (local.set $a (local.get $tmp))

        (local.set $t (i32.add (local.get $t) (i32.const 1)))
        (br $loop_main)))

    ;; H += working vars (FIPS §6.1.2 step 4).
    (local.set $h0 (i32.add (local.get $h0) (local.get $a)))
    (local.set $h1 (i32.add (local.get $h1) (local.get $b)))
    (local.set $h2 (i32.add (local.get $h2) (local.get $c)))
    (local.set $h3 (i32.add (local.get $h3) (local.get $d)))
    (local.set $h4 (i32.add (local.get $h4) (local.get $e)))

    (i32.store (local.get $out_ptr) (local.get $h0))
    (i32.store (i32.add (local.get $out_ptr) (i32.const 4)) (local.get $h1))
    (i32.store (i32.add (local.get $out_ptr) (i32.const 8)) (local.get $h2))
    (i32.store (i32.add (local.get $out_ptr) (i32.const 12)) (local.get $h3))
    (i32.store (i32.add (local.get $out_ptr) (i32.const 16)) (local.get $h4)))

  ;; ─── Slot management ─────────────────────────────────────────────────

  ;; Slot 0 base = 1024. Slot stride = 128.
  (func $slot_base (param $handle i32) (result i32)
    (i32.add (i32.const 1024) (i32.shl (local.get $handle) (i32.const 7))))

  ;; Allocate a free slot; trap if all 8 are in use.
  (func $alloc_slot (result i32)
    (local $i i32)
    (local $base i32)
    (local.set $i (i32.const 0))
    (block $break
      (loop $loop
        (br_if $break (i32.ge_s (local.get $i) (i32.const 8)))
        (local.set $base (call $slot_base (local.get $i)))
        (if (i32.eqz (i32.load (local.get $base)))
          (then
            (i32.store (local.get $base) (i32.const 1))
            ;; FIPS §5.3.1 initial H.
            (i32.store (i32.add (local.get $base) (i32.const 4))  (i32.const 0x67452301))
            (i32.store (i32.add (local.get $base) (i32.const 8))  (i32.const 0xEFCDAB89))
            (i32.store (i32.add (local.get $base) (i32.const 12)) (i32.const 0x98BADCFE))
            (i32.store (i32.add (local.get $base) (i32.const 16)) (i32.const 0x10325476))
            (i32.store (i32.add (local.get $base) (i32.const 20)) (i32.const 0xC3D2E1F0))
            (i32.store (i32.add (local.get $base) (i32.const 24)) (i32.const 0))
            (i32.store (i32.add (local.get $base) (i32.const 28)) (i32.const 0))
            (i32.store (i32.add (local.get $base) (i32.const 32)) (i32.const 0))
            (return (local.get $i))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $loop)))
    (unreachable))

  (func $state_ptr (param $handle i32) (result i32)
    (i32.add (call $slot_base (local.get $handle)) (i32.const 4)))

  (func $pending_ptr (param $handle i32) (result i32)
    (i32.add (call $slot_base (local.get $handle)) (i32.const 36)))

  (func $slot_compress (param $handle i32) (param $block_ptr i32)
    (local $sp i32)
    (local.set $sp (call $state_ptr (local.get $handle)))
    (call $compress_block (local.get $sp) (local.get $block_ptr) (local.get $sp)))

  (func $slot_add_total (param $handle i32) (param $n i32)
    (local $base i32)
    (local $lo i32)
    (local $new_lo i32)
    (local.set $base (call $slot_base (local.get $handle)))
    (local.set $lo (i32.load (i32.add (local.get $base) (i32.const 28))))
    (local.set $new_lo (i32.add (local.get $lo) (local.get $n)))
    (i32.store (i32.add (local.get $base) (i32.const 28)) (local.get $new_lo))
    (if (i32.lt_u (local.get $new_lo) (local.get $lo))
      (then
        (i32.store
          (i32.add (local.get $base) (i32.const 32))
          (i32.add
            (i32.load (i32.add (local.get $base) (i32.const 32)))
            (i32.const 1))))))

  ;; ─── Public: compress ────────────────────────────────────────────────
  ;;
  ;; Signature: `compress: func(state: list<u8>, block: list<u8>) -> list<u8>`
  ;; Core ABI: (state_ptr, state_len, block_ptr, block_len) → ret_ptr
  ;; ret area at ret_ptr: { ptr: i32, len: i32 } (8 bytes, 4-aligned).
  (func (export "covalence:hash/api@0.1.0#compress")
    (param $state_ptr i32) (param $state_len i32)
    (param $block_ptr i32) (param $block_len i32)
    (result i32)
    (local $out i32)
    (local $ret i32)
    (local $native_state i32)
    (local $native_out i32)
    (local $i i32)
    (if (i32.ne (local.get $state_len) (i32.const 20)) (then (unreachable)))
    (if (i32.ne (local.get $block_len) (i32.const 64)) (then (unreachable)))
    (local.set $native_state (call $cabi_realloc
      (i32.const 0) (i32.const 0) (i32.const 4) (i32.const 20)))
    (local.set $i (i32.const 0))
    (block $break
      (loop $loop
        (br_if $break (i32.ge_s (local.get $i) (i32.const 5)))
        (i32.store
          (i32.add (local.get $native_state) (i32.shl (local.get $i) (i32.const 2)))
          (call $load_be32
            (i32.add (local.get $state_ptr) (i32.shl (local.get $i) (i32.const 2)))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $loop)))
    (local.set $native_out (call $cabi_realloc
      (i32.const 0) (i32.const 0) (i32.const 4) (i32.const 20)))
    (call $compress_block
      (local.get $native_state) (local.get $block_ptr) (local.get $native_out))
    (local.set $out (call $cabi_realloc
      (i32.const 0) (i32.const 0) (i32.const 1) (i32.const 20)))
    (local.set $i (i32.const 0))
    (block $break
      (loop $loop
        (br_if $break (i32.ge_s (local.get $i) (i32.const 5)))
        (call $store_be32
          (i32.add (local.get $out) (i32.shl (local.get $i) (i32.const 2)))
          (i32.load
            (i32.add (local.get $native_out) (i32.shl (local.get $i) (i32.const 2)))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $loop)))
    (local.set $ret (call $cabi_realloc
      (i32.const 0) (i32.const 0) (i32.const 4) (i32.const 8)))
    (i32.store (local.get $ret) (local.get $out))
    (i32.store (i32.add (local.get $ret) (i32.const 4)) (i32.const 20))
    (local.get $ret))

  ;; ─── Resource: hasher constructor ────────────────────────────────────
  ;;
  ;; `$new_hasher_impl` returns a rep (slot index); the export wrapper
  ;; calls the canonical-ABI `resource.new` intrinsic to wrap it into a
  ;; handle for the host. The composed one-shot `hash` calls
  ;; `$new_hasher_impl` and then `$update_impl` / `$finalize_impl`
  ;; directly on the rep — no resource.new round-trip in the hot path.
  (func $new_hasher_impl (result i32)
    (call $alloc_slot))
  (func (export "covalence:hash/api@0.1.0#[constructor]hasher") (result i32)
    (call $resource_new_hasher (call $new_hasher_impl)))

  ;; ─── Resource: hasher.update ─────────────────────────────────────────
  ;;
  ;; Core ABI: (rep, data_ptr, data_len) → no result.
  (func $update_impl
    (param $handle i32) (param $data_ptr i32) (param $data_len i32)
    (local $base i32) (local $pending i32) (local $i i32) (local $needed i32)
    (local $pbuf i32)
    (local.set $base (call $slot_base (local.get $handle)))
    (local.set $pbuf (call $pending_ptr (local.get $handle)))
    (local.set $pending (i32.load (i32.add (local.get $base) (i32.const 24))))

    (call $slot_add_total (local.get $handle) (local.get $data_len))

    (if (i32.gt_s (local.get $pending) (i32.const 0))
      (then
        (local.set $needed (i32.sub (i32.const 64) (local.get $pending)))
        (if (i32.lt_u (local.get $data_len) (local.get $needed))
          (then
            (local.set $i (i32.const 0))
            (block $break
              (loop $loop
                (br_if $break (i32.ge_s (local.get $i) (local.get $data_len)))
                (i32.store8
                  (i32.add (local.get $pbuf) (i32.add (local.get $pending) (local.get $i)))
                  (i32.load8_u (i32.add (local.get $data_ptr) (local.get $i))))
                (local.set $i (i32.add (local.get $i) (i32.const 1)))
                (br $loop)))
            (i32.store
              (i32.add (local.get $base) (i32.const 24))
              (i32.add (local.get $pending) (local.get $data_len)))
            (return))
          (else
            (local.set $i (i32.const 0))
            (block $break
              (loop $loop
                (br_if $break (i32.ge_s (local.get $i) (local.get $needed)))
                (i32.store8
                  (i32.add (local.get $pbuf) (i32.add (local.get $pending) (local.get $i)))
                  (i32.load8_u (i32.add (local.get $data_ptr) (local.get $i))))
                (local.set $i (i32.add (local.get $i) (i32.const 1)))
                (br $loop)))
            (call $slot_compress (local.get $handle) (local.get $pbuf))
            (local.set $data_ptr (i32.add (local.get $data_ptr) (local.get $needed)))
            (local.set $data_len (i32.sub (local.get $data_len) (local.get $needed)))
            (i32.store (i32.add (local.get $base) (i32.const 24)) (i32.const 0))))))

    (block $break
      (loop $loop
        (br_if $break (i32.lt_u (local.get $data_len) (i32.const 64)))
        (call $slot_compress (local.get $handle) (local.get $data_ptr))
        (local.set $data_ptr (i32.add (local.get $data_ptr) (i32.const 64)))
        (local.set $data_len (i32.sub (local.get $data_len) (i32.const 64)))
        (br $loop)))

    (if (i32.gt_s (local.get $data_len) (i32.const 0))
      (then
        (local.set $i (i32.const 0))
        (block $break2
          (loop $loop2
            (br_if $break2 (i32.ge_s (local.get $i) (local.get $data_len)))
            (i32.store8
              (i32.add (local.get $pbuf) (local.get $i))
              (i32.load8_u (i32.add (local.get $data_ptr) (local.get $i))))
            (local.set $i (i32.add (local.get $i) (i32.const 1)))
            (br $loop2)))
        (i32.store (i32.add (local.get $base) (i32.const 24)) (local.get $data_len)))))
  (func (export "covalence:hash/api@0.1.0#[method]hasher.update")
    (param $handle i32) (param $data_ptr i32) (param $data_len i32)
    (call $update_impl
      (local.get $handle) (local.get $data_ptr) (local.get $data_len)))

  ;; ─── Resource: hasher.finalize ───────────────────────────────────────
  ;;
  ;; Core ABI: (rep) → ret_ptr (8-byte {ptr,len}). FIPS §5.1.1 padding.
  ;; finalize consumes the resource: we free the slot in-band.
  (func $finalize_impl (param $handle i32) (result i32)
    (local $base i32) (local $pbuf i32) (local $pending i32)
    (local $lo i32) (local $hi i32)
    (local $bit_lo i32) (local $bit_hi i32)
    (local $i i32)
    (local $out i32) (local $ret i32)

    (local.set $base (call $slot_base (local.get $handle)))
    (local.set $pbuf (call $pending_ptr (local.get $handle)))
    (local.set $pending (i32.load (i32.add (local.get $base) (i32.const 24))))
    (local.set $lo (i32.load (i32.add (local.get $base) (i32.const 28))))
    (local.set $hi (i32.load (i32.add (local.get $base) (i32.const 32))))

    (local.set $bit_lo (i32.shl (local.get $lo) (i32.const 3)))
    (local.set $bit_hi
      (i32.or
        (i32.shl (local.get $hi) (i32.const 3))
        (i32.shr_u (local.get $lo) (i32.const 29))))

    (i32.store8 (i32.add (local.get $pbuf) (local.get $pending)) (i32.const 0x80))
    (local.set $pending (i32.add (local.get $pending) (i32.const 1)))

    (if (i32.gt_s (local.get $pending) (i32.const 56))
      (then
        (local.set $i (local.get $pending))
        (block $break
          (loop $loop
            (br_if $break (i32.ge_s (local.get $i) (i32.const 64)))
            (i32.store8 (i32.add (local.get $pbuf) (local.get $i)) (i32.const 0))
            (local.set $i (i32.add (local.get $i) (i32.const 1)))
            (br $loop)))
        (call $slot_compress (local.get $handle) (local.get $pbuf))
        (local.set $pending (i32.const 0))))

    (local.set $i (local.get $pending))
    (block $break
      (loop $loop
        (br_if $break (i32.ge_s (local.get $i) (i32.const 56)))
        (i32.store8 (i32.add (local.get $pbuf) (local.get $i)) (i32.const 0))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $loop)))

    (call $store_be32 (i32.add (local.get $pbuf) (i32.const 56)) (local.get $bit_hi))
    (call $store_be32 (i32.add (local.get $pbuf) (i32.const 60)) (local.get $bit_lo))

    (call $slot_compress (local.get $handle) (local.get $pbuf))

    (local.set $out (call $cabi_realloc
      (i32.const 0) (i32.const 0) (i32.const 1) (i32.const 20)))
    (local.set $i (i32.const 0))
    (block $break
      (loop $loop
        (br_if $break (i32.ge_s (local.get $i) (i32.const 5)))
        (call $store_be32
          (i32.add (local.get $out) (i32.shl (local.get $i) (i32.const 2)))
          (i32.load
            (i32.add (call $state_ptr (local.get $handle))
                     (i32.shl (local.get $i) (i32.const 2)))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $loop)))

    ;; finalize consumes the resource — free the slot.
    (i32.store (local.get $base) (i32.const 0))

    (local.set $ret (call $cabi_realloc
      (i32.const 0) (i32.const 0) (i32.const 4) (i32.const 8)))
    (i32.store (local.get $ret) (local.get $out))
    (i32.store (i32.add (local.get $ret) (i32.const 4)) (i32.const 20))
    (local.get $ret))
  (func (export "covalence:hash/api@0.1.0#[method]hasher.finalize") (param $handle i32) (result i32)
    (call $finalize_impl (local.get $handle)))

  ;; ─── cabi_realloc — bump allocator + memory growth ───────────────────
  ;;
  ;; Bump pointer at offset 512 (scratch). Resize / free not supported.
  ;; If the new allocation would run past the end of linear memory we
  ;; grow it in 64 KiB pages until it fits, trapping on grow failure.
  (func $cabi_realloc
    (param $orig_ptr i32) (param $orig_size i32)
    (param $align i32) (param $new_size i32)
    (result i32)
    (local $bump i32) (local $mask i32) (local $aligned i32)
    (local $end i32) (local $cur_bytes i32) (local $need_pages i32)
    (if (i32.ne (local.get $orig_ptr) (i32.const 0)) (then (unreachable)))
    (local.set $bump (i32.load (i32.const 512)))
    (if (i32.eqz (local.get $bump))
      (then (local.set $bump (i32.const 2048))))
    (local.set $mask (i32.sub (local.get $align) (i32.const 1)))
    (local.set $aligned
      (i32.and
        (i32.add (local.get $bump) (local.get $mask))
        (i32.xor (local.get $mask) (i32.const -1))))
    (local.set $end (i32.add (local.get $aligned) (local.get $new_size)))
    ;; Grow memory if `end` exceeds current size (in bytes).
    (local.set $cur_bytes (i32.shl (memory.size) (i32.const 16)))
    (if (i32.gt_u (local.get $end) (local.get $cur_bytes))
      (then
        (local.set $need_pages
          (i32.shr_u
            (i32.add
              (i32.sub (local.get $end) (local.get $cur_bytes))
              (i32.const 0xFFFF))
            (i32.const 16)))
        (if (i32.eq (memory.grow (local.get $need_pages)) (i32.const -1))
          (then (unreachable)))))
    (i32.store (i32.const 512) (local.get $end))
    (local.get $aligned))

  (func (export "cabi_realloc")
    (param i32) (param i32) (param i32) (param i32) (result i32)
    (call $cabi_realloc
      (local.get 0) (local.get 1) (local.get 2) (local.get 3)))
)
