;; SHA-1 (FIPS PUB 180-4 §6.1) — hand-written WAT, single-instance world.
;;
;; Implements `sha1-stateful.wit`: `init` / `update` / `finalize` /
;; `compress`. The composed one-shot `hash` is added by
;; `compose_one_shot` during rebuild.
;;
;; Single global state — no handle table, no per-hasher allocation.
;; An embedder gets N concurrent hashers by instantiating N copies of
;; the component; that's the entire "object model" — the module
;; instance IS the hasher object.
;;
;; Memory layout (single page, 64 KiB):
;;   [   0,  320) — W[0..79] message schedule scratch (320 B)
;;   [ 320,  340) — H[0..5] running state, native-endian (20 B)
;;   [ 340,  344) — pending_bytes (i32)
;;   [ 344,  348) — total_lo (i32)
;;   [ 348,  352) — total_hi (i32)
;;   [ 352,  416) — pending buffer (64 B)
;;   [ 416,  512) — reserved / padding
;;   [ 512,  516) — cabi_realloc bump pointer
;;   [1024,65536) — cabi_realloc bump heap (~63 KiB)

(module
  (memory (export "memory") 1)

  ;; State offsets
  (global $H_OFF i32 (i32.const 320))
  (global $PENDING_OFF i32 (i32.const 340))
  (global $TOTAL_LO_OFF i32 (i32.const 344))
  (global $TOTAL_HI_OFF i32 (i32.const 348))
  (global $PBUF_OFF i32 (i32.const 352))

  ;; ─── Helpers ─────────────────────────────────────────────────────────

  (func $load_be32 (param $ptr i32) (result i32)
    (i32.or
      (i32.or
        (i32.shl (i32.load8_u (local.get $ptr)) (i32.const 24))
        (i32.shl (i32.load8_u (i32.add (local.get $ptr) (i32.const 1))) (i32.const 16)))
      (i32.or
        (i32.shl (i32.load8_u (i32.add (local.get $ptr) (i32.const 2))) (i32.const 8))
        (i32.load8_u (i32.add (local.get $ptr) (i32.const 3))))))

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

    (local.set $a (local.get $h0))
    (local.set $b (local.get $h1))
    (local.set $c (local.get $h2))
    (local.set $d (local.get $h3))
    (local.set $e (local.get $h4))

    (local.set $t (i32.const 0))
    (block $break_main
      (loop $loop_main
        (br_if $break_main (i32.ge_s (local.get $t) (i32.const 80)))

        (if (i32.lt_s (local.get $t) (i32.const 20))
          (then
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

  ;; Compress the global state against `block_ptr`, updating it in place.
  (func $compress_global (param $block_ptr i32)
    (call $compress_block (global.get $H_OFF) (local.get $block_ptr) (global.get $H_OFF)))

  (func $add_total (param $n i32)
    (local $lo i32)
    (local $new_lo i32)
    (local.set $lo (i32.load (global.get $TOTAL_LO_OFF)))
    (local.set $new_lo (i32.add (local.get $lo) (local.get $n)))
    (i32.store (global.get $TOTAL_LO_OFF) (local.get $new_lo))
    (if (i32.lt_u (local.get $new_lo) (local.get $lo))
      (then
        (i32.store
          (global.get $TOTAL_HI_OFF)
          (i32.add
            (i32.load (global.get $TOTAL_HI_OFF))
            (i32.const 1))))))

  ;; ─── Public: compress (block primitive) ──────────────────────────────
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

  ;; ─── Public: init ────────────────────────────────────────────────────
  ;;
  ;; Reset the global hasher state to the SHA-1 IV (FIPS §5.3.1).
  (func $init_impl
    ;; H = IV
    (i32.store (global.get $H_OFF)                              (i32.const 0x67452301))
    (i32.store (i32.add (global.get $H_OFF) (i32.const 4))      (i32.const 0xEFCDAB89))
    (i32.store (i32.add (global.get $H_OFF) (i32.const 8))      (i32.const 0x98BADCFE))
    (i32.store (i32.add (global.get $H_OFF) (i32.const 12))     (i32.const 0x10325476))
    (i32.store (i32.add (global.get $H_OFF) (i32.const 16))     (i32.const 0xC3D2E1F0))
    ;; pending = 0, total = 0
    (i32.store (global.get $PENDING_OFF)  (i32.const 0))
    (i32.store (global.get $TOTAL_LO_OFF) (i32.const 0))
    (i32.store (global.get $TOTAL_HI_OFF) (i32.const 0))
    ;; reset bump allocator so streaming-then-finalize doesn't leak.
    ;; compress's output buffer is freed implicitly by reusing the
    ;; scratch area each call.
    (i32.store (i32.const 512) (i32.const 0)))
  (func (export "covalence:hash/api@0.1.0#init")
    (call $init_impl))

  ;; ─── Public: update ──────────────────────────────────────────────────
  (func $update_impl
    (param $data_ptr i32) (param $data_len i32)
    (local $pending i32) (local $i i32) (local $needed i32)
    (local $pbuf i32)
    (local.set $pbuf (global.get $PBUF_OFF))
    (local.set $pending (i32.load (global.get $PENDING_OFF)))

    (call $add_total (local.get $data_len))

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
              (global.get $PENDING_OFF)
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
            (call $compress_global (local.get $pbuf))
            (local.set $data_ptr (i32.add (local.get $data_ptr) (local.get $needed)))
            (local.set $data_len (i32.sub (local.get $data_len) (local.get $needed)))
            (i32.store (global.get $PENDING_OFF) (i32.const 0))))))

    (block $break
      (loop $loop
        (br_if $break (i32.lt_u (local.get $data_len) (i32.const 64)))
        (call $compress_global (local.get $data_ptr))
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
        (i32.store (global.get $PENDING_OFF) (local.get $data_len)))))
  (func (export "covalence:hash/api@0.1.0#update")
    (param $data_ptr i32) (param $data_len i32)
    (call $update_impl (local.get $data_ptr) (local.get $data_len)))

  ;; ─── Public: finalize ────────────────────────────────────────────────
  ;;
  ;; FIPS §5.1.1 padding: append 0x80, zero-pad, then 8-byte BE total bit
  ;; length so the padded length is a multiple of 64. Emit 20-byte digest.
  (func $finalize_impl (result i32)
    (local $pbuf i32) (local $pending i32)
    (local $lo i32) (local $hi i32)
    (local $bit_lo i32) (local $bit_hi i32)
    (local $i i32)
    (local $out i32) (local $ret i32)

    (local.set $pbuf (global.get $PBUF_OFF))
    (local.set $pending (i32.load (global.get $PENDING_OFF)))
    (local.set $lo (i32.load (global.get $TOTAL_LO_OFF)))
    (local.set $hi (i32.load (global.get $TOTAL_HI_OFF)))

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
        (call $compress_global (local.get $pbuf))
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

    (call $compress_global (local.get $pbuf))

    (local.set $out (call $cabi_realloc
      (i32.const 0) (i32.const 0) (i32.const 1) (i32.const 20)))
    (local.set $i (i32.const 0))
    (block $break
      (loop $loop
        (br_if $break (i32.ge_s (local.get $i) (i32.const 5)))
        (call $store_be32
          (i32.add (local.get $out) (i32.shl (local.get $i) (i32.const 2)))
          (i32.load
            (i32.add (global.get $H_OFF) (i32.shl (local.get $i) (i32.const 2)))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $loop)))

    (local.set $ret (call $cabi_realloc
      (i32.const 0) (i32.const 0) (i32.const 4) (i32.const 8)))
    (i32.store (local.get $ret) (local.get $out))
    (i32.store (i32.add (local.get $ret) (i32.const 4)) (i32.const 20))
    (local.get $ret))
  (func (export "covalence:hash/api@0.1.0#finalize") (result i32)
    (call $finalize_impl))

  ;; ─── cabi_realloc — bump allocator + memory growth ───────────────────
  ;;
  ;; Bump pointer at offset 512; reset to 1024 by `init` so each hash
  ;; session starts with a clean heap. We `memory.grow` lazily when
  ;; needed; resize / free aren't supported.
  (func $cabi_realloc
    (param $orig_ptr i32) (param $orig_size i32)
    (param $align i32) (param $new_size i32)
    (result i32)
    (local $bump i32) (local $mask i32) (local $aligned i32)
    (local $end i32) (local $cur_bytes i32) (local $need_pages i32)
    (if (i32.ne (local.get $orig_ptr) (i32.const 0)) (then (unreachable)))
    (local.set $bump (i32.load (i32.const 512)))
    (if (i32.eqz (local.get $bump))
      (then (local.set $bump (i32.const 1024))))
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
