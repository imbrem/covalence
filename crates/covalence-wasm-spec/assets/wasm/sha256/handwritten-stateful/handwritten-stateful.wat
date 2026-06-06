;; SHA-256 (FIPS PUB 180-4 §6.2) — hand-written WAT, single-instance world.
;;
;; Implements `sha256-stateful.wit`: `init` / `update` / `finalize` /
;; `compress`. The composed one-shot `hash` is added by
;; `compose_one_shot` during rebuild.
;;
;; Single global state — no handle table, no per-hasher allocation.
;; An embedder gets N concurrent hashers by instantiating N copies of
;; the component; that's the entire "object model" — the module
;; instance IS the hasher object.
;;
;; Memory layout (single page, 64 KiB):
;;   [    0,  256) — W[0..63] message schedule scratch (256 B)
;;   [  256,  512) — K[0..63] round constants, native-endian (256 B; FIPS §4.2.2)
;;   [  512,  516) — cabi_realloc bump pointer
;;   [  640,  672) — H[0..8] running state, native-endian (32 B)
;;   [  672,  676) — pending_bytes (i32)
;;   [  676,  680) — total_lo (i32)
;;   [  680,  684) — total_hi (i32)
;;   [  684,  748) — pending buffer (64 B)
;;   [  748, 1024) — reserved / padding
;;   [ 1024,65536) — cabi_realloc bump heap (~63 KiB), grows on demand

(module
  (memory (export "memory") 1)

  ;; K[0..63] round constants from FIPS §4.2.2, stored native-endian
  ;; (little-endian on wasm) so we can load each with a plain `i32.load`.
  (data (i32.const 256)
    "\98\2f\8a\42\91\44\37\71\cf\fb\c0\b5\a5\db\b5\e9"
    "\5b\c2\56\39\f1\11\f1\59\a4\82\3f\92\d5\5e\1c\ab"
    "\98\aa\07\d8\01\5b\83\12\be\85\31\24\c3\7d\0c\55"
    "\74\5d\be\72\fe\b1\de\80\a7\06\dc\9b\74\f1\9b\c1"
    "\c1\69\9b\e4\86\47\be\ef\c6\9d\c1\0f\cc\a1\0c\24"
    "\6f\2c\e9\2d\aa\84\74\4a\dc\a9\b0\5c\da\88\f9\76"
    "\52\51\3e\98\6d\c6\31\a8\c8\27\03\b0\c7\7f\59\bf"
    "\f3\0b\e0\c6\47\91\a7\d5\51\63\ca\06\67\29\29\14"
    "\85\0a\b7\27\38\21\1b\2e\fc\6d\2c\4d\13\0d\38\53"
    "\54\73\0a\65\bb\0a\6a\76\2e\c9\c2\81\85\2c\72\92"
    "\a1\e8\bf\a2\4b\66\1a\a8\70\8b\4b\c2\a3\51\6c\c7"
    "\19\e8\92\d1\24\06\99\d6\85\35\0e\f4\70\a0\6a\10"
    "\16\c1\a4\19\08\6c\37\1e\4c\77\48\27\b5\bc\b0\34"
    "\b3\0c\1c\39\4a\aa\d8\4e\4f\ca\9c\5b\f3\6f\2e\68"
    "\ee\82\8f\74\6f\63\a5\78\14\78\c8\84\08\02\c7\8c"
    "\fa\ff\be\90\eb\6c\50\a4\f7\a3\f9\be\f2\78\71\c6")

  ;; State offsets
  (global $H_OFF i32 (i32.const 640))
  (global $PENDING_OFF i32 (i32.const 672))
  (global $TOTAL_LO_OFF i32 (i32.const 676))
  (global $TOTAL_HI_OFF i32 (i32.const 680))
  (global $PBUF_OFF i32 (i32.const 684))

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

  ;; ─── Bitwise mixing functions (FIPS §4.1.2) ──────────────────────────

  (func $ch (param $x i32) (param $y i32) (param $z i32) (result i32)
    (i32.xor
      (i32.and (local.get $x) (local.get $y))
      (i32.and (i32.xor (local.get $x) (i32.const -1)) (local.get $z))))

  (func $maj (param $x i32) (param $y i32) (param $z i32) (result i32)
    (i32.xor
      (i32.xor
        (i32.and (local.get $x) (local.get $y))
        (i32.and (local.get $x) (local.get $z)))
      (i32.and (local.get $y) (local.get $z))))

  (func $big_sigma0 (param $x i32) (result i32)
    (i32.xor
      (i32.xor
        (i32.rotr (local.get $x) (i32.const 2))
        (i32.rotr (local.get $x) (i32.const 13)))
      (i32.rotr (local.get $x) (i32.const 22))))

  (func $big_sigma1 (param $x i32) (result i32)
    (i32.xor
      (i32.xor
        (i32.rotr (local.get $x) (i32.const 6))
        (i32.rotr (local.get $x) (i32.const 11)))
      (i32.rotr (local.get $x) (i32.const 25))))

  (func $small_sigma0 (param $x i32) (result i32)
    (i32.xor
      (i32.xor
        (i32.rotr (local.get $x) (i32.const 7))
        (i32.rotr (local.get $x) (i32.const 18)))
      (i32.shr_u (local.get $x) (i32.const 3))))

  (func $small_sigma1 (param $x i32) (result i32)
    (i32.xor
      (i32.xor
        (i32.rotr (local.get $x) (i32.const 17))
        (i32.rotr (local.get $x) (i32.const 19)))
      (i32.shr_u (local.get $x) (i32.const 10))))

  ;; ─── Core compress (FIPS §6.2.2) ─────────────────────────────────────
  (func $compress_block
    (param $state_ptr i32) (param $block_ptr i32) (param $out_ptr i32)
    (local $t i32)
    (local $a i32) (local $b i32) (local $c i32) (local $d i32)
    (local $e i32) (local $f i32) (local $g i32) (local $h i32)
    (local $h0 i32) (local $h1 i32) (local $h2 i32) (local $h3 i32)
    (local $h4 i32) (local $h5 i32) (local $h6 i32) (local $h7 i32)
    (local $w_t i32) (local $t1 i32) (local $t2 i32)

    (local.set $h0 (i32.load (local.get $state_ptr)))
    (local.set $h1 (i32.load (i32.add (local.get $state_ptr) (i32.const 4))))
    (local.set $h2 (i32.load (i32.add (local.get $state_ptr) (i32.const 8))))
    (local.set $h3 (i32.load (i32.add (local.get $state_ptr) (i32.const 12))))
    (local.set $h4 (i32.load (i32.add (local.get $state_ptr) (i32.const 16))))
    (local.set $h5 (i32.load (i32.add (local.get $state_ptr) (i32.const 20))))
    (local.set $h6 (i32.load (i32.add (local.get $state_ptr) (i32.const 24))))
    (local.set $h7 (i32.load (i32.add (local.get $state_ptr) (i32.const 28))))

    ;; W[0..15] from block.
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

    ;; W[16..63] = σ₁(W[t-2]) + W[t-7] + σ₀(W[t-15]) + W[t-16].
    (local.set $t (i32.const 16))
    (block $break_ext
      (loop $loop_ext
        (br_if $break_ext (i32.ge_s (local.get $t) (i32.const 64)))
        (local.set $w_t
          (i32.add
            (i32.add
              (call $small_sigma1
                (i32.load (i32.shl (i32.sub (local.get $t) (i32.const 2)) (i32.const 2))))
              (i32.load (i32.shl (i32.sub (local.get $t) (i32.const 7)) (i32.const 2))))
            (i32.add
              (call $small_sigma0
                (i32.load (i32.shl (i32.sub (local.get $t) (i32.const 15)) (i32.const 2))))
              (i32.load (i32.shl (i32.sub (local.get $t) (i32.const 16)) (i32.const 2))))))
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
    (local.set $f (local.get $h5))
    (local.set $g (local.get $h6))
    (local.set $h (local.get $h7))

    ;; 64-round main loop (FIPS §6.2.2 step 3).
    (local.set $t (i32.const 0))
    (block $break_main
      (loop $loop_main
        (br_if $break_main (i32.ge_s (local.get $t) (i32.const 64)))
        (local.set $t1
          (i32.add
            (i32.add
              (i32.add (local.get $h) (call $big_sigma1 (local.get $e)))
              (call $ch (local.get $e) (local.get $f) (local.get $g)))
            (i32.add
              (i32.load (i32.add (i32.const 256) (i32.shl (local.get $t) (i32.const 2))))
              (i32.load (i32.shl (local.get $t) (i32.const 2))))))
        (local.set $t2
          (i32.add
            (call $big_sigma0 (local.get $a))
            (call $maj (local.get $a) (local.get $b) (local.get $c))))

        (local.set $h (local.get $g))
        (local.set $g (local.get $f))
        (local.set $f (local.get $e))
        (local.set $e (i32.add (local.get $d) (local.get $t1)))
        (local.set $d (local.get $c))
        (local.set $c (local.get $b))
        (local.set $b (local.get $a))
        (local.set $a (i32.add (local.get $t1) (local.get $t2)))

        (local.set $t (i32.add (local.get $t) (i32.const 1)))
        (br $loop_main)))

    (local.set $h0 (i32.add (local.get $h0) (local.get $a)))
    (local.set $h1 (i32.add (local.get $h1) (local.get $b)))
    (local.set $h2 (i32.add (local.get $h2) (local.get $c)))
    (local.set $h3 (i32.add (local.get $h3) (local.get $d)))
    (local.set $h4 (i32.add (local.get $h4) (local.get $e)))
    (local.set $h5 (i32.add (local.get $h5) (local.get $f)))
    (local.set $h6 (i32.add (local.get $h6) (local.get $g)))
    (local.set $h7 (i32.add (local.get $h7) (local.get $h)))

    (i32.store (local.get $out_ptr) (local.get $h0))
    (i32.store (i32.add (local.get $out_ptr) (i32.const 4))  (local.get $h1))
    (i32.store (i32.add (local.get $out_ptr) (i32.const 8))  (local.get $h2))
    (i32.store (i32.add (local.get $out_ptr) (i32.const 12)) (local.get $h3))
    (i32.store (i32.add (local.get $out_ptr) (i32.const 16)) (local.get $h4))
    (i32.store (i32.add (local.get $out_ptr) (i32.const 20)) (local.get $h5))
    (i32.store (i32.add (local.get $out_ptr) (i32.const 24)) (local.get $h6))
    (i32.store (i32.add (local.get $out_ptr) (i32.const 28)) (local.get $h7)))

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
    (if (i32.ne (local.get $state_len) (i32.const 32)) (then (unreachable)))
    (if (i32.ne (local.get $block_len) (i32.const 64)) (then (unreachable)))
    (local.set $native_state (call $cabi_realloc
      (i32.const 0) (i32.const 0) (i32.const 4) (i32.const 32)))
    (local.set $i (i32.const 0))
    (block $break
      (loop $loop
        (br_if $break (i32.ge_s (local.get $i) (i32.const 8)))
        (i32.store
          (i32.add (local.get $native_state) (i32.shl (local.get $i) (i32.const 2)))
          (call $load_be32
            (i32.add (local.get $state_ptr) (i32.shl (local.get $i) (i32.const 2)))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $loop)))
    (local.set $native_out (call $cabi_realloc
      (i32.const 0) (i32.const 0) (i32.const 4) (i32.const 32)))
    (call $compress_block
      (local.get $native_state) (local.get $block_ptr) (local.get $native_out))
    (local.set $out (call $cabi_realloc
      (i32.const 0) (i32.const 0) (i32.const 1) (i32.const 32)))
    (local.set $i (i32.const 0))
    (block $break
      (loop $loop
        (br_if $break (i32.ge_s (local.get $i) (i32.const 8)))
        (call $store_be32
          (i32.add (local.get $out) (i32.shl (local.get $i) (i32.const 2)))
          (i32.load
            (i32.add (local.get $native_out) (i32.shl (local.get $i) (i32.const 2)))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $loop)))
    (local.set $ret (call $cabi_realloc
      (i32.const 0) (i32.const 0) (i32.const 4) (i32.const 8)))
    (i32.store (local.get $ret) (local.get $out))
    (i32.store (i32.add (local.get $ret) (i32.const 4)) (i32.const 32))
    (local.get $ret))

  ;; ─── Public: init ────────────────────────────────────────────────────
  ;;
  ;; Reset the global hasher state to the SHA-256 IV (FIPS §5.3.3).
  (func $init_impl
    ;; H = IV
    (i32.store (global.get $H_OFF)                              (i32.const 0x6A09E667))
    (i32.store (i32.add (global.get $H_OFF) (i32.const 4))      (i32.const 0xBB67AE85))
    (i32.store (i32.add (global.get $H_OFF) (i32.const 8))      (i32.const 0x3C6EF372))
    (i32.store (i32.add (global.get $H_OFF) (i32.const 12))     (i32.const 0xA54FF53A))
    (i32.store (i32.add (global.get $H_OFF) (i32.const 16))     (i32.const 0x510E527F))
    (i32.store (i32.add (global.get $H_OFF) (i32.const 20))     (i32.const 0x9B05688C))
    (i32.store (i32.add (global.get $H_OFF) (i32.const 24))     (i32.const 0x1F83D9AB))
    (i32.store (i32.add (global.get $H_OFF) (i32.const 28))     (i32.const 0x5BE0CD19))
    ;; pending = 0, total = 0
    (i32.store (global.get $PENDING_OFF)  (i32.const 0))
    (i32.store (global.get $TOTAL_LO_OFF) (i32.const 0))
    (i32.store (global.get $TOTAL_HI_OFF) (i32.const 0))
    ;; reset bump allocator so streaming-then-finalize doesn't leak.
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
  ;; length so the padded length is a multiple of 64. Emit 32-byte digest.
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
      (i32.const 0) (i32.const 0) (i32.const 1) (i32.const 32)))
    (local.set $i (i32.const 0))
    (block $break
      (loop $loop
        (br_if $break (i32.ge_s (local.get $i) (i32.const 8)))
        (call $store_be32
          (i32.add (local.get $out) (i32.shl (local.get $i) (i32.const 2)))
          (i32.load
            (i32.add (global.get $H_OFF) (i32.shl (local.get $i) (i32.const 2)))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $loop)))

    (local.set $ret (call $cabi_realloc
      (i32.const 0) (i32.const 0) (i32.const 4) (i32.const 8)))
    (i32.store (local.get $ret) (local.get $out))
    (i32.store (i32.add (local.get $ret) (i32.const 4)) (i32.const 32))
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
