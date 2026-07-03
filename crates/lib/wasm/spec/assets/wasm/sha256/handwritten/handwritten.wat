;; SHA-256 (FIPS PUB 180-4 §6.2) — hand-written WAT, resource-shape world.
;;
;; Implements the canonical-ABI streaming hasher resource defined in
;; `sha256.wit`:
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
;; Memory layout (single page, 64 KiB; cabi_realloc grows as needed):
;;   [    0,  256) — W[0..63] message schedule scratch (256 B)
;;   [  256,  512) — K[0..63] round constants, native-endian (256 B; FIPS §4.2.2)
;;   [  512,  516) — cabi_realloc bump pointer
;;   [ 1024, 2048) — 8 hasher slots × 128 B each (see below)
;;   [ 2048,65536) — cabi_realloc bump heap (~62 KiB), grows on demand
;;
;; Hasher slot layout (128 B per slot):
;;   +  0  i32   in_use (0 = free, 1 = active)
;;   +  4  i32×8  H[0..8] (running state, native-endian; FIPS §5.3.3 IV)
;;   + 36  i32   pending_bytes (count of bytes in pending buffer, 0..64)
;;   + 40  i32   total_len_lo (low 32 bits of total bytes hashed)
;;   + 44  i32   total_len_hi (high 32 bits of total bytes hashed)
;;   + 48  i8×64 pending buffer (incomplete block awaiting more data)
;;   +112..128   reserved
;;
;; The 8-slot cap is a v0 limitation — overflow traps. The stateful
;; variant (`handwritten-stateful`) demonstrates the alternative single-
;; instance-per-hasher model with no handle table at all.

(module
  ;; Canonical-ABI intrinsics for the exported `hasher` resource.
  ;; `[resource-new]hasher` takes a rep (i32) and returns a handle (i32).
  (import "[export]covalence:hash/api@0.1.0" "[resource-new]hasher"
    (func $resource_new_hasher (param i32) (result i32)))

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

  ;; ─── Bitwise mixing functions (FIPS §4.1.2) ──────────────────────────
  ;;
  ;; SHA-256 uses ROTR (right-rotate); wasm has `i32.rotr`. All shifts /
  ;; rotates are on 32-bit words.

  ;; Ch(x,y,z) = (x AND y) XOR ((NOT x) AND z)
  (func $ch (param $x i32) (param $y i32) (param $z i32) (result i32)
    (i32.xor
      (i32.and (local.get $x) (local.get $y))
      (i32.and (i32.xor (local.get $x) (i32.const -1)) (local.get $z))))

  ;; Maj(x,y,z) = (x AND y) XOR (x AND z) XOR (y AND z)
  (func $maj (param $x i32) (param $y i32) (param $z i32) (result i32)
    (i32.xor
      (i32.xor
        (i32.and (local.get $x) (local.get $y))
        (i32.and (local.get $x) (local.get $z)))
      (i32.and (local.get $y) (local.get $z))))

  ;; Σ₀(x) = ROTR(x,2) ⊕ ROTR(x,13) ⊕ ROTR(x,22)
  (func $big_sigma0 (param $x i32) (result i32)
    (i32.xor
      (i32.xor
        (i32.rotr (local.get $x) (i32.const 2))
        (i32.rotr (local.get $x) (i32.const 13)))
      (i32.rotr (local.get $x) (i32.const 22))))

  ;; Σ₁(x) = ROTR(x,6) ⊕ ROTR(x,11) ⊕ ROTR(x,25)
  (func $big_sigma1 (param $x i32) (result i32)
    (i32.xor
      (i32.xor
        (i32.rotr (local.get $x) (i32.const 6))
        (i32.rotr (local.get $x) (i32.const 11)))
      (i32.rotr (local.get $x) (i32.const 25))))

  ;; σ₀(x) = ROTR(x,7) ⊕ ROTR(x,18) ⊕ SHR(x,3)
  (func $small_sigma0 (param $x i32) (result i32)
    (i32.xor
      (i32.xor
        (i32.rotr (local.get $x) (i32.const 7))
        (i32.rotr (local.get $x) (i32.const 18)))
      (i32.shr_u (local.get $x) (i32.const 3))))

  ;; σ₁(x) = ROTR(x,17) ⊕ ROTR(x,19) ⊕ SHR(x,10)
  (func $small_sigma1 (param $x i32) (result i32)
    (i32.xor
      (i32.xor
        (i32.rotr (local.get $x) (i32.const 17))
        (i32.rotr (local.get $x) (i32.const 19)))
      (i32.shr_u (local.get $x) (i32.const 10))))

  ;; ─── Core compress (FIPS §6.2.2) ─────────────────────────────────────
  ;;
  ;; state_ptr: 8 native-endian i32 words of running state.
  ;; block_ptr: 64 bytes of input block (BE byte stream).
  ;; out_ptr:   32-byte output (new state, native-endian).
  ;; W[] scratch lives at offset 0; we re-use it for every block.
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

    ;; W[0..15] from block (FIPS §6.2.2 step 1).
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

    ;; Working vars (FIPS §6.2.2 step 2).
    (local.set $a (local.get $h0))
    (local.set $b (local.get $h1))
    (local.set $c (local.get $h2))
    (local.set $d (local.get $h3))
    (local.set $e (local.get $h4))
    (local.set $f (local.get $h5))
    (local.set $g (local.get $h6))
    (local.set $h (local.get $h7))

    ;; 64-round main loop (FIPS §6.2.2 step 3).
    ;; T₁ = h + Σ₁(e) + Ch(e,f,g) + K[t] + W[t]
    ;; T₂ = Σ₀(a) + Maj(a,b,c)
    ;; h=g; g=f; f=e; e=d+T₁; d=c; c=b; b=a; a=T₁+T₂
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
              ;; K[t] from constant table at offset 256.
              (i32.load (i32.add (i32.const 256) (i32.shl (local.get $t) (i32.const 2))))
              ;; W[t] from scratch at offset 0.
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

    ;; H += working vars (FIPS §6.2.2 step 4).
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
            ;; FIPS §5.3.3 initial H.
            (i32.store (i32.add (local.get $base) (i32.const 4))  (i32.const 0x6A09E667))
            (i32.store (i32.add (local.get $base) (i32.const 8))  (i32.const 0xBB67AE85))
            (i32.store (i32.add (local.get $base) (i32.const 12)) (i32.const 0x3C6EF372))
            (i32.store (i32.add (local.get $base) (i32.const 16)) (i32.const 0xA54FF53A))
            (i32.store (i32.add (local.get $base) (i32.const 20)) (i32.const 0x510E527F))
            (i32.store (i32.add (local.get $base) (i32.const 24)) (i32.const 0x9B05688C))
            (i32.store (i32.add (local.get $base) (i32.const 28)) (i32.const 0x1F83D9AB))
            (i32.store (i32.add (local.get $base) (i32.const 32)) (i32.const 0x5BE0CD19))
            (i32.store (i32.add (local.get $base) (i32.const 36)) (i32.const 0))
            (i32.store (i32.add (local.get $base) (i32.const 40)) (i32.const 0))
            (i32.store (i32.add (local.get $base) (i32.const 44)) (i32.const 0))
            (return (local.get $i))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $loop)))
    (unreachable))

  (func $state_ptr (param $handle i32) (result i32)
    (i32.add (call $slot_base (local.get $handle)) (i32.const 4)))

  (func $pending_ptr (param $handle i32) (result i32)
    (i32.add (call $slot_base (local.get $handle)) (i32.const 48)))

  (func $slot_compress (param $handle i32) (param $block_ptr i32)
    (local $sp i32)
    (local.set $sp (call $state_ptr (local.get $handle)))
    (call $compress_block (local.get $sp) (local.get $block_ptr) (local.get $sp)))

  (func $slot_add_total (param $handle i32) (param $n i32)
    (local $base i32)
    (local $lo i32)
    (local $new_lo i32)
    (local.set $base (call $slot_base (local.get $handle)))
    (local.set $lo (i32.load (i32.add (local.get $base) (i32.const 40))))
    (local.set $new_lo (i32.add (local.get $lo) (local.get $n)))
    (i32.store (i32.add (local.get $base) (i32.const 40)) (local.get $new_lo))
    (if (i32.lt_u (local.get $new_lo) (local.get $lo))
      (then
        (i32.store
          (i32.add (local.get $base) (i32.const 44))
          (i32.add
            (i32.load (i32.add (local.get $base) (i32.const 44)))
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
    (local.set $pending (i32.load (i32.add (local.get $base) (i32.const 36))))

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
              (i32.add (local.get $base) (i32.const 36))
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
            (i32.store (i32.add (local.get $base) (i32.const 36)) (i32.const 0))))))

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
        (i32.store (i32.add (local.get $base) (i32.const 36)) (local.get $data_len)))))
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
    (local.set $pending (i32.load (i32.add (local.get $base) (i32.const 36))))
    (local.set $lo (i32.load (i32.add (local.get $base) (i32.const 40))))
    (local.set $hi (i32.load (i32.add (local.get $base) (i32.const 44))))

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
      (i32.const 0) (i32.const 0) (i32.const 1) (i32.const 32)))
    (local.set $i (i32.const 0))
    (block $break
      (loop $loop
        (br_if $break (i32.ge_s (local.get $i) (i32.const 8)))
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
    (i32.store (i32.add (local.get $ret) (i32.const 4)) (i32.const 32))
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
