;; SHA-512 (FIPS PUB 180-4 §6.4) — hand-written WAT, resource-shape world.
;;
;; Implements the canonical-ABI streaming hasher resource defined in
;; `sha512.wit`:
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
;; Memory layout (initial single page, grows on demand):
;;   [    0,  640) — W[0..79] message schedule scratch (80 × 8 B)
;;   [  640, 1280) — K[0..79] round constants (data segment, native-LE)
;;   [ 1280, 2048) — reserved (bump pointer cell at 1536)
;;   [ 2048, 4096) — 8 hasher slots × 256 B each (see below)
;;   [ 4096,65536) — cabi_realloc bump heap (~60 KiB)
;;
;; Hasher slot layout (256 B per slot):
;;   +  0  i32       in_use (0 = free, 1 = active)
;;   +  4  i64×8     H[0..7] (running state, native-endian)
;;   + 68  i32       pending_bytes (count of bytes in pending buffer, 0..128)
;;   + 72  i32×4     total bytes hashed (128-bit, LE words: w0..w3)
;;   + 88  i8×128    pending buffer (incomplete block awaiting more data)
;;   +216 …         padding
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

  (global $K_OFF i32 (i32.const 640))

  ;; K[0..79]: FIPS §4.2.3 round constants (frac(cube_root(prime))).
  ;; Stored native-LE so we can `i64.load` directly.
  (data (i32.const 640)
    "\22\ae\28\d7\98\2f\8a\42\cd\65\ef\23\91\44\37\71"
    "\2f\3b\4d\ec\cf\fb\c0\b5\bc\db\89\81\a5\db\b5\e9"
    "\38\b5\48\f3\5b\c2\56\39\19\d0\05\b6\f1\11\f1\59"
    "\9b\4f\19\af\a4\82\3f\92\18\81\6d\da\d5\5e\1c\ab"
    "\42\02\03\a3\98\aa\07\d8\be\6f\70\45\01\5b\83\12"
    "\8c\b2\e4\4e\be\85\31\24\e2\b4\ff\d5\c3\7d\0c\55"
    "\6f\89\7b\f2\74\5d\be\72\b1\96\16\3b\fe\b1\de\80"
    "\35\12\c7\25\a7\06\dc\9b\94\26\69\cf\74\f1\9b\c1"
    "\d2\4a\f1\9e\c1\69\9b\e4\e3\25\4f\38\86\47\be\ef"
    "\b5\d5\8c\8b\c6\9d\c1\0f\65\9c\ac\77\cc\a1\0c\24"
    "\75\02\2b\59\6f\2c\e9\2d\83\e4\a6\6e\aa\84\74\4a"
    "\d4\fb\41\bd\dc\a9\b0\5c\b5\53\11\83\da\88\f9\76"
    "\ab\df\66\ee\52\51\3e\98\10\32\b4\2d\6d\c6\31\a8"
    "\3f\21\fb\98\c8\27\03\b0\e4\0e\ef\be\c7\7f\59\bf"
    "\c2\8f\a8\3d\f3\0b\e0\c6\25\a7\0a\93\47\91\a7\d5"
    "\6f\82\03\e0\51\63\ca\06\70\6e\0e\0a\67\29\29\14"
    "\fc\2f\d2\46\85\0a\b7\27\26\c9\26\5c\38\21\1b\2e"
    "\ed\2a\c4\5a\fc\6d\2c\4d\df\b3\95\9d\13\0d\38\53"
    "\de\63\af\8b\54\73\0a\65\a8\b2\77\3c\bb\0a\6a\76"
    "\e6\ae\ed\47\2e\c9\c2\81\3b\35\82\14\85\2c\72\92"
    "\64\03\f1\4c\a1\e8\bf\a2\01\30\42\bc\4b\66\1a\a8"
    "\91\97\f8\d0\70\8b\4b\c2\30\be\54\06\a3\51\6c\c7"
    "\18\52\ef\d6\19\e8\92\d1\10\a9\65\55\24\06\99\d6"
    "\2a\20\71\57\85\35\0e\f4\b8\d1\bb\32\70\a0\6a\10"
    "\c8\d0\d2\b8\16\c1\a4\19\53\ab\41\51\08\6c\37\1e"
    "\99\eb\8e\df\4c\77\48\27\a8\48\9b\e1\b5\bc\b0\34"
    "\63\5a\c9\c5\b3\0c\1c\39\cb\8a\41\e3\4a\aa\d8\4e"
    "\73\e3\63\77\4f\ca\9c\5b\a3\b8\b2\d6\f3\6f\2e\68"
    "\fc\b2\ef\5d\ee\82\8f\74\60\2f\17\43\6f\63\a5\78"
    "\72\ab\f0\a1\14\78\c8\84\ec\39\64\1a\08\02\c7\8c"
    "\28\1e\63\23\fa\ff\be\90\e9\bd\82\de\eb\6c\50\a4"
    "\15\79\c6\b2\f7\a3\f9\be\2b\53\72\e3\f2\78\71\c6"
    "\9c\61\26\ea\ce\3e\27\ca\07\c2\c0\21\c7\b8\86\d1"
    "\1e\eb\e0\cd\d6\7d\da\ea\78\d1\6e\ee\7f\4f\7d\f5"
    "\ba\6f\17\72\aa\67\f0\06\a6\98\c8\a2\c5\7d\63\0a"
    "\ae\0d\f9\be\04\98\3f\11\1b\47\1c\13\35\0b\71\1b"
    "\84\7d\04\23\f5\77\db\28\93\24\c7\40\7b\ab\ca\32"
    "\bc\be\c9\15\0a\be\9e\3c\4c\0d\10\9c\c4\67\1d\43"
    "\b6\42\3e\cb\be\d4\c5\4c\2a\7e\65\fc\9c\29\7f\59"
    "\ec\fa\d6\3a\ab\6f\cb\5f\17\58\47\4a\8c\19\44\6c"
  )

  ;; ─── Helpers ─────────────────────────────────────────────────────────

  (func $load_be64 (param $ptr i32) (result i64)
    (i64.or
      (i64.or
        (i64.or
          (i64.shl (i64.load8_u (local.get $ptr)) (i64.const 56))
          (i64.shl (i64.load8_u (i32.add (local.get $ptr) (i32.const 1))) (i64.const 48)))
        (i64.or
          (i64.shl (i64.load8_u (i32.add (local.get $ptr) (i32.const 2))) (i64.const 40))
          (i64.shl (i64.load8_u (i32.add (local.get $ptr) (i32.const 3))) (i64.const 32))))
      (i64.or
        (i64.or
          (i64.shl (i64.load8_u (i32.add (local.get $ptr) (i32.const 4))) (i64.const 24))
          (i64.shl (i64.load8_u (i32.add (local.get $ptr) (i32.const 5))) (i64.const 16)))
        (i64.or
          (i64.shl (i64.load8_u (i32.add (local.get $ptr) (i32.const 6))) (i64.const 8))
          (i64.load8_u (i32.add (local.get $ptr) (i32.const 7)))))))

  (func $store_be64 (param $ptr i32) (param $v i64)
    (i32.store8 (local.get $ptr)
      (i32.wrap_i64 (i64.shr_u (local.get $v) (i64.const 56))))
    (i32.store8 (i32.add (local.get $ptr) (i32.const 1))
      (i32.wrap_i64 (i64.shr_u (local.get $v) (i64.const 48))))
    (i32.store8 (i32.add (local.get $ptr) (i32.const 2))
      (i32.wrap_i64 (i64.shr_u (local.get $v) (i64.const 40))))
    (i32.store8 (i32.add (local.get $ptr) (i32.const 3))
      (i32.wrap_i64 (i64.shr_u (local.get $v) (i64.const 32))))
    (i32.store8 (i32.add (local.get $ptr) (i32.const 4))
      (i32.wrap_i64 (i64.shr_u (local.get $v) (i64.const 24))))
    (i32.store8 (i32.add (local.get $ptr) (i32.const 5))
      (i32.wrap_i64 (i64.shr_u (local.get $v) (i64.const 16))))
    (i32.store8 (i32.add (local.get $ptr) (i32.const 6))
      (i32.wrap_i64 (i64.shr_u (local.get $v) (i64.const 8))))
    (i32.store8 (i32.add (local.get $ptr) (i32.const 7))
      (i32.wrap_i64 (local.get $v))))

  ;; ─── Core compress (FIPS §6.4.2) ─────────────────────────────────────
  ;;
  ;; state_ptr: 8 native-endian i64 words of running state.
  ;; block_ptr: 128 bytes of input block (BE byte stream).
  ;; out_ptr:   64-byte output (new state, native-endian).
  ;; W[] scratch lives at offset 0; we re-use it for every block.
  (func $compress_block
    (param $state_ptr i32) (param $block_ptr i32) (param $out_ptr i32)
    (local $t i32)
    (local $a i64) (local $b i64) (local $c i64) (local $d i64)
    (local $e i64) (local $f i64) (local $g i64) (local $h i64)
    (local $h0 i64) (local $h1 i64) (local $h2 i64) (local $h3 i64)
    (local $h4 i64) (local $h5 i64) (local $h6 i64) (local $h7 i64)
    (local $w_t i64) (local $s0 i64) (local $s1 i64)
    (local $t1 i64) (local $t2 i64)
    (local $ch i64) (local $maj i64)
    (local $bigS0 i64) (local $bigS1 i64)
    (local $x i64)

    (local.set $h0 (i64.load (local.get $state_ptr)))
    (local.set $h1 (i64.load (i32.add (local.get $state_ptr) (i32.const 8))))
    (local.set $h2 (i64.load (i32.add (local.get $state_ptr) (i32.const 16))))
    (local.set $h3 (i64.load (i32.add (local.get $state_ptr) (i32.const 24))))
    (local.set $h4 (i64.load (i32.add (local.get $state_ptr) (i32.const 32))))
    (local.set $h5 (i64.load (i32.add (local.get $state_ptr) (i32.const 40))))
    (local.set $h6 (i64.load (i32.add (local.get $state_ptr) (i32.const 48))))
    (local.set $h7 (i64.load (i32.add (local.get $state_ptr) (i32.const 56))))

    ;; W[0..15] from block (FIPS §6.4.2 step 1).
    (local.set $t (i32.const 0))
    (block $break_init
      (loop $loop_init
        (br_if $break_init (i32.ge_s (local.get $t) (i32.const 16)))
        (i64.store
          (i32.shl (local.get $t) (i32.const 3))
          (call $load_be64
            (i32.add (local.get $block_ptr) (i32.shl (local.get $t) (i32.const 3)))))
        (local.set $t (i32.add (local.get $t) (i32.const 1)))
        (br $loop_init)))

    ;; W[16..79] = σ₁(W[t-2]) + W[t-7] + σ₀(W[t-15]) + W[t-16].
    (local.set $t (i32.const 16))
    (block $break_ext
      (loop $loop_ext
        (br_if $break_ext (i32.ge_s (local.get $t) (i32.const 80)))
        (local.set $x (i64.load
          (i32.shl (i32.sub (local.get $t) (i32.const 2)) (i32.const 3))))
        (local.set $s1
          (i64.xor
            (i64.xor
              (i64.rotr (local.get $x) (i64.const 19))
              (i64.rotr (local.get $x) (i64.const 61)))
            (i64.shr_u (local.get $x) (i64.const 6))))
        (local.set $x (i64.load
          (i32.shl (i32.sub (local.get $t) (i32.const 15)) (i32.const 3))))
        (local.set $s0
          (i64.xor
            (i64.xor
              (i64.rotr (local.get $x) (i64.const 1))
              (i64.rotr (local.get $x) (i64.const 8)))
            (i64.shr_u (local.get $x) (i64.const 7))))
        (local.set $w_t
          (i64.add
            (i64.add (local.get $s1)
              (i64.load (i32.shl (i32.sub (local.get $t) (i32.const 7)) (i32.const 3))))
            (i64.add (local.get $s0)
              (i64.load (i32.shl (i32.sub (local.get $t) (i32.const 16)) (i32.const 3))))))
        (i64.store
          (i32.shl (local.get $t) (i32.const 3))
          (local.get $w_t))
        (local.set $t (i32.add (local.get $t) (i32.const 1)))
        (br $loop_ext)))

    ;; Working vars (FIPS §6.4.2 step 2).
    (local.set $a (local.get $h0))
    (local.set $b (local.get $h1))
    (local.set $c (local.get $h2))
    (local.set $d (local.get $h3))
    (local.set $e (local.get $h4))
    (local.set $f (local.get $h5))
    (local.set $g (local.get $h6))
    (local.set $h (local.get $h7))

    ;; 80-round main loop (FIPS §6.4.2 step 3).
    (local.set $t (i32.const 0))
    (block $break_main
      (loop $loop_main
        (br_if $break_main (i32.ge_s (local.get $t) (i32.const 80)))

        ;; Σ₁(e) = ROTR14 ^ ROTR18 ^ ROTR41
        (local.set $bigS1
          (i64.xor
            (i64.xor
              (i64.rotr (local.get $e) (i64.const 14))
              (i64.rotr (local.get $e) (i64.const 18)))
            (i64.rotr (local.get $e) (i64.const 41))))

        ;; Ch(e,f,g) = (e & f) ^ (~e & g)
        (local.set $ch
          (i64.xor
            (i64.and (local.get $e) (local.get $f))
            (i64.and (i64.xor (local.get $e) (i64.const -1)) (local.get $g))))

        ;; T1 = h + Σ₁(e) + Ch + K[t] + W[t]
        (local.set $t1
          (i64.add
            (i64.add (local.get $h) (local.get $bigS1))
            (i64.add
              (i64.add (local.get $ch)
                (i64.load
                  (i32.add (global.get $K_OFF) (i32.shl (local.get $t) (i32.const 3)))))
              (i64.load (i32.shl (local.get $t) (i32.const 3))))))

        ;; Σ₀(a) = ROTR28 ^ ROTR34 ^ ROTR39
        (local.set $bigS0
          (i64.xor
            (i64.xor
              (i64.rotr (local.get $a) (i64.const 28))
              (i64.rotr (local.get $a) (i64.const 34)))
            (i64.rotr (local.get $a) (i64.const 39))))

        ;; Maj(a,b,c) = (a & b) ^ (a & c) ^ (b & c)
        (local.set $maj
          (i64.xor
            (i64.xor
              (i64.and (local.get $a) (local.get $b))
              (i64.and (local.get $a) (local.get $c)))
            (i64.and (local.get $b) (local.get $c))))

        ;; T2 = Σ₀(a) + Maj
        (local.set $t2 (i64.add (local.get $bigS0) (local.get $maj)))

        (local.set $h (local.get $g))
        (local.set $g (local.get $f))
        (local.set $f (local.get $e))
        (local.set $e (i64.add (local.get $d) (local.get $t1)))
        (local.set $d (local.get $c))
        (local.set $c (local.get $b))
        (local.set $b (local.get $a))
        (local.set $a (i64.add (local.get $t1) (local.get $t2)))

        (local.set $t (i32.add (local.get $t) (i32.const 1)))
        (br $loop_main)))

    ;; H += working vars (FIPS §6.4.2 step 4).
    (local.set $h0 (i64.add (local.get $h0) (local.get $a)))
    (local.set $h1 (i64.add (local.get $h1) (local.get $b)))
    (local.set $h2 (i64.add (local.get $h2) (local.get $c)))
    (local.set $h3 (i64.add (local.get $h3) (local.get $d)))
    (local.set $h4 (i64.add (local.get $h4) (local.get $e)))
    (local.set $h5 (i64.add (local.get $h5) (local.get $f)))
    (local.set $h6 (i64.add (local.get $h6) (local.get $g)))
    (local.set $h7 (i64.add (local.get $h7) (local.get $h)))

    (i64.store (local.get $out_ptr)                              (local.get $h0))
    (i64.store (i32.add (local.get $out_ptr) (i32.const 8))      (local.get $h1))
    (i64.store (i32.add (local.get $out_ptr) (i32.const 16))     (local.get $h2))
    (i64.store (i32.add (local.get $out_ptr) (i32.const 24))     (local.get $h3))
    (i64.store (i32.add (local.get $out_ptr) (i32.const 32))     (local.get $h4))
    (i64.store (i32.add (local.get $out_ptr) (i32.const 40))     (local.get $h5))
    (i64.store (i32.add (local.get $out_ptr) (i32.const 48))     (local.get $h6))
    (i64.store (i32.add (local.get $out_ptr) (i32.const 56))     (local.get $h7)))

  ;; ─── Slot management ─────────────────────────────────────────────────

  ;; Slot 0 base = 2048. Slot stride = 256.
  (func $slot_base (param $handle i32) (result i32)
    (i32.add (i32.const 2048) (i32.shl (local.get $handle) (i32.const 8))))

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
            ;; FIPS §5.3.5 initial H.
            (i64.store (i32.add (local.get $base) (i32.const 4))  (i64.const 0x6a09e667f3bcc908))
            (i64.store (i32.add (local.get $base) (i32.const 12)) (i64.const 0xbb67ae8584caa73b))
            (i64.store (i32.add (local.get $base) (i32.const 20)) (i64.const 0x3c6ef372fe94f82b))
            (i64.store (i32.add (local.get $base) (i32.const 28)) (i64.const 0xa54ff53a5f1d36f1))
            (i64.store (i32.add (local.get $base) (i32.const 36)) (i64.const 0x510e527fade682d1))
            (i64.store (i32.add (local.get $base) (i32.const 44)) (i64.const 0x9b05688c2b3e6c1f))
            (i64.store (i32.add (local.get $base) (i32.const 52)) (i64.const 0x1f83d9abfb41bd6b))
            (i64.store (i32.add (local.get $base) (i32.const 60)) (i64.const 0x5be0cd19137e2179))
            ;; pending_bytes = 0
            (i32.store (i32.add (local.get $base) (i32.const 68)) (i32.const 0))
            ;; total[0..3] = 0
            (i32.store (i32.add (local.get $base) (i32.const 72)) (i32.const 0))
            (i32.store (i32.add (local.get $base) (i32.const 76)) (i32.const 0))
            (i32.store (i32.add (local.get $base) (i32.const 80)) (i32.const 0))
            (i32.store (i32.add (local.get $base) (i32.const 84)) (i32.const 0))
            (return (local.get $i))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $loop)))
    (unreachable))

  (func $state_ptr (param $handle i32) (result i32)
    (i32.add (call $slot_base (local.get $handle)) (i32.const 4)))

  (func $pending_ptr (param $handle i32) (result i32)
    (i32.add (call $slot_base (local.get $handle)) (i32.const 88)))

  (func $slot_compress (param $handle i32) (param $block_ptr i32)
    (local $sp i32)
    (local.set $sp (call $state_ptr (local.get $handle)))
    (call $compress_block (local.get $sp) (local.get $block_ptr) (local.get $sp)))

  (func $slot_add_total (param $handle i32) (param $n i32)
    (local $base i32)
    (local $w0 i32) (local $w1 i32) (local $w2 i32) (local $w3 i32)
    (local $nw0 i32) (local $nw1 i32) (local $nw2 i32) (local $nw3 i32)
    (local $c i32)
    (local.set $base (i32.add (call $slot_base (local.get $handle)) (i32.const 72)))
    (local.set $w0 (i32.load (local.get $base)))
    (local.set $w1 (i32.load (i32.add (local.get $base) (i32.const 4))))
    (local.set $w2 (i32.load (i32.add (local.get $base) (i32.const 8))))
    (local.set $w3 (i32.load (i32.add (local.get $base) (i32.const 12))))

    (local.set $nw0 (i32.add (local.get $w0) (local.get $n)))
    (local.set $c (i32.lt_u (local.get $nw0) (local.get $w0)))
    (local.set $nw1 (i32.add (local.get $w1) (local.get $c)))
    (local.set $c (i32.lt_u (local.get $nw1) (local.get $w1)))
    (local.set $nw2 (i32.add (local.get $w2) (local.get $c)))
    (local.set $c (i32.lt_u (local.get $nw2) (local.get $w2)))
    (local.set $nw3 (i32.add (local.get $w3) (local.get $c)))

    (i32.store (local.get $base) (local.get $nw0))
    (i32.store (i32.add (local.get $base) (i32.const 4)) (local.get $nw1))
    (i32.store (i32.add (local.get $base) (i32.const 8)) (local.get $nw2))
    (i32.store (i32.add (local.get $base) (i32.const 12)) (local.get $nw3)))

  ;; ─── Public: compress ────────────────────────────────────────────────
  (func (export "covalence:hash/api@0.1.0#compress")
    (param $state_ptr i32) (param $state_len i32)
    (param $block_ptr i32) (param $block_len i32)
    (result i32)
    (local $out i32)
    (local $ret i32)
    (local $native_state i32)
    (local $native_out i32)
    (local $i i32)
    (if (i32.ne (local.get $state_len) (i32.const 64)) (then (unreachable)))
    (if (i32.ne (local.get $block_len) (i32.const 128)) (then (unreachable)))
    (local.set $native_state (call $cabi_realloc
      (i32.const 0) (i32.const 0) (i32.const 8) (i32.const 64)))
    (local.set $i (i32.const 0))
    (block $break
      (loop $loop
        (br_if $break (i32.ge_s (local.get $i) (i32.const 8)))
        (i64.store
          (i32.add (local.get $native_state) (i32.shl (local.get $i) (i32.const 3)))
          (call $load_be64
            (i32.add (local.get $state_ptr) (i32.shl (local.get $i) (i32.const 3)))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $loop)))
    (local.set $native_out (call $cabi_realloc
      (i32.const 0) (i32.const 0) (i32.const 8) (i32.const 64)))
    (call $compress_block
      (local.get $native_state) (local.get $block_ptr) (local.get $native_out))
    (local.set $out (call $cabi_realloc
      (i32.const 0) (i32.const 0) (i32.const 1) (i32.const 64)))
    (local.set $i (i32.const 0))
    (block $break
      (loop $loop
        (br_if $break (i32.ge_s (local.get $i) (i32.const 8)))
        (call $store_be64
          (i32.add (local.get $out) (i32.shl (local.get $i) (i32.const 3)))
          (i64.load
            (i32.add (local.get $native_out) (i32.shl (local.get $i) (i32.const 3)))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $loop)))
    (local.set $ret (call $cabi_realloc
      (i32.const 0) (i32.const 0) (i32.const 4) (i32.const 8)))
    (i32.store (local.get $ret) (local.get $out))
    (i32.store (i32.add (local.get $ret) (i32.const 4)) (i32.const 64))
    (local.get $ret))

  ;; ─── Resource: hasher constructor ────────────────────────────────────
  (func $new_hasher_impl (result i32)
    (call $alloc_slot))
  (func (export "covalence:hash/api@0.1.0#[constructor]hasher") (result i32)
    (call $resource_new_hasher (call $new_hasher_impl)))

  ;; ─── Resource: hasher.update ─────────────────────────────────────────
  (func $update_impl
    (param $handle i32) (param $data_ptr i32) (param $data_len i32)
    (local $base i32) (local $pending i32) (local $i i32) (local $needed i32)
    (local $pbuf i32)
    (local.set $base (call $slot_base (local.get $handle)))
    (local.set $pbuf (call $pending_ptr (local.get $handle)))
    (local.set $pending (i32.load (i32.add (local.get $base) (i32.const 68))))

    (call $slot_add_total (local.get $handle) (local.get $data_len))

    (if (i32.gt_s (local.get $pending) (i32.const 0))
      (then
        (local.set $needed (i32.sub (i32.const 128) (local.get $pending)))
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
              (i32.add (local.get $base) (i32.const 68))
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
            (i32.store (i32.add (local.get $base) (i32.const 68)) (i32.const 0))))))

    (block $break
      (loop $loop
        (br_if $break (i32.lt_u (local.get $data_len) (i32.const 128)))
        (call $slot_compress (local.get $handle) (local.get $data_ptr))
        (local.set $data_ptr (i32.add (local.get $data_ptr) (i32.const 128)))
        (local.set $data_len (i32.sub (local.get $data_len) (i32.const 128)))
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
        (i32.store (i32.add (local.get $base) (i32.const 68)) (local.get $data_len)))))
  (func (export "covalence:hash/api@0.1.0#[method]hasher.update")
    (param $handle i32) (param $data_ptr i32) (param $data_len i32)
    (call $update_impl
      (local.get $handle) (local.get $data_ptr) (local.get $data_len)))

  ;; ─── Resource: hasher.finalize ───────────────────────────────────────
  (func $finalize_impl (param $handle i32) (result i32)
    (local $base i32) (local $pbuf i32) (local $pending i32)
    (local $w0 i32) (local $w1 i32) (local $w2 i32) (local $w3 i32)
    (local $b0 i32) (local $b1 i32) (local $b2 i32) (local $b3 i32)
    (local $i i32)
    (local $out i32) (local $ret i32)

    (local.set $base (call $slot_base (local.get $handle)))
    (local.set $pbuf (call $pending_ptr (local.get $handle)))
    (local.set $pending (i32.load (i32.add (local.get $base) (i32.const 68))))
    (local.set $w0 (i32.load (i32.add (local.get $base) (i32.const 72))))
    (local.set $w1 (i32.load (i32.add (local.get $base) (i32.const 76))))
    (local.set $w2 (i32.load (i32.add (local.get $base) (i32.const 80))))
    (local.set $w3 (i32.load (i32.add (local.get $base) (i32.const 84))))

    (local.set $b0 (i32.shl (local.get $w0) (i32.const 3)))
    (local.set $b1 (i32.or
      (i32.shl (local.get $w1) (i32.const 3))
      (i32.shr_u (local.get $w0) (i32.const 29))))
    (local.set $b2 (i32.or
      (i32.shl (local.get $w2) (i32.const 3))
      (i32.shr_u (local.get $w1) (i32.const 29))))
    (local.set $b3 (i32.or
      (i32.shl (local.get $w3) (i32.const 3))
      (i32.shr_u (local.get $w2) (i32.const 29))))

    (i32.store8 (i32.add (local.get $pbuf) (local.get $pending)) (i32.const 0x80))
    (local.set $pending (i32.add (local.get $pending) (i32.const 1)))

    (if (i32.gt_s (local.get $pending) (i32.const 112))
      (then
        (local.set $i (local.get $pending))
        (block $break
          (loop $loop
            (br_if $break (i32.ge_s (local.get $i) (i32.const 128)))
            (i32.store8 (i32.add (local.get $pbuf) (local.get $i)) (i32.const 0))
            (local.set $i (i32.add (local.get $i) (i32.const 1)))
            (br $loop)))
        (call $slot_compress (local.get $handle) (local.get $pbuf))
        (local.set $pending (i32.const 0))))

    (local.set $i (local.get $pending))
    (block $break
      (loop $loop
        (br_if $break (i32.ge_s (local.get $i) (i32.const 112)))
        (i32.store8 (i32.add (local.get $pbuf) (local.get $i)) (i32.const 0))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $loop)))

    ;; Write 128-bit BE length: bytes [112..128).
    (i32.store8 (i32.add (local.get $pbuf) (i32.const 112))
      (i32.shr_u (local.get $b3) (i32.const 24)))
    (i32.store8 (i32.add (local.get $pbuf) (i32.const 113))
      (i32.shr_u (local.get $b3) (i32.const 16)))
    (i32.store8 (i32.add (local.get $pbuf) (i32.const 114))
      (i32.shr_u (local.get $b3) (i32.const 8)))
    (i32.store8 (i32.add (local.get $pbuf) (i32.const 115))
      (local.get $b3))
    (i32.store8 (i32.add (local.get $pbuf) (i32.const 116))
      (i32.shr_u (local.get $b2) (i32.const 24)))
    (i32.store8 (i32.add (local.get $pbuf) (i32.const 117))
      (i32.shr_u (local.get $b2) (i32.const 16)))
    (i32.store8 (i32.add (local.get $pbuf) (i32.const 118))
      (i32.shr_u (local.get $b2) (i32.const 8)))
    (i32.store8 (i32.add (local.get $pbuf) (i32.const 119))
      (local.get $b2))
    (i32.store8 (i32.add (local.get $pbuf) (i32.const 120))
      (i32.shr_u (local.get $b1) (i32.const 24)))
    (i32.store8 (i32.add (local.get $pbuf) (i32.const 121))
      (i32.shr_u (local.get $b1) (i32.const 16)))
    (i32.store8 (i32.add (local.get $pbuf) (i32.const 122))
      (i32.shr_u (local.get $b1) (i32.const 8)))
    (i32.store8 (i32.add (local.get $pbuf) (i32.const 123))
      (local.get $b1))
    (i32.store8 (i32.add (local.get $pbuf) (i32.const 124))
      (i32.shr_u (local.get $b0) (i32.const 24)))
    (i32.store8 (i32.add (local.get $pbuf) (i32.const 125))
      (i32.shr_u (local.get $b0) (i32.const 16)))
    (i32.store8 (i32.add (local.get $pbuf) (i32.const 126))
      (i32.shr_u (local.get $b0) (i32.const 8)))
    (i32.store8 (i32.add (local.get $pbuf) (i32.const 127))
      (local.get $b0))

    (call $slot_compress (local.get $handle) (local.get $pbuf))

    (local.set $out (call $cabi_realloc
      (i32.const 0) (i32.const 0) (i32.const 1) (i32.const 64)))
    (local.set $i (i32.const 0))
    (block $break
      (loop $loop
        (br_if $break (i32.ge_s (local.get $i) (i32.const 8)))
        (call $store_be64
          (i32.add (local.get $out) (i32.shl (local.get $i) (i32.const 3)))
          (i64.load
            (i32.add (call $state_ptr (local.get $handle))
                     (i32.shl (local.get $i) (i32.const 3)))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $loop)))

    ;; finalize consumes the resource — free the slot.
    (i32.store (local.get $base) (i32.const 0))

    (local.set $ret (call $cabi_realloc
      (i32.const 0) (i32.const 0) (i32.const 4) (i32.const 8)))
    (i32.store (local.get $ret) (local.get $out))
    (i32.store (i32.add (local.get $ret) (i32.const 4)) (i32.const 64))
    (local.get $ret))
  (func (export "covalence:hash/api@0.1.0#[method]hasher.finalize") (param $handle i32) (result i32)
    (call $finalize_impl (local.get $handle)))

  ;; ─── cabi_realloc — bump allocator + memory growth ───────────────────
  ;;
  ;; Bump pointer at offset 1536 (scratch within reserved region).
  ;; If the new allocation would run past the end of linear memory we
  ;; grow it in 64 KiB pages until it fits, trapping on grow failure.
  (func $cabi_realloc
    (param $orig_ptr i32) (param $orig_size i32)
    (param $align i32) (param $new_size i32)
    (result i32)
    (local $bump i32) (local $mask i32) (local $aligned i32)
    (local $end i32) (local $cur_bytes i32) (local $need_pages i32)
    (if (i32.ne (local.get $orig_ptr) (i32.const 0)) (then (unreachable)))
    (local.set $bump (i32.load (i32.const 1536)))
    (if (i32.eqz (local.get $bump))
      (then (local.set $bump (i32.const 4096))))
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
    (i32.store (i32.const 1536) (local.get $end))
    (local.get $aligned))

  (func (export "cabi_realloc")
    (param i32) (param i32) (param i32) (param i32) (result i32)
    (call $cabi_realloc
      (local.get 0) (local.get 1) (local.get 2) (local.get 3)))
)
