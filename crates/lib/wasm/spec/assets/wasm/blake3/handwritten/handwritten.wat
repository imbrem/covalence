;; BLAKE3 ("BLAKE3: one function, fast everywhere", 2020, §2) —
;; hand-written WAT, resource-shape world.
;;
;; Implements `blake3.wit`:
;;   resource hasher { constructor; update; finalize }   (plain mode)
;;   keyed-hash / derive-key  (one-shots)
;;   compress                  (block primitive: t=0, b=64, d=0)
;; The composed one-shot `hash` is added by `compose_one_shot` during
;; rebuild as `[constructor]hasher → update → finalize`.
;;
;; Memory layout (single page initial = 64 KiB; cabi_realloc grows it):
;;   [    0,   64) — compress state[16] words (full 16-word state buffer)
;;   [   64,  128) — message buffer m[16] words (LE-decoded block)
;;   [  128,  192) — permutation scratch (next message buffer)
;;   [  192,  224) — temp CV scratch (truncate8 output)
;;   [  224,  256) — derive-key context-key scratch
;;   [  256,  320) — parent block buffer (64 B, used for stack merges)
;;   [  320,  512) — reserved scratch
;;   [  512,  516) — cabi_realloc bump pointer
;;   [  516, 4096) — reserved
;;   [ 4096,12288) — 4 resource slots × 2048 B (slots 0..3)
;;   [12288,14336) — transient slot for one-shot keyed-hash/derive-key
;;   [14336,65536) — cabi_realloc bump heap
;;
;; Per-slot layout (2048 B, slot stride 2048):
;;   +   0  i32      in_use         (0 = free, 1 = active)
;;   +   4  i32×8    key_words      (initial CV per chunk, native i32)
;;   +  36  i32×8    chunk_cv       (running CV within current chunk)
;;   +  68  byte×64  chunk_block    (partial block buffer)
;;   + 132  i32      chunk_block_len
;;   + 136  i32      chunk_blocks_compressed
;;   + 140  i32      chunk_counter_lo
;;   + 144  i32      chunk_counter_hi
;;   + 148  i32      flags          (mode flags)
;;   + 152  i32      cv_stack_len
;;   + 156  i32×8×54 cv_stack       (subtree chaining values, 1728 B)
;;
;; All hot-path helpers read state through the mutable global $CUR_STATE
;; — set once at the start of each entry point — so the per-slot offsets
;; can be encoded as constant displacements from the base.
;;
;; Resource ABI (Legacy mangling, sync):
;;   `[constructor]hasher  : () -> i32`    (returns the rep — slot index)
;;   `[method]hasher.update: (i32 ptr i32 len i32)`  → no result
;;   `[method]hasher.finalize: (i32) -> i32`         → ret-area ptr
;; We do NOT export a destructor — `finalize` consumes the resource in
;; band. Resources dropped without finalize leak their slot until the
;; module instance is gone (acceptable for a reference implementation).

(module
  (import "[export]covalence:hash/api@0.1.0" "[resource-new]hasher"
    (func $resource_new_hasher (param i32) (result i32)))

  (memory (export "memory") 1)

  ;; ─── Scratch offsets (same as stateful variant) ──────────────────────
  (global $STATE_OFF i32 (i32.const 0))
  (global $MSG_OFF i32 (i32.const 64))
  (global $PMSG_OFF i32 (i32.const 128))
  (global $TCV_OFF i32 (i32.const 192))
  (global $DK_CTX_OFF i32 (i32.const 224))
  (global $PB_OFF i32 (i32.const 256))
  (global $BUMP_PTR i32 (i32.const 512))

  ;; ─── Slot pool ───────────────────────────────────────────────────────
  (global $SLOT_BASE i32 (i32.const 4096))
  (global $SLOT_STRIDE i32 (i32.const 2048))
  (global $SLOT_COUNT i32 (i32.const 4))
  (global $TRANSIENT_BASE i32 (i32.const 12288))
  (global $BUMP_HEAP_START i32 (i32.const 14336))

  ;; ─── Per-slot field offsets (relative to slot base) ──────────────────
  (global $F_IN_USE i32 (i32.const 0))
  (global $F_KEY i32 (i32.const 4))
  (global $F_CHUNK_CV i32 (i32.const 36))
  (global $F_CHUNK_BLOCK i32 (i32.const 68))
  (global $F_BLOCK_LEN i32 (i32.const 132))
  (global $F_BLOCKS_COMPR i32 (i32.const 136))
  (global $F_CTR_LO i32 (i32.const 140))
  (global $F_CTR_HI i32 (i32.const 144))
  (global $F_FLAGS i32 (i32.const 148))
  (global $F_STACK_LEN i32 (i32.const 152))
  (global $F_STACK i32 (i32.const 156))

  ;; ─── Current operating state base ────────────────────────────────────
  ;;
  ;; Mutated by every entry point. Each entry point points it at the
  ;; slot (or transient buffer) it operates on, then calls inner helpers
  ;; that read fields as (global.get $CUR_STATE) + F_X.
  (global $CUR_STATE (mut i32) (i32.const 0))

  ;; ─── LE byte ↔ i32 word helpers ──────────────────────────────────────
  (func $load_le32 (param $ptr i32) (result i32)
    (i32.or
      (i32.or
        (i32.load8_u (local.get $ptr))
        (i32.shl (i32.load8_u (i32.add (local.get $ptr) (i32.const 1))) (i32.const 8)))
      (i32.or
        (i32.shl (i32.load8_u (i32.add (local.get $ptr) (i32.const 2))) (i32.const 16))
        (i32.shl (i32.load8_u (i32.add (local.get $ptr) (i32.const 3))) (i32.const 24)))))

  (func $store_le32 (param $ptr i32) (param $v i32)
    (i32.store8 (local.get $ptr) (local.get $v))
    (i32.store8 (i32.add (local.get $ptr) (i32.const 1))
      (i32.shr_u (local.get $v) (i32.const 8)))
    (i32.store8 (i32.add (local.get $ptr) (i32.const 2))
      (i32.shr_u (local.get $v) (i32.const 16)))
    (i32.store8 (i32.add (local.get $ptr) (i32.const 3))
      (i32.shr_u (local.get $v) (i32.const 24))))

  ;; ─── G mixing function (spec §2.4) ───────────────────────────────────
  (func $g (param $a i32) (param $b i32) (param $c i32) (param $d i32)
           (param $mx i32) (param $my i32)
    (local $pa i32) (local $pb i32) (local $pc i32) (local $pd i32)
    (local $va i32) (local $vb i32) (local $vc i32) (local $vd i32)
    (local.set $pa (i32.add (global.get $STATE_OFF) (i32.shl (local.get $a) (i32.const 2))))
    (local.set $pb (i32.add (global.get $STATE_OFF) (i32.shl (local.get $b) (i32.const 2))))
    (local.set $pc (i32.add (global.get $STATE_OFF) (i32.shl (local.get $c) (i32.const 2))))
    (local.set $pd (i32.add (global.get $STATE_OFF) (i32.shl (local.get $d) (i32.const 2))))
    (local.set $va (i32.load (local.get $pa)))
    (local.set $vb (i32.load (local.get $pb)))
    (local.set $vc (i32.load (local.get $pc)))
    (local.set $vd (i32.load (local.get $pd)))
    (local.set $va (i32.add (i32.add (local.get $va) (local.get $vb)) (local.get $mx)))
    (local.set $vd (i32.rotr (i32.xor (local.get $vd) (local.get $va)) (i32.const 16)))
    (local.set $vc (i32.add (local.get $vc) (local.get $vd)))
    (local.set $vb (i32.rotr (i32.xor (local.get $vb) (local.get $vc)) (i32.const 12)))
    (local.set $va (i32.add (i32.add (local.get $va) (local.get $vb)) (local.get $my)))
    (local.set $vd (i32.rotr (i32.xor (local.get $vd) (local.get $va)) (i32.const 8)))
    (local.set $vc (i32.add (local.get $vc) (local.get $vd)))
    (local.set $vb (i32.rotr (i32.xor (local.get $vb) (local.get $vc)) (i32.const 7)))
    (i32.store (local.get $pa) (local.get $va))
    (i32.store (local.get $pb) (local.get $vb))
    (i32.store (local.get $pc) (local.get $vc))
    (i32.store (local.get $pd) (local.get $vd)))

  ;; ─── One round (column step + diagonal step), spec §2.5 ──────────────
  (func $round (param $m i32)
    (call $g (i32.const 0) (i32.const 4) (i32.const 8) (i32.const 12)
             (i32.load (i32.add (local.get $m) (i32.const 0)))
             (i32.load (i32.add (local.get $m) (i32.const 4))))
    (call $g (i32.const 1) (i32.const 5) (i32.const 9) (i32.const 13)
             (i32.load (i32.add (local.get $m) (i32.const 8)))
             (i32.load (i32.add (local.get $m) (i32.const 12))))
    (call $g (i32.const 2) (i32.const 6) (i32.const 10) (i32.const 14)
             (i32.load (i32.add (local.get $m) (i32.const 16)))
             (i32.load (i32.add (local.get $m) (i32.const 20))))
    (call $g (i32.const 3) (i32.const 7) (i32.const 11) (i32.const 15)
             (i32.load (i32.add (local.get $m) (i32.const 24)))
             (i32.load (i32.add (local.get $m) (i32.const 28))))
    (call $g (i32.const 0) (i32.const 5) (i32.const 10) (i32.const 15)
             (i32.load (i32.add (local.get $m) (i32.const 32)))
             (i32.load (i32.add (local.get $m) (i32.const 36))))
    (call $g (i32.const 1) (i32.const 6) (i32.const 11) (i32.const 12)
             (i32.load (i32.add (local.get $m) (i32.const 40)))
             (i32.load (i32.add (local.get $m) (i32.const 44))))
    (call $g (i32.const 2) (i32.const 7) (i32.const 8) (i32.const 13)
             (i32.load (i32.add (local.get $m) (i32.const 48)))
             (i32.load (i32.add (local.get $m) (i32.const 52))))
    (call $g (i32.const 3) (i32.const 4) (i32.const 9) (i32.const 14)
             (i32.load (i32.add (local.get $m) (i32.const 56)))
             (i32.load (i32.add (local.get $m) (i32.const 60)))))

  ;; ─── Message permutation (spec §2.5) ─────────────────────────────────
  ;; MSG_PERMUTATION = [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8]
  (func $permute (param $src i32) (param $dst i32)
    (i32.store (i32.add (local.get $dst) (i32.const 0))
      (i32.load (i32.add (local.get $src) (i32.const 8))))
    (i32.store (i32.add (local.get $dst) (i32.const 4))
      (i32.load (i32.add (local.get $src) (i32.const 24))))
    (i32.store (i32.add (local.get $dst) (i32.const 8))
      (i32.load (i32.add (local.get $src) (i32.const 12))))
    (i32.store (i32.add (local.get $dst) (i32.const 12))
      (i32.load (i32.add (local.get $src) (i32.const 40))))
    (i32.store (i32.add (local.get $dst) (i32.const 16))
      (i32.load (i32.add (local.get $src) (i32.const 28))))
    (i32.store (i32.add (local.get $dst) (i32.const 20))
      (i32.load (i32.add (local.get $src) (i32.const 0))))
    (i32.store (i32.add (local.get $dst) (i32.const 24))
      (i32.load (i32.add (local.get $src) (i32.const 16))))
    (i32.store (i32.add (local.get $dst) (i32.const 28))
      (i32.load (i32.add (local.get $src) (i32.const 52))))
    (i32.store (i32.add (local.get $dst) (i32.const 32))
      (i32.load (i32.add (local.get $src) (i32.const 4))))
    (i32.store (i32.add (local.get $dst) (i32.const 36))
      (i32.load (i32.add (local.get $src) (i32.const 44))))
    (i32.store (i32.add (local.get $dst) (i32.const 40))
      (i32.load (i32.add (local.get $src) (i32.const 48))))
    (i32.store (i32.add (local.get $dst) (i32.const 44))
      (i32.load (i32.add (local.get $src) (i32.const 20))))
    (i32.store (i32.add (local.get $dst) (i32.const 48))
      (i32.load (i32.add (local.get $src) (i32.const 36))))
    (i32.store (i32.add (local.get $dst) (i32.const 52))
      (i32.load (i32.add (local.get $src) (i32.const 56))))
    (i32.store (i32.add (local.get $dst) (i32.const 56))
      (i32.load (i32.add (local.get $src) (i32.const 60))))
    (i32.store (i32.add (local.get $dst) (i32.const 60))
      (i32.load (i32.add (local.get $src) (i32.const 32)))))

  ;; ─── Compression function (spec §2.3) ────────────────────────────────
  (func $compress
    (param $cv_ptr i32) (param $block_ptr i32)
    (param $t_lo i32) (param $t_hi i32) (param $b i32) (param $d i32)
    (local $i i32) (local $r i32) (local $src i32) (local $dst i32) (local $tmp i32)

    (local.set $i (i32.const 0))
    (block $brk
      (loop $lp
        (br_if $brk (i32.ge_s (local.get $i) (i32.const 8)))
        (i32.store
          (i32.add (global.get $STATE_OFF) (i32.shl (local.get $i) (i32.const 2)))
          (i32.load (i32.add (local.get $cv_ptr) (i32.shl (local.get $i) (i32.const 2)))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $lp)))

    (i32.store
      (i32.add (global.get $STATE_OFF) (i32.const 32)) (i32.const 0x6A09E667))
    (i32.store
      (i32.add (global.get $STATE_OFF) (i32.const 36)) (i32.const 0xBB67AE85))
    (i32.store
      (i32.add (global.get $STATE_OFF) (i32.const 40)) (i32.const 0x3C6EF372))
    (i32.store
      (i32.add (global.get $STATE_OFF) (i32.const 44)) (i32.const 0xA54FF53A))

    (i32.store (i32.add (global.get $STATE_OFF) (i32.const 48)) (local.get $t_lo))
    (i32.store (i32.add (global.get $STATE_OFF) (i32.const 52)) (local.get $t_hi))
    (i32.store (i32.add (global.get $STATE_OFF) (i32.const 56)) (local.get $b))
    (i32.store (i32.add (global.get $STATE_OFF) (i32.const 60)) (local.get $d))

    (local.set $i (i32.const 0))
    (block $brk2
      (loop $lp2
        (br_if $brk2 (i32.ge_s (local.get $i) (i32.const 16)))
        (i32.store
          (i32.add (global.get $MSG_OFF) (i32.shl (local.get $i) (i32.const 2)))
          (call $load_le32
            (i32.add (local.get $block_ptr) (i32.shl (local.get $i) (i32.const 2)))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $lp2)))

    (local.set $src (global.get $MSG_OFF))
    (local.set $dst (global.get $PMSG_OFF))
    (local.set $r (i32.const 0))
    (block $brk3
      (loop $lp3
        (br_if $brk3 (i32.ge_s (local.get $r) (i32.const 6)))
        (call $round (local.get $src))
        (call $permute (local.get $src) (local.get $dst))
        (local.set $tmp (local.get $src))
        (local.set $src (local.get $dst))
        (local.set $dst (local.get $tmp))
        (local.set $r (i32.add (local.get $r) (i32.const 1)))
        (br $lp3)))
    (call $round (local.get $src)))

  (func $truncate8 (param $out_cv_ptr i32)
    (local $i i32)
    (local.set $i (i32.const 0))
    (block $brk
      (loop $lp
        (br_if $brk (i32.ge_s (local.get $i) (i32.const 8)))
        (i32.store
          (i32.add (local.get $out_cv_ptr) (i32.shl (local.get $i) (i32.const 2)))
          (i32.xor
            (i32.load (i32.add (global.get $STATE_OFF)
                               (i32.shl (local.get $i) (i32.const 2))))
            (i32.load (i32.add (global.get $STATE_OFF)
                               (i32.add (i32.const 32)
                                        (i32.shl (local.get $i) (i32.const 2)))))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $lp))))

  ;; ─── Per-slot field accessors (read $CUR_STATE) ──────────────────────
  (func $key_ptr (result i32)
    (i32.add (global.get $CUR_STATE) (global.get $F_KEY)))
  (func $chunk_cv_ptr (result i32)
    (i32.add (global.get $CUR_STATE) (global.get $F_CHUNK_CV)))
  (func $chunk_block_ptr (result i32)
    (i32.add (global.get $CUR_STATE) (global.get $F_CHUNK_BLOCK)))
  (func $block_len (result i32)
    (i32.load (i32.add (global.get $CUR_STATE) (global.get $F_BLOCK_LEN))))
  (func $set_block_len (param $v i32)
    (i32.store (i32.add (global.get $CUR_STATE) (global.get $F_BLOCK_LEN)) (local.get $v)))
  (func $blocks_compr (result i32)
    (i32.load (i32.add (global.get $CUR_STATE) (global.get $F_BLOCKS_COMPR))))
  (func $set_blocks_compr (param $v i32)
    (i32.store (i32.add (global.get $CUR_STATE) (global.get $F_BLOCKS_COMPR)) (local.get $v)))
  (func $ctr_lo (result i32)
    (i32.load (i32.add (global.get $CUR_STATE) (global.get $F_CTR_LO))))
  (func $ctr_hi (result i32)
    (i32.load (i32.add (global.get $CUR_STATE) (global.get $F_CTR_HI))))
  (func $set_ctr_lo (param $v i32)
    (i32.store (i32.add (global.get $CUR_STATE) (global.get $F_CTR_LO)) (local.get $v)))
  (func $set_ctr_hi (param $v i32)
    (i32.store (i32.add (global.get $CUR_STATE) (global.get $F_CTR_HI)) (local.get $v)))
  (func $flags (result i32)
    (i32.load (i32.add (global.get $CUR_STATE) (global.get $F_FLAGS))))
  (func $set_flags (param $v i32)
    (i32.store (i32.add (global.get $CUR_STATE) (global.get $F_FLAGS)) (local.get $v)))
  (func $stack_len (result i32)
    (i32.load (i32.add (global.get $CUR_STATE) (global.get $F_STACK_LEN))))
  (func $set_stack_len (param $v i32)
    (i32.store (i32.add (global.get $CUR_STATE) (global.get $F_STACK_LEN)) (local.get $v)))
  (func $stack_entry_ptr (param $i i32) (result i32)
    (i32.add
      (i32.add (global.get $CUR_STATE) (global.get $F_STACK))
      (i32.shl (local.get $i) (i32.const 5))))

  ;; ─── IV constants ────────────────────────────────────────────────────
  (func $store_iv_at (param $ptr i32)
    (i32.store (local.get $ptr)                         (i32.const 0x6A09E667))
    (i32.store (i32.add (local.get $ptr) (i32.const 4)) (i32.const 0xBB67AE85))
    (i32.store (i32.add (local.get $ptr) (i32.const 8)) (i32.const 0x3C6EF372))
    (i32.store (i32.add (local.get $ptr) (i32.const 12)) (i32.const 0xA54FF53A))
    (i32.store (i32.add (local.get $ptr) (i32.const 16)) (i32.const 0x510E527F))
    (i32.store (i32.add (local.get $ptr) (i32.const 20)) (i32.const 0x9B05688C))
    (i32.store (i32.add (local.get $ptr) (i32.const 24)) (i32.const 0x1F83D9AB))
    (i32.store (i32.add (local.get $ptr) (i32.const 28)) (i32.const 0x5BE0CD19)))

  ;; Reset $CUR_STATE's per-slot fields for a new hashing pass with
  ;; key_words at $src_key_ptr (32 B, 8 native i32 words) and given
  ;; mode flags.
  (func $reset_with (param $src_key_ptr i32) (param $mode_flags i32)
    (local $i i32)
    ;; Copy key_words.
    (local.set $i (i32.const 0))
    (block $brk
      (loop $lp
        (br_if $brk (i32.ge_s (local.get $i) (i32.const 8)))
        (i32.store
          (i32.add (call $key_ptr) (i32.shl (local.get $i) (i32.const 2)))
          (i32.load (i32.add (local.get $src_key_ptr) (i32.shl (local.get $i) (i32.const 2)))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $lp)))
    ;; key_words → chunk_cv.
    (local.set $i (i32.const 0))
    (block $brk2
      (loop $lp2
        (br_if $brk2 (i32.ge_s (local.get $i) (i32.const 8)))
        (i32.store
          (i32.add (call $chunk_cv_ptr) (i32.shl (local.get $i) (i32.const 2)))
          (i32.load (i32.add (call $key_ptr) (i32.shl (local.get $i) (i32.const 2)))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $lp2)))
    ;; Zero chunk_block.
    (local.set $i (i32.const 0))
    (block $brk3
      (loop $lp3
        (br_if $brk3 (i32.ge_s (local.get $i) (i32.const 64)))
        (i32.store8 (i32.add (call $chunk_block_ptr) (local.get $i)) (i32.const 0))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $lp3)))
    (call $set_block_len (i32.const 0))
    (call $set_blocks_compr (i32.const 0))
    (call $set_ctr_lo (i32.const 0))
    (call $set_ctr_hi (i32.const 0))
    (call $set_flags (local.get $mode_flags))
    (call $set_stack_len (i32.const 0)))

  (func $inc_chunk_counter
    (local $lo i32) (local $new_lo i32)
    (local.set $lo (call $ctr_lo))
    (local.set $new_lo (i32.add (local.get $lo) (i32.const 1)))
    (call $set_ctr_lo (local.get $new_lo))
    (if (i32.lt_u (local.get $new_lo) (local.get $lo))
      (then
        (call $set_ctr_hi (i32.add (call $ctr_hi) (i32.const 1))))))

  ;; ─── Chunk CV stack: push & fold equal-height subtrees ───────────────
  (func $add_chunk_cv (param $chunk_cv_ptr i32) (param $total_chunks_after i32)
    (local $tc i32) (local $sl i32) (local $top_ptr i32)
    (local $merged_ptr i32) (local $i i32) (local $mode_flags i32)
    (local.set $tc (local.get $total_chunks_after))
    (local.set $sl (call $stack_len))
    (local.set $mode_flags (call $flags))

    (local.set $merged_ptr (global.get $TCV_OFF))
    (local.set $i (i32.const 0))
    (block $brk_cp
      (loop $lp_cp
        (br_if $brk_cp (i32.ge_s (local.get $i) (i32.const 8)))
        (i32.store
          (i32.add (local.get $merged_ptr) (i32.shl (local.get $i) (i32.const 2)))
          (i32.load (i32.add (local.get $chunk_cv_ptr) (i32.shl (local.get $i) (i32.const 2)))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $lp_cp)))

    (block $brk_merge
      (loop $lp_merge
        (br_if $brk_merge (i32.eq (i32.and (local.get $tc) (i32.const 1)) (i32.const 1)))
        (local.set $sl (i32.sub (local.get $sl) (i32.const 1)))
        (local.set $top_ptr (call $stack_entry_ptr (local.get $sl)))
        (local.set $i (i32.const 0))
        (block $brk_l
          (loop $lp_l
            (br_if $brk_l (i32.ge_s (local.get $i) (i32.const 32)))
            (i32.store8
              (i32.add (global.get $PB_OFF) (local.get $i))
              (i32.load8_u (i32.add (local.get $top_ptr) (local.get $i))))
            (local.set $i (i32.add (local.get $i) (i32.const 1)))
            (br $lp_l)))
        (local.set $i (i32.const 0))
        (block $brk_r
          (loop $lp_r
            (br_if $brk_r (i32.ge_s (local.get $i) (i32.const 32)))
            (i32.store8
              (i32.add (i32.add (global.get $PB_OFF) (i32.const 32)) (local.get $i))
              (i32.load8_u (i32.add (local.get $merged_ptr) (local.get $i))))
            (local.set $i (i32.add (local.get $i) (i32.const 1)))
            (br $lp_r)))
        (call $compress
          (call $key_ptr)
          (global.get $PB_OFF)
          (i32.const 0) (i32.const 0)
          (i32.const 64)
          (i32.or (local.get $mode_flags) (i32.const 4))) ;; PARENT
        (call $truncate8 (local.get $merged_ptr))
        (local.set $tc (i32.shr_u (local.get $tc) (i32.const 1)))
        (br $lp_merge)))

    (local.set $top_ptr (call $stack_entry_ptr (local.get $sl)))
    (local.set $i (i32.const 0))
    (block $brk_push
      (loop $lp_push
        (br_if $brk_push (i32.ge_s (local.get $i) (i32.const 8)))
        (i32.store
          (i32.add (local.get $top_ptr) (i32.shl (local.get $i) (i32.const 2)))
          (i32.load (i32.add (local.get $merged_ptr) (i32.shl (local.get $i) (i32.const 2)))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $lp_push)))
    (call $set_stack_len (i32.add (local.get $sl) (i32.const 1))))

  ;; Compress current FULL block (64 B) and fold into chunk_cv.
  (func $compress_full_block
    (local $start_flag i32) (local $mode_flags i32) (local $blocks i32)
    (local.set $blocks (call $blocks_compr))
    (local.set $start_flag
      (if (result i32) (i32.eqz (local.get $blocks))
        (then (i32.const 1))
        (else (i32.const 0))))
    (local.set $mode_flags (call $flags))
    (call $compress
      (call $chunk_cv_ptr)
      (call $chunk_block_ptr)
      (call $ctr_lo) (call $ctr_hi)
      (i32.const 64)
      (i32.or (local.get $mode_flags) (local.get $start_flag)))
    (call $truncate8 (call $chunk_cv_ptr))
    (call $set_blocks_compr (i32.add (local.get $blocks) (i32.const 1))))

  ;; Finish current chunk (produce CV, push to stack, reset for next chunk).
  (func $finish_chunk
    (local $start_flag i32) (local $mode_flags i32) (local $blocks i32)
    (local $tc_lo i32) (local $i i32) (local $bl i32)
    (local.set $blocks (call $blocks_compr))
    (local.set $start_flag
      (if (result i32) (i32.eqz (local.get $blocks))
        (then (i32.const 1))
        (else (i32.const 0))))
    (local.set $mode_flags (call $flags))
    (local.set $bl (call $block_len))
    (local.set $i (local.get $bl))
    (block $brk_pad
      (loop $lp_pad
        (br_if $brk_pad (i32.ge_s (local.get $i) (i32.const 64)))
        (i32.store8 (i32.add (call $chunk_block_ptr) (local.get $i)) (i32.const 0))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $lp_pad)))
    (call $compress
      (call $chunk_cv_ptr) (call $chunk_block_ptr)
      (call $ctr_lo) (call $ctr_hi)
      (local.get $bl)
      (i32.or (i32.or (local.get $mode_flags) (local.get $start_flag))
              (i32.const 2))) ;; CHUNK_END
    (call $truncate8 (global.get $TCV_OFF))

    (call $inc_chunk_counter)
    (local.set $tc_lo (call $ctr_lo))
    (call $add_chunk_cv (global.get $TCV_OFF) (local.get $tc_lo))

    ;; Reset chunk_cv = key_words.
    (local.set $i (i32.const 0))
    (block $brk_k
      (loop $lp_k
        (br_if $brk_k (i32.ge_s (local.get $i) (i32.const 8)))
        (i32.store
          (i32.add (call $chunk_cv_ptr) (i32.shl (local.get $i) (i32.const 2)))
          (i32.load (i32.add (call $key_ptr) (i32.shl (local.get $i) (i32.const 2)))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $lp_k)))
    (call $set_block_len (i32.const 0))
    (call $set_blocks_compr (i32.const 0))
    (local.set $i (i32.const 0))
    (block $brk_z
      (loop $lp_z
        (br_if $brk_z (i32.ge_s (local.get $i) (i32.const 64)))
        (i32.store8 (i32.add (call $chunk_block_ptr) (local.get $i)) (i32.const 0))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $lp_z))))

  ;; ─── update_impl_inner: assumes $CUR_STATE already set ───────────────
  (func $update_inner (param $data_ptr i32) (param $data_len i32)
    (local $bl i32) (local $room i32) (local $take i32) (local $i i32)
    (block $brk_outer
      (loop $lp_outer
        (br_if $brk_outer (i32.eqz (local.get $data_len)))

        ;; chunk_total_len = blocks_compressed * 64 + block_len.
        (if (i32.eq
              (i32.add
                (i32.shl (call $blocks_compr) (i32.const 6))
                (call $block_len))
              (i32.const 1024))
          (then (call $finish_chunk)))

        (local.set $bl (call $block_len))
        (if (i32.eq (local.get $bl) (i32.const 64))
          (then
            (call $compress_full_block)
            (call $set_block_len (i32.const 0))
            (local.set $bl (i32.const 0))))

        (local.set $room (i32.sub (i32.const 64) (local.get $bl)))
        (local.set $take
          (if (result i32) (i32.lt_u (local.get $data_len) (local.get $room))
            (then (local.get $data_len))
            (else (local.get $room))))
        (local.set $i (i32.const 0))
        (block $brk_cp
          (loop $lp_cp
            (br_if $brk_cp (i32.ge_s (local.get $i) (local.get $take)))
            (i32.store8
              (i32.add (call $chunk_block_ptr) (i32.add (local.get $bl) (local.get $i)))
              (i32.load8_u (i32.add (local.get $data_ptr) (local.get $i))))
            (local.set $i (i32.add (local.get $i) (i32.const 1)))
            (br $lp_cp)))
        (call $set_block_len (i32.add (local.get $bl) (local.get $take)))
        (local.set $data_ptr (i32.add (local.get $data_ptr) (local.get $take)))
        (local.set $data_len (i32.sub (local.get $data_len) (local.get $take)))
        (br $lp_outer))))

  ;; Compute the final 32-byte digest into $TCV_OFF.
  (func $finalize_inner
    (local $start_flag i32) (local $mode_flags i32)
    (local $blocks i32) (local $sl i32)
    (local $cur_cv_ptr i32) (local $cur_block_ptr i32)
    (local $cur_t_lo i32) (local $cur_t_hi i32)
    (local $cur_b i32) (local $cur_d i32)
    (local $i i32) (local $top_ptr i32) (local $merged_cv_ptr i32)
    (local.set $mode_flags (call $flags))
    (local.set $sl (call $stack_len))
    (local.set $blocks (call $blocks_compr))
    (local.set $start_flag
      (if (result i32) (i32.eqz (local.get $blocks))
        (then (i32.const 1))
        (else (i32.const 0))))

    ;; Zero-pad past block_len.
    (local.set $i (call $block_len))
    (block $brk_pad
      (loop $lp_pad
        (br_if $brk_pad (i32.ge_s (local.get $i) (i32.const 64)))
        (i32.store8 (i32.add (call $chunk_block_ptr) (local.get $i)) (i32.const 0))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $lp_pad)))

    (local.set $cur_cv_ptr (call $chunk_cv_ptr))
    (local.set $cur_block_ptr (call $chunk_block_ptr))
    (local.set $cur_t_lo (call $ctr_lo))
    (local.set $cur_t_hi (call $ctr_hi))
    (local.set $cur_b (call $block_len))
    (local.set $cur_d
      (i32.or (i32.or (local.get $mode_flags) (local.get $start_flag))
              (i32.const 2))) ;; CHUNK_END

    (block $brk_walk
      (loop $lp_walk
        (br_if $brk_walk (i32.eqz (local.get $sl)))
        (call $compress
          (local.get $cur_cv_ptr) (local.get $cur_block_ptr)
          (local.get $cur_t_lo) (local.get $cur_t_hi)
          (local.get $cur_b) (local.get $cur_d))
        (local.set $merged_cv_ptr (i32.add (global.get $PB_OFF) (i32.const 32)))
        (call $truncate8 (local.get $merged_cv_ptr))
        (local.set $sl (i32.sub (local.get $sl) (i32.const 1)))
        (local.set $top_ptr (call $stack_entry_ptr (local.get $sl)))
        (local.set $i (i32.const 0))
        (block $brk_l
          (loop $lp_l
            (br_if $brk_l (i32.ge_s (local.get $i) (i32.const 32)))
            (i32.store8
              (i32.add (global.get $PB_OFF) (local.get $i))
              (i32.load8_u (i32.add (local.get $top_ptr) (local.get $i))))
            (local.set $i (i32.add (local.get $i) (i32.const 1)))
            (br $lp_l)))
        (local.set $cur_cv_ptr (call $key_ptr))
        (local.set $cur_block_ptr (global.get $PB_OFF))
        (local.set $cur_t_lo (i32.const 0))
        (local.set $cur_t_hi (i32.const 0))
        (local.set $cur_b (i32.const 64))
        (local.set $cur_d (i32.or (local.get $mode_flags) (i32.const 4))) ;; PARENT
        (br $lp_walk)))

    (call $compress
      (local.get $cur_cv_ptr) (local.get $cur_block_ptr)
      (local.get $cur_t_lo) (local.get $cur_t_hi)
      (local.get $cur_b)
      (i32.or (local.get $cur_d) (i32.const 8))) ;; ROOT
    (call $truncate8 (global.get $TCV_OFF)))

  ;; Emit the 32-byte digest currently in $TCV_OFF as a {ptr, len} ret area.
  (func $emit_digest_ret (result i32)
    (local $out i32) (local $ret i32) (local $i i32)
    (local.set $out (call $cabi_realloc
      (i32.const 0) (i32.const 0) (i32.const 1) (i32.const 32)))
    (local.set $i (i32.const 0))
    (block $brk
      (loop $lp
        (br_if $brk (i32.ge_s (local.get $i) (i32.const 8)))
        (call $store_le32
          (i32.add (local.get $out) (i32.shl (local.get $i) (i32.const 2)))
          (i32.load (i32.add (global.get $TCV_OFF)
                             (i32.shl (local.get $i) (i32.const 2)))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $lp)))
    (local.set $ret (call $cabi_realloc
      (i32.const 0) (i32.const 0) (i32.const 4) (i32.const 8)))
    (i32.store (local.get $ret) (local.get $out))
    (i32.store (i32.add (local.get $ret) (i32.const 4)) (i32.const 32))
    (local.get $ret))

  ;; ─── Slot management ─────────────────────────────────────────────────
  (func $slot_base (param $handle i32) (result i32)
    (i32.add (global.get $SLOT_BASE)
             (i32.mul (local.get $handle) (global.get $SLOT_STRIDE))))

  (func $alloc_slot (result i32)
    (local $i i32) (local $base i32)
    (local.set $i (i32.const 0))
    (block $brk
      (loop $lp
        (br_if $brk (i32.ge_s (local.get $i) (global.get $SLOT_COUNT)))
        (local.set $base (call $slot_base (local.get $i)))
        (if (i32.eqz (i32.load (i32.add (local.get $base) (global.get $F_IN_USE))))
          (then
            (i32.store (i32.add (local.get $base) (global.get $F_IN_USE)) (i32.const 1))
            (return (local.get $i))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $lp)))
    (unreachable))

  ;; ─── Resource: hasher constructor ────────────────────────────────────
  (func $new_hasher_impl (result i32)
    (local $h i32)
    (local.set $h (call $alloc_slot))
    (global.set $CUR_STATE (call $slot_base (local.get $h)))
    (call $store_iv_at (global.get $TCV_OFF))
    (call $reset_with (global.get $TCV_OFF) (i32.const 0))
    (local.get $h))
  (func (export "covalence:hash/api@0.1.0#[constructor]hasher") (result i32)
    (call $resource_new_hasher (call $new_hasher_impl)))

  ;; ─── Resource: hasher.update ─────────────────────────────────────────
  (func $update_impl
    (param $handle i32) (param $data_ptr i32) (param $data_len i32)
    (global.set $CUR_STATE (call $slot_base (local.get $handle)))
    (call $update_inner (local.get $data_ptr) (local.get $data_len)))
  (func (export "covalence:hash/api@0.1.0#[method]hasher.update")
    (param $handle i32) (param $data_ptr i32) (param $data_len i32)
    (call $update_impl (local.get $handle) (local.get $data_ptr) (local.get $data_len)))

  ;; ─── Resource: hasher.finalize ───────────────────────────────────────
  (func $finalize_impl (param $handle i32) (result i32)
    (local $base i32) (local $ret i32)
    (local.set $base (call $slot_base (local.get $handle)))
    (global.set $CUR_STATE (local.get $base))
    (call $finalize_inner)
    (local.set $ret (call $emit_digest_ret))
    ;; Free the slot.
    (i32.store (i32.add (local.get $base) (global.get $F_IN_USE)) (i32.const 0))
    (local.get $ret))
  (func (export "covalence:hash/api@0.1.0#[method]hasher.finalize")
    (param $handle i32) (result i32)
    (call $finalize_impl (local.get $handle)))

  ;; ─── Public: compress (block primitive, t=0 b=64 d=0) ────────────────
  (func (export "covalence:hash/api@0.1.0#compress")
    (param $state_ptr i32) (param $state_len i32)
    (param $block_ptr i32) (param $block_len i32)
    (result i32)
    (local $native_state i32) (local $i i32)
    (if (i32.ne (local.get $state_len) (i32.const 32)) (then (unreachable)))
    (if (i32.ne (local.get $block_len) (i32.const 64)) (then (unreachable)))
    (local.set $native_state (call $cabi_realloc
      (i32.const 0) (i32.const 0) (i32.const 4) (i32.const 32)))
    (local.set $i (i32.const 0))
    (block $brk
      (loop $lp
        (br_if $brk (i32.ge_s (local.get $i) (i32.const 8)))
        (i32.store
          (i32.add (local.get $native_state) (i32.shl (local.get $i) (i32.const 2)))
          (call $load_le32
            (i32.add (local.get $state_ptr) (i32.shl (local.get $i) (i32.const 2)))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $lp)))
    (call $compress
      (local.get $native_state) (local.get $block_ptr)
      (i32.const 0) (i32.const 0) (i32.const 64) (i32.const 0))
    (call $truncate8 (global.get $TCV_OFF))
    (call $emit_digest_ret))

  ;; ─── keyed-hash (one-shot) ───────────────────────────────────────────
  ;;
  ;; Uses the transient slot so the resource handle pool isn't perturbed.
  ;; Resets the transient slot before use.
  (func (export "covalence:hash/api@0.1.0#keyed-hash")
    (param $key_ptr i32) (param $key_len i32)
    (param $data_ptr i32) (param $data_len i32)
    (result i32)
    (local $i i32)
    (if (i32.ne (local.get $key_len) (i32.const 32)) (then (unreachable)))
    (global.set $CUR_STATE (global.get $TRANSIENT_BASE))
    (local.set $i (i32.const 0))
    (block $brk
      (loop $lp
        (br_if $brk (i32.ge_s (local.get $i) (i32.const 8)))
        (i32.store
          (i32.add (global.get $TCV_OFF) (i32.shl (local.get $i) (i32.const 2)))
          (call $load_le32
            (i32.add (local.get $key_ptr) (i32.shl (local.get $i) (i32.const 2)))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $lp)))
    (call $reset_with (global.get $TCV_OFF) (i32.const 16)) ;; KEYED_HASH
    (call $update_inner (local.get $data_ptr) (local.get $data_len))
    (call $finalize_inner)
    (call $emit_digest_ret))

  ;; ─── derive-key (one-shot) ───────────────────────────────────────────
  (func (export "covalence:hash/api@0.1.0#derive-key")
    (param $ctx_ptr i32) (param $ctx_len i32)
    (param $km_ptr i32) (param $km_len i32)
    (result i32)
    (local $i i32)
    (global.set $CUR_STATE (global.get $TRANSIENT_BASE))
    ;; Pass 1: hash ctx with IV and DERIVE_KEY_CONTEXT.
    (call $store_iv_at (global.get $TCV_OFF))
    (call $reset_with (global.get $TCV_OFF) (i32.const 32)) ;; DERIVE_KEY_CONTEXT
    (call $update_inner (local.get $ctx_ptr) (local.get $ctx_len))
    (call $finalize_inner)
    ;; Copy 32-byte context key (now at $TCV_OFF as 8 native words) → $DK_CTX_OFF.
    (local.set $i (i32.const 0))
    (block $brk
      (loop $lp
        (br_if $brk (i32.ge_s (local.get $i) (i32.const 8)))
        (i32.store
          (i32.add (global.get $DK_CTX_OFF) (i32.shl (local.get $i) (i32.const 2)))
          (i32.load (i32.add (global.get $TCV_OFF) (i32.shl (local.get $i) (i32.const 2)))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $lp)))
    ;; Pass 2: hash key_material with context_key and DERIVE_KEY_MATERIAL.
    (call $reset_with (global.get $DK_CTX_OFF) (i32.const 64)) ;; DERIVE_KEY_MATERIAL
    (call $update_inner (local.get $km_ptr) (local.get $km_len))
    (call $finalize_inner)
    (call $emit_digest_ret))

  ;; ─── cabi_realloc — bump allocator + memory growth ───────────────────
  (func $cabi_realloc
    (param $orig_ptr i32) (param $orig_size i32)
    (param $align i32) (param $new_size i32)
    (result i32)
    (local $bump i32) (local $mask i32) (local $aligned i32)
    (local $end i32) (local $cur_bytes i32) (local $need_pages i32)
    (if (i32.ne (local.get $orig_ptr) (i32.const 0)) (then (unreachable)))
    (local.set $bump (i32.load (global.get $BUMP_PTR)))
    (if (i32.eqz (local.get $bump))
      (then (local.set $bump (global.get $BUMP_HEAP_START))))
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
    (i32.store (global.get $BUMP_PTR) (local.get $end))
    (local.get $aligned))

  (func (export "cabi_realloc")
    (param i32) (param i32) (param i32) (param i32) (result i32)
    (call $cabi_realloc
      (local.get 0) (local.get 1) (local.get 2) (local.get 3)))
)
