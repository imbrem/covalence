;; BLAKE3 ("BLAKE3: one function, fast everywhere", 2020, §2) —
;; hand-written WAT, single-instance ("object model") shape.
;;
;; Implements `blake3-stateful.wit`:
;;   init / update / finalize (plain-mode streaming)
;;   keyed-hash / derive-key  (one-shots; reset the instance)
;;   compress                  (block primitive: t=0, b=64, d=0)
;; The composed one-shot `hash` is added by `compose_one_shot` during
;; rebuild as `init; update(data); finalize()`.
;;
;; Memory layout (single page initial = 64 KiB; cabi_realloc grows it):
;;   [   0,  64) — compress state[16] words (full 16-word state buffer)
;;   [  64, 128) — message buffer m[16] words (LE-decoded block)
;;   [ 128, 192) — permutation scratch (next message buffer)
;;   [ 192, 224) — temp CV scratch (truncate8 output)
;;   [ 224, 256) — derive-key context-key scratch (32 B)
;;   [ 256, 320) — parent block buffer (64 B, used for stack merges)
;;   [ 320, 512) — reserved scratch
;;   [ 512, 516) — cabi_realloc bump pointer
;;   [ 516, 4096) — reserved
;;   [4096, 6144) — single hasher state (see field layout below)
;;   [6144,65536) — cabi_realloc bump heap
;;
;; Hasher state layout (at $S_OFF = 4096, 2048 bytes total):
;;   +   0  i32×8    key_words      (initial CV per chunk, native i32) — 32 B
;;   +  32  i32×8    chunk_cv       (running CV within current chunk)  — 32 B
;;   +  64  byte×64  chunk_block    (current partial block being filled) — 64 B
;;   + 128  i32      chunk_block_len           (bytes in chunk_block, 0..64)
;;   + 132  i32      chunk_blocks_compressed   (full blocks compressed in chunk, 0..16)
;;   + 136  i32      chunk_counter_lo          (low 32 bits of chunk counter)
;;   + 140  i32      chunk_counter_hi          (high 32 bits)
;;   + 144  i32      flags                     (mode flags: 0 / KEYED_HASH / DERIVE_KEY_MATERIAL)
;;   + 148  i32      cv_stack_len              (number of subtree CVs on stack, 0..54)
;;   + 152..(152+54*32)  cv_stack[54]          (subtree chaining values)
;;
;; The cv_stack depth of 54 covers any input up to 2^54 chunks ≈ 2^64
;; bytes — the i64 chunk-counter limit, larger than any realistic input.

(module
  (memory (export "memory") 1)

  ;; ─── Scratch offsets ─────────────────────────────────────────────────
  (global $STATE_OFF i32 (i32.const 0))
  (global $MSG_OFF i32 (i32.const 64))
  (global $PMSG_OFF i32 (i32.const 128))
  (global $TCV_OFF i32 (i32.const 192))
  (global $DK_CTX_OFF i32 (i32.const 224))
  (global $PB_OFF i32 (i32.const 256))
  (global $BUMP_PTR i32 (i32.const 512))

  ;; ─── Stateful state offsets (relative to $S_OFF) ─────────────────────
  (global $S_OFF i32 (i32.const 4096))
  (global $S_KEY_OFF i32 (i32.const 0))            ;; +0
  (global $S_CHUNK_CV_OFF i32 (i32.const 32))      ;; +32
  (global $S_CHUNK_BLOCK_OFF i32 (i32.const 64))   ;; +64
  (global $S_BLOCK_LEN_OFF i32 (i32.const 128))    ;; +128
  (global $S_BLOCKS_COMPR_OFF i32 (i32.const 132)) ;; +132
  (global $S_CTR_LO_OFF i32 (i32.const 136))       ;; +136
  (global $S_CTR_HI_OFF i32 (i32.const 140))       ;; +140
  (global $S_FLAGS_OFF i32 (i32.const 144))        ;; +144
  (global $S_STACK_LEN_OFF i32 (i32.const 148))    ;; +148
  (global $S_STACK_OFF i32 (i32.const 152))        ;; +152

  ;; ─── Flag bits (spec §2.2) ───────────────────────────────────────────
  ;; CHUNK_START         = 1
  ;; CHUNK_END           = 2
  ;; PARENT              = 4
  ;; ROOT                = 8
  ;; KEYED_HASH          = 16
  ;; DERIVE_KEY_CONTEXT  = 32
  ;; DERIVE_KEY_MATERIAL = 64

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
  ;;
  ;; G operates on four state cells s[a], s[b], s[c], s[d] in place,
  ;; mixing two message words mx, my. State cells live in linear memory
  ;; at $STATE_OFF + 4*idx as little-endian native i32 words.
  ;;
  ;;   s[a] := s[a] + s[b] + mx
  ;;   s[d] := rotr(s[d] ^ s[a], 16)
  ;;   s[c] := s[c] + s[d]
  ;;   s[b] := rotr(s[b] ^ s[c], 12)
  ;;   s[a] := s[a] + s[b] + my
  ;;   s[d] := rotr(s[d] ^ s[a], 8)
  ;;   s[c] := s[c] + s[d]
  ;;   s[b] := rotr(s[b] ^ s[c], 7)
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
  ;;
  ;; m points at 16 native-i32 message words.
  (func $round (param $m i32)
    ;; Column step.
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
    ;; Diagonal step.
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
  ;;
  ;; MSG_PERMUTATION = [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8]
  ;; Writes permuted view of $src to $dst (both 16 native-i32 words).
  (func $permute (param $src i32) (param $dst i32)
    (i32.store (i32.add (local.get $dst) (i32.const 0))
      (i32.load (i32.add (local.get $src) (i32.const 8))))   ;; new[0] = old[2]
    (i32.store (i32.add (local.get $dst) (i32.const 4))
      (i32.load (i32.add (local.get $src) (i32.const 24))))  ;; new[1] = old[6]
    (i32.store (i32.add (local.get $dst) (i32.const 8))
      (i32.load (i32.add (local.get $src) (i32.const 12))))  ;; new[2] = old[3]
    (i32.store (i32.add (local.get $dst) (i32.const 12))
      (i32.load (i32.add (local.get $src) (i32.const 40))))  ;; new[3] = old[10]
    (i32.store (i32.add (local.get $dst) (i32.const 16))
      (i32.load (i32.add (local.get $src) (i32.const 28))))  ;; new[4] = old[7]
    (i32.store (i32.add (local.get $dst) (i32.const 20))
      (i32.load (i32.add (local.get $src) (i32.const 0))))   ;; new[5] = old[0]
    (i32.store (i32.add (local.get $dst) (i32.const 24))
      (i32.load (i32.add (local.get $src) (i32.const 16))))  ;; new[6] = old[4]
    (i32.store (i32.add (local.get $dst) (i32.const 28))
      (i32.load (i32.add (local.get $src) (i32.const 52))))  ;; new[7] = old[13]
    (i32.store (i32.add (local.get $dst) (i32.const 32))
      (i32.load (i32.add (local.get $src) (i32.const 4))))   ;; new[8] = old[1]
    (i32.store (i32.add (local.get $dst) (i32.const 36))
      (i32.load (i32.add (local.get $src) (i32.const 44))))  ;; new[9] = old[11]
    (i32.store (i32.add (local.get $dst) (i32.const 40))
      (i32.load (i32.add (local.get $src) (i32.const 48))))  ;; new[10] = old[12]
    (i32.store (i32.add (local.get $dst) (i32.const 44))
      (i32.load (i32.add (local.get $src) (i32.const 20))))  ;; new[11] = old[5]
    (i32.store (i32.add (local.get $dst) (i32.const 48))
      (i32.load (i32.add (local.get $src) (i32.const 36))))  ;; new[12] = old[9]
    (i32.store (i32.add (local.get $dst) (i32.const 52))
      (i32.load (i32.add (local.get $src) (i32.const 56))))  ;; new[13] = old[14]
    (i32.store (i32.add (local.get $dst) (i32.const 56))
      (i32.load (i32.add (local.get $src) (i32.const 60))))  ;; new[14] = old[15]
    (i32.store (i32.add (local.get $dst) (i32.const 60))
      (i32.load (i32.add (local.get $src) (i32.const 32))))) ;; new[15] = old[8]

  ;; ─── Compression function (spec §2.3) ────────────────────────────────
  ;;
  ;; Writes the full 16-word state at $STATE_OFF.
  ;;   cv_ptr: 32 bytes (8 native i32 words) — input chaining value
  ;;   block_ptr: 64 bytes (LE byte stream) — message block
  ;;   t_lo, t_hi: counter (low/high 32 bits)
  ;;   b: block_len
  ;;   d: flags
  ;;
  ;; Initial state (spec eq. (2.1)):
  ;;   s[ 0.. 8] = cv[0..8]
  ;;   s[ 8..12] = IV[0..4]                = {0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A}
  ;;   s[12] = t_lo
  ;;   s[13] = t_hi
  ;;   s[14] = b
  ;;   s[15] = d
  ;; Then 7 rounds; permute message between rounds (not after the last).
  (func $compress
    (param $cv_ptr i32) (param $block_ptr i32)
    (param $t_lo i32) (param $t_hi i32) (param $b i32) (param $d i32)
    (local $i i32) (local $r i32) (local $src i32) (local $dst i32) (local $tmp i32)

    ;; Load cv into state[0..8].
    (local.set $i (i32.const 0))
    (block $brk
      (loop $lp
        (br_if $brk (i32.ge_s (local.get $i) (i32.const 8)))
        (i32.store
          (i32.add (global.get $STATE_OFF) (i32.shl (local.get $i) (i32.const 2)))
          (i32.load (i32.add (local.get $cv_ptr) (i32.shl (local.get $i) (i32.const 2)))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $lp)))

    ;; IV constants into state[8..12].
    (i32.store
      (i32.add (global.get $STATE_OFF) (i32.const 32)) (i32.const 0x6A09E667))
    (i32.store
      (i32.add (global.get $STATE_OFF) (i32.const 36)) (i32.const 0xBB67AE85))
    (i32.store
      (i32.add (global.get $STATE_OFF) (i32.const 40)) (i32.const 0x3C6EF372))
    (i32.store
      (i32.add (global.get $STATE_OFF) (i32.const 44)) (i32.const 0xA54FF53A))

    ;; Counter, block_len, flags into state[12..16].
    (i32.store (i32.add (global.get $STATE_OFF) (i32.const 48)) (local.get $t_lo))
    (i32.store (i32.add (global.get $STATE_OFF) (i32.const 52)) (local.get $t_hi))
    (i32.store (i32.add (global.get $STATE_OFF) (i32.const 56)) (local.get $b))
    (i32.store (i32.add (global.get $STATE_OFF) (i32.const 60)) (local.get $d))

    ;; Decode block bytes (LE) into message buffer m[0..16] at $MSG_OFF.
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

    ;; 7 rounds: round(m); m = permute(m); …; round(m_final).
    ;; We alternate between $MSG_OFF and $PMSG_OFF as ping-pong buffers.
    (local.set $src (global.get $MSG_OFF))
    (local.set $dst (global.get $PMSG_OFF))
    (local.set $r (i32.const 0))
    (block $brk3
      (loop $lp3
        (br_if $brk3 (i32.ge_s (local.get $r) (i32.const 6)))
        (call $round (local.get $src))
        (call $permute (local.get $src) (local.get $dst))
        ;; swap src and dst
        (local.set $tmp (local.get $src))
        (local.set $src (local.get $dst))
        (local.set $dst (local.get $tmp))
        (local.set $r (i32.add (local.get $r) (i32.const 1)))
        (br $lp3)))
    ;; 7th (final) round, no permutation after.
    (call $round (local.get $src)))

  ;; truncate8: write XOR of first 8 and last 8 state words to out_cv_ptr (32 B).
  ;; Used to derive a 32-byte CV from the full 16-word state.
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

  ;; ─── Initialization helpers ──────────────────────────────────────────
  ;;
  ;; IV[0..8] = {0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
  ;;             0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19}

  (func $store_iv_at (param $ptr i32)
    (i32.store (local.get $ptr)                         (i32.const 0x6A09E667))
    (i32.store (i32.add (local.get $ptr) (i32.const 4)) (i32.const 0xBB67AE85))
    (i32.store (i32.add (local.get $ptr) (i32.const 8)) (i32.const 0x3C6EF372))
    (i32.store (i32.add (local.get $ptr) (i32.const 12)) (i32.const 0xA54FF53A))
    (i32.store (i32.add (local.get $ptr) (i32.const 16)) (i32.const 0x510E527F))
    (i32.store (i32.add (local.get $ptr) (i32.const 20)) (i32.const 0x9B05688C))
    (i32.store (i32.add (local.get $ptr) (i32.const 24)) (i32.const 0x1F83D9AB))
    (i32.store (i32.add (local.get $ptr) (i32.const 28)) (i32.const 0x5BE0CD19)))

  ;; Reset everything for a new hashing pass with the given key_words at
  ;; `src_key_ptr` (32 B, 8 native i32 words) and `mode_flags` (e.g.
  ;; KEYED_HASH or DERIVE_KEY_MATERIAL or 0 for plain).
  (func $reset_with (param $src_key_ptr i32) (param $mode_flags i32)
    (local $i i32)
    ;; Copy key_words (8 words = 32 bytes).
    (local.set $i (i32.const 0))
    (block $brk
      (loop $lp
        (br_if $brk (i32.ge_s (local.get $i) (i32.const 8)))
        (i32.store
          (i32.add (i32.add (global.get $S_OFF) (global.get $S_KEY_OFF))
                   (i32.shl (local.get $i) (i32.const 2)))
          (i32.load (i32.add (local.get $src_key_ptr)
                             (i32.shl (local.get $i) (i32.const 2)))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $lp)))
    ;; Copy key_words → chunk_cv (starting CV = key_words).
    (local.set $i (i32.const 0))
    (block $brk2
      (loop $lp2
        (br_if $brk2 (i32.ge_s (local.get $i) (i32.const 8)))
        (i32.store
          (i32.add (i32.add (global.get $S_OFF) (global.get $S_CHUNK_CV_OFF))
                   (i32.shl (local.get $i) (i32.const 2)))
          (i32.load (i32.add (i32.add (global.get $S_OFF) (global.get $S_KEY_OFF))
                             (i32.shl (local.get $i) (i32.const 2)))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $lp2)))
    ;; Zero the chunk_block (64 bytes) so output() sees clean zero-pad.
    (local.set $i (i32.const 0))
    (block $brk3
      (loop $lp3
        (br_if $brk3 (i32.ge_s (local.get $i) (i32.const 64)))
        (i32.store8
          (i32.add (i32.add (global.get $S_OFF) (global.get $S_CHUNK_BLOCK_OFF))
                   (local.get $i))
          (i32.const 0))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $lp3)))
    ;; Reset scalar fields.
    (i32.store (i32.add (global.get $S_OFF) (global.get $S_BLOCK_LEN_OFF)) (i32.const 0))
    (i32.store (i32.add (global.get $S_OFF) (global.get $S_BLOCKS_COMPR_OFF)) (i32.const 0))
    (i32.store (i32.add (global.get $S_OFF) (global.get $S_CTR_LO_OFF)) (i32.const 0))
    (i32.store (i32.add (global.get $S_OFF) (global.get $S_CTR_HI_OFF)) (i32.const 0))
    (i32.store (i32.add (global.get $S_OFF) (global.get $S_FLAGS_OFF)) (local.get $mode_flags))
    (i32.store (i32.add (global.get $S_OFF) (global.get $S_STACK_LEN_OFF)) (i32.const 0))
    ;; Reset bump allocator so repeated hash() calls don't accumulate
    ;; garbage in the heap.
    (i32.store (global.get $BUMP_PTR) (i32.const 0)))

  ;; ─── Counter helpers (64-bit chunk counter) ──────────────────────────
  ;;
  ;; Increment chunk counter by 1.
  (func $inc_chunk_counter
    (local $lo i32)
    (local $new_lo i32)
    (local.set $lo (i32.load (i32.add (global.get $S_OFF) (global.get $S_CTR_LO_OFF))))
    (local.set $new_lo (i32.add (local.get $lo) (i32.const 1)))
    (i32.store (i32.add (global.get $S_OFF) (global.get $S_CTR_LO_OFF)) (local.get $new_lo))
    (if (i32.lt_u (local.get $new_lo) (local.get $lo))
      (then
        (i32.store
          (i32.add (global.get $S_OFF) (global.get $S_CTR_HI_OFF))
          (i32.add
            (i32.load (i32.add (global.get $S_OFF) (global.get $S_CTR_HI_OFF)))
            (i32.const 1))))))

  ;; ─── Chunk CV stack management ───────────────────────────────────────
  ;;
  ;; Push a chunk CV onto the stack and fold equal-height subtrees via
  ;; PARENT compression. Spec §2.1: a chunk's leaf is "added" at index
  ;; total_chunks_after_this. While the index is even, merge with the
  ;; top of the stack (i.e. while the lowest bit of total_chunks is 0).
  ;;
  ;; `chunk_cv_ptr` points at the 32-byte CV to push (8 native i32 words).
  ;; `total_chunks_after` is the post-increment chunk count (1-based).
  ;; Modifies the cv_stack and cv_stack_len in place.
  ;; Mutates compress scratch.
  (func $add_chunk_cv (param $chunk_cv_ptr i32) (param $total_chunks_after i32)
    (local $tc i32)
    (local $stack_len i32)
    (local $top_ptr i32)
    (local $merged_ptr i32)
    (local $i i32)
    (local $mode_flags i32)
    (local.set $tc (local.get $total_chunks_after))
    (local.set $stack_len
      (i32.load (i32.add (global.get $S_OFF) (global.get $S_STACK_LEN_OFF))))
    (local.set $mode_flags
      (i32.load (i32.add (global.get $S_OFF) (global.get $S_FLAGS_OFF))))

    ;; Use $TCV_OFF as the merged-CV scratch slot, $PB_OFF as the parent
    ;; block buffer.
    (local.set $merged_ptr (global.get $TCV_OFF))
    ;; Initially "current" CV is the one passed in.
    ;; Copy to merged_ptr so we can iteratively re-merge.
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
        ;; Stop merging when tc is odd (lowest bit set).
        (br_if $brk_merge (i32.eq (i32.and (local.get $tc) (i32.const 1)) (i32.const 1)))
        ;; Pop top of stack into parent block buffer first half; merged
        ;; CV is the second half.
        (local.set $stack_len (i32.sub (local.get $stack_len) (i32.const 1)))
        (local.set $top_ptr
          (i32.add (i32.add (global.get $S_OFF) (global.get $S_STACK_OFF))
                   (i32.shl (local.get $stack_len) (i32.const 5))))
        ;; Build parent block: left = top_ptr (32 B), right = merged_ptr (32 B).
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
        ;; Compress(key_words, parent_block, 0, 64, PARENT | mode_flags).
        ;; Then truncate8 into merged_ptr — but $TCV_OFF == merged_ptr,
        ;; and truncate8 writes to a 32 B region. We need to use a
        ;; *different* output buffer to avoid clobbering inputs of the
        ;; next iteration's parent block. So write to $S_OFF + S_CHUNK_CV_OFF?
        ;; That's a state slot we shouldn't pollute mid-stream. Use
        ;; a small scratch: after compress, state is at $STATE_OFF; we
        ;; can truncate8 directly into merged_ptr safely because the
        ;; truncate8 reads from $STATE_OFF (independent of merged_ptr).
        (call $compress
          (i32.add (global.get $S_OFF) (global.get $S_KEY_OFF))
          (global.get $PB_OFF)
          (i32.const 0) (i32.const 0)
          (i32.const 64)
          (i32.or (local.get $mode_flags) (i32.const 4))) ;; PARENT = 4
        (call $truncate8 (local.get $merged_ptr))

        ;; Halve tc to advance to the parent level.
        (local.set $tc (i32.shr_u (local.get $tc) (i32.const 1)))
        (br $lp_merge)))

    ;; Push merged CV onto the stack at position stack_len.
    (local.set $top_ptr
      (i32.add (i32.add (global.get $S_OFF) (global.get $S_STACK_OFF))
               (i32.shl (local.get $stack_len) (i32.const 5))))
    (local.set $i (i32.const 0))
    (block $brk_push
      (loop $lp_push
        (br_if $brk_push (i32.ge_s (local.get $i) (i32.const 8)))
        (i32.store
          (i32.add (local.get $top_ptr) (i32.shl (local.get $i) (i32.const 2)))
          (i32.load (i32.add (local.get $merged_ptr) (i32.shl (local.get $i) (i32.const 2)))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $lp_push)))
    (i32.store
      (i32.add (global.get $S_OFF) (global.get $S_STACK_LEN_OFF))
      (i32.add (local.get $stack_len) (i32.const 1))))

  ;; ─── Chunk-block compression: compress current block, fold into CV ───
  ;;
  ;; If $is_last is 0: compress the current FULL block (64 B) with
  ;; CHUNK_START (if first block of chunk) flag added; the result
  ;; updates chunk_cv in place. blocks_compressed += 1.
  ;; We don't apply CHUNK_END here — that's for output()/finalize.
  (func $compress_full_block
    (local $start_flag i32)
    (local $mode_flags i32)
    (local $blocks i32)
    (local.set $blocks
      (i32.load (i32.add (global.get $S_OFF) (global.get $S_BLOCKS_COMPR_OFF))))
    (local.set $start_flag
      (if (result i32) (i32.eqz (local.get $blocks))
        (then (i32.const 1)) ;; CHUNK_START
        (else (i32.const 0))))
    (local.set $mode_flags
      (i32.load (i32.add (global.get $S_OFF) (global.get $S_FLAGS_OFF))))
    (call $compress
      (i32.add (global.get $S_OFF) (global.get $S_CHUNK_CV_OFF))
      (i32.add (global.get $S_OFF) (global.get $S_CHUNK_BLOCK_OFF))
      (i32.load (i32.add (global.get $S_OFF) (global.get $S_CTR_LO_OFF)))
      (i32.load (i32.add (global.get $S_OFF) (global.get $S_CTR_HI_OFF)))
      (i32.const 64)
      (i32.or (local.get $mode_flags) (local.get $start_flag)))
    ;; chunk_cv = truncate8(state)
    (call $truncate8 (i32.add (global.get $S_OFF) (global.get $S_CHUNK_CV_OFF)))
    (i32.store
      (i32.add (global.get $S_OFF) (global.get $S_BLOCKS_COMPR_OFF))
      (i32.add (local.get $blocks) (i32.const 1))))

  ;; ─── update(data_ptr, data_len) ──────────────────────────────────────
  ;;
  ;; Stream `data_len` bytes into the current chunk; spill full blocks
  ;; via $compress_full_block; spill full chunks via $finish_chunk.
  ;; The "delayed compression" pattern: we don't compress block 16; if
  ;; the chunk is exactly 1024 bytes (16 blocks), we leave block 16 in
  ;; the buffer with CHUNK_END pending so a future output() can apply
  ;; the right flags.
  ;;
  ;; Actually we follow the standard reference: when chunk_len == 1024,
  ;; emit chunk CV via "output", push to stack, reset chunk. The output()
  ;; path runs the LAST block compression with CHUNK_END so the chunk
  ;; CV is correct.
  (func $update_impl (param $data_ptr i32) (param $data_len i32)
    (local $block_len i32) (local $room i32) (local $take i32) (local $i i32)
    (block $brk_outer
      (loop $lp_outer
        (br_if $brk_outer (i32.eqz (local.get $data_len)))

        ;; If current chunk is full (16 blocks worth = 1024 bytes), finalize it.
        ;; chunk_total_len = blocks_compressed * 64 + block_len.
        (if (i32.eq
              (i32.add
                (i32.shl
                  (i32.load (i32.add (global.get $S_OFF) (global.get $S_BLOCKS_COMPR_OFF)))
                  (i32.const 6))
                (i32.load (i32.add (global.get $S_OFF) (global.get $S_BLOCK_LEN_OFF))))
              (i32.const 1024))
          (then
            (call $finish_chunk)))

        ;; If the per-block buffer is full, compress and reset it.
        (local.set $block_len
          (i32.load (i32.add (global.get $S_OFF) (global.get $S_BLOCK_LEN_OFF))))
        (if (i32.eq (local.get $block_len) (i32.const 64))
          (then
            (call $compress_full_block)
            (i32.store
              (i32.add (global.get $S_OFF) (global.get $S_BLOCK_LEN_OFF))
              (i32.const 0))
            (local.set $block_len (i32.const 0))))

        ;; Take min(64 - block_len, data_len) bytes into chunk_block at
        ;; offset block_len.
        (local.set $room (i32.sub (i32.const 64) (local.get $block_len)))
        (local.set $take
          (if (result i32) (i32.lt_u (local.get $data_len) (local.get $room))
            (then (local.get $data_len))
            (else (local.get $room))))
        (local.set $i (i32.const 0))
        (block $brk_cp
          (loop $lp_cp
            (br_if $brk_cp (i32.ge_s (local.get $i) (local.get $take)))
            (i32.store8
              (i32.add
                (i32.add (global.get $S_OFF) (global.get $S_CHUNK_BLOCK_OFF))
                (i32.add (local.get $block_len) (local.get $i)))
              (i32.load8_u (i32.add (local.get $data_ptr) (local.get $i))))
            (local.set $i (i32.add (local.get $i) (i32.const 1)))
            (br $lp_cp)))
        (i32.store
          (i32.add (global.get $S_OFF) (global.get $S_BLOCK_LEN_OFF))
          (i32.add (local.get $block_len) (local.get $take)))
        (local.set $data_ptr (i32.add (local.get $data_ptr) (local.get $take)))
        (local.set $data_len (i32.sub (local.get $data_len) (local.get $take)))
        (br $lp_outer))))
  (func (export "covalence:hash/api@0.1.0#update")
    (param $data_ptr i32) (param $data_len i32)
    (call $update_impl (local.get $data_ptr) (local.get $data_len)))

  ;; ─── Finish current chunk: compute its CV via output() and push ──────
  ;;
  ;; The buffered block is the LAST block (possibly partial, possibly the
  ;; 16th full block). Run a CHUNK_END compression on it from the current
  ;; chunk_cv and chunk_counter; truncate8 → chunk CV. Push to cv_stack
  ;; with fold-equal-heights logic. Reset for the next chunk:
  ;; chunk_counter += 1, chunk_cv = key_words, block_len = 0,
  ;; blocks_compressed = 0, zero the block buffer.
  (func $finish_chunk
    (local $start_flag i32) (local $mode_flags i32) (local $blocks i32)
    (local $tc_lo i32) (local $tc_hi i32)
    (local $i i32)
    (local.set $blocks
      (i32.load (i32.add (global.get $S_OFF) (global.get $S_BLOCKS_COMPR_OFF))))
    (local.set $start_flag
      (if (result i32) (i32.eqz (local.get $blocks))
        (then (i32.const 1)) ;; CHUNK_START
        (else (i32.const 0))))
    (local.set $mode_flags
      (i32.load (i32.add (global.get $S_OFF) (global.get $S_FLAGS_OFF))))
    ;; Zero-pad the buffer past block_len for the final compression.
    (local.set $i
      (i32.load (i32.add (global.get $S_OFF) (global.get $S_BLOCK_LEN_OFF))))
    (block $brk_pad
      (loop $lp_pad
        (br_if $brk_pad (i32.ge_s (local.get $i) (i32.const 64)))
        (i32.store8
          (i32.add (i32.add (global.get $S_OFF) (global.get $S_CHUNK_BLOCK_OFF))
                   (local.get $i))
          (i32.const 0))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $lp_pad)))
    ;; CHUNK_END = 2. final flags = mode_flags | start_flag | CHUNK_END.
    (call $compress
      (i32.add (global.get $S_OFF) (global.get $S_CHUNK_CV_OFF))
      (i32.add (global.get $S_OFF) (global.get $S_CHUNK_BLOCK_OFF))
      (i32.load (i32.add (global.get $S_OFF) (global.get $S_CTR_LO_OFF)))
      (i32.load (i32.add (global.get $S_OFF) (global.get $S_CTR_HI_OFF)))
      (i32.load (i32.add (global.get $S_OFF) (global.get $S_BLOCK_LEN_OFF)))
      (i32.or (i32.or (local.get $mode_flags) (local.get $start_flag))
              (i32.const 2)))
    ;; truncate8 into $TCV_OFF to use as a scratch buffer for stacking.
    (call $truncate8 (global.get $TCV_OFF))

    ;; Increment chunk counter; pass NEW counter (1-based total chunks) to
    ;; add_chunk_cv.
    (call $inc_chunk_counter)
    (local.set $tc_lo
      (i32.load (i32.add (global.get $S_OFF) (global.get $S_CTR_LO_OFF))))
    (local.set $tc_hi
      (i32.load (i32.add (global.get $S_OFF) (global.get $S_CTR_HI_OFF))))
    ;; For the merge logic we only need the low 32 bits of tc; in
    ;; practice no realistic input exceeds 2^32 chunks (2^32 * 1024 ≈
    ;; 4 TiB). add_chunk_cv shifts tc_lo right at each merge; the high
    ;; bit fold-up is handled by depth-bounded stack size (54).
    (call $add_chunk_cv (global.get $TCV_OFF) (local.get $tc_lo))

    ;; Reset chunk_cv = key_words.
    (local.set $i (i32.const 0))
    (block $brk_k
      (loop $lp_k
        (br_if $brk_k (i32.ge_s (local.get $i) (i32.const 8)))
        (i32.store
          (i32.add (i32.add (global.get $S_OFF) (global.get $S_CHUNK_CV_OFF))
                   (i32.shl (local.get $i) (i32.const 2)))
          (i32.load (i32.add (i32.add (global.get $S_OFF) (global.get $S_KEY_OFF))
                             (i32.shl (local.get $i) (i32.const 2)))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $lp_k)))
    ;; Reset block_len, blocks_compressed; zero the chunk block.
    (i32.store (i32.add (global.get $S_OFF) (global.get $S_BLOCK_LEN_OFF)) (i32.const 0))
    (i32.store (i32.add (global.get $S_OFF) (global.get $S_BLOCKS_COMPR_OFF)) (i32.const 0))
    (local.set $i (i32.const 0))
    (block $brk_z
      (loop $lp_z
        (br_if $brk_z (i32.ge_s (local.get $i) (i32.const 64)))
        (i32.store8
          (i32.add (i32.add (global.get $S_OFF) (global.get $S_CHUNK_BLOCK_OFF))
                   (local.get $i))
          (i32.const 0))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $lp_z))))

  ;; ─── init (plain mode) ───────────────────────────────────────────────
  ;;
  ;; key_words = IV; mode_flags = 0.
  (func $init_impl
    (call $store_iv_at (global.get $TCV_OFF))
    (call $reset_with (global.get $TCV_OFF) (i32.const 0)))
  (func (export "covalence:hash/api@0.1.0#init")
    (call $init_impl))

  ;; ─── finalize ────────────────────────────────────────────────────────
  ;;
  ;; Build the root output. Two cases:
  ;;   (a) No subtrees on the stack — the in-progress chunk IS the root.
  ;;       Run its final-block compression with ROOT|CHUNK_END (and
  ;;       CHUNK_START if blocks_compressed == 0), then truncate8 →
  ;;       first 32 bytes of the (s[0..8] ^ s[8..16]) state are the
  ;;       output. The first chunk-output is the root.
  ;;   (b) Stack non-empty — first compute the in-progress chunk's CV
  ;;       (non-root), then walk the stack from top to bottom merging
  ;;       with PARENT. The FINAL parent merge gets ROOT.
  ;;
  ;; In both cases the very last compression is `flags | ROOT`. The
  ;; rest are non-root.
  (func $finalize_impl (result i32)
    (local $start_flag i32) (local $mode_flags i32)
    (local $blocks i32) (local $stack_len i32)
    (local $cur_cv_ptr i32) (local $cur_block_ptr i32)
    (local $cur_t_lo i32) (local $cur_t_hi i32)
    (local $cur_b i32) (local $cur_d i32)
    (local $out i32) (local $ret i32) (local $i i32) (local $p i32)
    (local $top_ptr i32)
    (local $merged_cv_ptr i32)
    (local.set $mode_flags
      (i32.load (i32.add (global.get $S_OFF) (global.get $S_FLAGS_OFF))))
    (local.set $stack_len
      (i32.load (i32.add (global.get $S_OFF) (global.get $S_STACK_LEN_OFF))))
    (local.set $blocks
      (i32.load (i32.add (global.get $S_OFF) (global.get $S_BLOCKS_COMPR_OFF))))
    (local.set $start_flag
      (if (result i32) (i32.eqz (local.get $blocks))
        (then (i32.const 1)) ;; CHUNK_START
        (else (i32.const 0))))

    ;; Zero-pad the buffered block past block_len.
    (local.set $i
      (i32.load (i32.add (global.get $S_OFF) (global.get $S_BLOCK_LEN_OFF))))
    (block $brk_pad
      (loop $lp_pad
        (br_if $brk_pad (i32.ge_s (local.get $i) (i32.const 64)))
        (i32.store8
          (i32.add (i32.add (global.get $S_OFF) (global.get $S_CHUNK_BLOCK_OFF))
                   (local.get $i))
          (i32.const 0))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $lp_pad)))

    ;; The "current Output" represents a deferred compression that we
    ;; will eventually run with the ROOT flag added.
    ;;   cur_cv  = chunk_cv  (8 native words)
    ;;   cur_blk = chunk_block (64 bytes)
    ;;   cur_t   = chunk_counter
    ;;   cur_b   = block_len
    ;;   cur_d   = mode_flags | start_flag | CHUNK_END
    (local.set $cur_cv_ptr
      (i32.add (global.get $S_OFF) (global.get $S_CHUNK_CV_OFF)))
    (local.set $cur_block_ptr
      (i32.add (global.get $S_OFF) (global.get $S_CHUNK_BLOCK_OFF)))
    (local.set $cur_t_lo
      (i32.load (i32.add (global.get $S_OFF) (global.get $S_CTR_LO_OFF))))
    (local.set $cur_t_hi
      (i32.load (i32.add (global.get $S_OFF) (global.get $S_CTR_HI_OFF))))
    (local.set $cur_b
      (i32.load (i32.add (global.get $S_OFF) (global.get $S_BLOCK_LEN_OFF))))
    (local.set $cur_d
      (i32.or (i32.or (local.get $mode_flags) (local.get $start_flag))
              (i32.const 2))) ;; CHUNK_END

    ;; If stack non-empty, walk it from top to bottom turning the
    ;; "current output" into a chain of parent_outputs.
    ;; Each iteration:
    ;;   1. Run current output as a non-root compression → cv (32 B).
    ;;   2. Pop top of stack into PB_OFF[0..32], cv into PB_OFF[32..64].
    ;;   3. cur becomes a PARENT output:
    ;;        cv = key_words; block = parent_block; t = 0; b = 64;
    ;;        d = mode_flags | PARENT.
    ;; After the loop, run cur as root: d |= ROOT, compress, truncate8.
    (block $brk_walk
      (loop $lp_walk
        (br_if $brk_walk (i32.eqz (local.get $stack_len)))
        ;; Step 1: non-root compress; truncate8 → temp.
        (call $compress
          (local.get $cur_cv_ptr) (local.get $cur_block_ptr)
          (local.get $cur_t_lo) (local.get $cur_t_hi)
          (local.get $cur_b) (local.get $cur_d))
        ;; Use the parent block buffer's *right half* slot as the cv
        ;; output. That way the next pop writes into the *left half*
        ;; and we don't need a separate scratch buffer.
        (local.set $merged_cv_ptr (i32.add (global.get $PB_OFF) (i32.const 32)))
        (call $truncate8 (local.get $merged_cv_ptr))
        ;; Step 2: pop top of stack into left half.
        (local.set $stack_len (i32.sub (local.get $stack_len) (i32.const 1)))
        (local.set $top_ptr
          (i32.add (i32.add (global.get $S_OFF) (global.get $S_STACK_OFF))
                   (i32.shl (local.get $stack_len) (i32.const 5))))
        (local.set $i (i32.const 0))
        (block $brk_l
          (loop $lp_l
            (br_if $brk_l (i32.ge_s (local.get $i) (i32.const 32)))
            (i32.store8
              (i32.add (global.get $PB_OFF) (local.get $i))
              (i32.load8_u (i32.add (local.get $top_ptr) (local.get $i))))
            (local.set $i (i32.add (local.get $i) (i32.const 1)))
            (br $lp_l)))
        ;; Step 3: make cur a PARENT output anchored at this block.
        (local.set $cur_cv_ptr
          (i32.add (global.get $S_OFF) (global.get $S_KEY_OFF)))
        (local.set $cur_block_ptr (global.get $PB_OFF))
        (local.set $cur_t_lo (i32.const 0))
        (local.set $cur_t_hi (i32.const 0))
        (local.set $cur_b (i32.const 64))
        (local.set $cur_d (i32.or (local.get $mode_flags) (i32.const 4))) ;; PARENT
        (br $lp_walk)))

    ;; Run the final compression with ROOT added.
    (call $compress
      (local.get $cur_cv_ptr) (local.get $cur_block_ptr)
      (local.get $cur_t_lo) (local.get $cur_t_hi)
      (local.get $cur_b)
      (i32.or (local.get $cur_d) (i32.const 8))) ;; ROOT
    ;; Truncate to 32 bytes (LE u32 ^ LE u32, written as LE bytes).
    (call $truncate8 (global.get $TCV_OFF))

    ;; Allocate 32-byte output buffer; serialize TCV (8 native LE words)
    ;; as LE bytes (already LE; on a wasm i32 store that's identical).
    (local.set $out (call $cabi_realloc
      (i32.const 0) (i32.const 0) (i32.const 1) (i32.const 32)))
    (local.set $i (i32.const 0))
    (block $brk_out
      (loop $lp_out
        (br_if $brk_out (i32.ge_s (local.get $i) (i32.const 8)))
        (call $store_le32
          (i32.add (local.get $out) (i32.shl (local.get $i) (i32.const 2)))
          (i32.load (i32.add (global.get $TCV_OFF)
                             (i32.shl (local.get $i) (i32.const 2)))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $lp_out)))

    ;; Build {ptr, len} return area.
    (local.set $ret (call $cabi_realloc
      (i32.const 0) (i32.const 0) (i32.const 4) (i32.const 8)))
    (i32.store (local.get $ret) (local.get $out))
    (i32.store (i32.add (local.get $ret) (i32.const 4)) (i32.const 32))
    (local.get $ret))
  (func (export "covalence:hash/api@0.1.0#finalize") (result i32)
    (call $finalize_impl))

  ;; ─── Public: compress (block primitive) ──────────────────────────────
  ;;
  ;; Apply the compression with counter = 0, block_len = 64, flags = 0,
  ;; then return truncate8(state) as 32 LE bytes. This is the most
  ;; reduced form of the BLAKE3 block function — useful as a
  ;; verifiable primitive even though it doesn't run the full hash.
  (func (export "covalence:hash/api@0.1.0#compress")
    (param $state_ptr i32) (param $state_len i32)
    (param $block_ptr i32) (param $block_len i32)
    (result i32)
    (local $out i32) (local $ret i32) (local $i i32)
    (local $native_state i32)
    (if (i32.ne (local.get $state_len) (i32.const 32)) (then (unreachable)))
    (if (i32.ne (local.get $block_len) (i32.const 64)) (then (unreachable)))
    ;; Decode caller's LE-encoded state into native i32 words.
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
    (local.set $out (call $cabi_realloc
      (i32.const 0) (i32.const 0) (i32.const 1) (i32.const 32)))
    (local.set $i (i32.const 0))
    (block $brk2
      (loop $lp2
        (br_if $brk2 (i32.ge_s (local.get $i) (i32.const 8)))
        (call $store_le32
          (i32.add (local.get $out) (i32.shl (local.get $i) (i32.const 2)))
          (i32.load (i32.add (global.get $TCV_OFF)
                             (i32.shl (local.get $i) (i32.const 2)))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $lp2)))
    (local.set $ret (call $cabi_realloc
      (i32.const 0) (i32.const 0) (i32.const 4) (i32.const 8)))
    (i32.store (local.get $ret) (local.get $out))
    (i32.store (i32.add (local.get $ret) (i32.const 4)) (i32.const 32))
    (local.get $ret))

  ;; ─── keyed-hash (one-shot) ───────────────────────────────────────────
  ;;
  ;; init with key_words = LE-decoded(key) and mode_flags = KEYED_HASH (16),
  ;; then update(data), then finalize.
  ;; Resets the stateful instance as a side effect.
  (func (export "covalence:hash/api@0.1.0#keyed-hash")
    (param $key_ptr i32) (param $key_len i32)
    (param $data_ptr i32) (param $data_len i32)
    (result i32)
    (local $i i32)
    (if (i32.ne (local.get $key_len) (i32.const 32)) (then (unreachable)))
    ;; Decode key (LE) into 8 native words at $TCV_OFF (scratch).
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
    (call $update_impl (local.get $data_ptr) (local.get $data_len))
    (call $finalize_impl))

  ;; ─── derive-key (one-shot) ───────────────────────────────────────────
  ;;
  ;; Pass 1: hash `context` with IV and DERIVE_KEY_CONTEXT (32) → 32-byte
  ;; context_key (stashed at $DK_CTX_OFF as 8 native words).
  ;; Pass 2: hash `key_material` with context_key and DERIVE_KEY_MATERIAL (64).
  ;; Resets the stateful instance as a side effect.
  (func (export "covalence:hash/api@0.1.0#derive-key")
    (param $ctx_ptr i32) (param $ctx_len i32)
    (param $km_ptr i32) (param $km_len i32)
    (result i32)
    (local $tmp_ret i32) (local $tmp_buf i32) (local $tmp_len i32) (local $i i32)
    ;; Pass 1: init plain → mode = DERIVE_KEY_CONTEXT; key = IV.
    (call $store_iv_at (global.get $TCV_OFF))
    (call $reset_with (global.get $TCV_OFF) (i32.const 32)) ;; DERIVE_KEY_CONTEXT
    (call $update_impl (local.get $ctx_ptr) (local.get $ctx_len))
    (local.set $tmp_ret (call $finalize_impl))
    ;; tmp_ret points at {ptr, len}. The 32-byte context key is at
    ;; *ptr. Copy as 8 LE words into $DK_CTX_OFF.
    (local.set $tmp_buf (i32.load (local.get $tmp_ret)))
    (local.set $tmp_len (i32.load (i32.add (local.get $tmp_ret) (i32.const 4))))
    (if (i32.ne (local.get $tmp_len) (i32.const 32)) (then (unreachable)))
    (local.set $i (i32.const 0))
    (block $brk
      (loop $lp
        (br_if $brk (i32.ge_s (local.get $i) (i32.const 8)))
        (i32.store
          (i32.add (global.get $DK_CTX_OFF) (i32.shl (local.get $i) (i32.const 2)))
          (call $load_le32
            (i32.add (local.get $tmp_buf) (i32.shl (local.get $i) (i32.const 2)))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $lp)))
    ;; Pass 2.
    (call $reset_with (global.get $DK_CTX_OFF) (i32.const 64)) ;; DERIVE_KEY_MATERIAL
    (call $update_impl (local.get $km_ptr) (local.get $km_len))
    (call $finalize_impl))

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
      (then (local.set $bump (i32.const 6144))))
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
