# Handoff: f32/f64 + ball arithmetic

**Goal:** f32/f64 support → ball arithmetic → statistics. A float IS its
bit-pattern; `f32 := u32` / `f64 := u64` newtypes + NaN-canonical base wrappers
already exist. Full course F0–F5 in memory `float-ball-track`.

## DONE + merged to main (audited)

- **F0** (608de02c): full WASM f32/f64 op inventory in
  `crates/kernel/base/trusted/src/float.rs` — sqrt/min/max/abs/neg/copysign,
  ceil/floor/trunc/nearest, IEEE compares, promote/demote, trunc_sat convert,
  reinterpret. Single NaN-canonicalization point preserved (arithmetic routes
  through it; abs/neg/copysign/reinterpret are payload-preserving bit moves).
  +445 TCB lines.
- **F1** (8b43a697): 62 ops admitted into `Builtins` via
  `crates/kernel/base/eval/src/float.rs`; **native-only wasmtime v45 differential
  suite** (`tests/differential_float.rs`) — bit-for-bit vs a real engine over
  ±0/±inf/NaN(canonical+signaling+payload)/subnormal/trunc_sat-boundary/tie
  operands (incl. added negatives), ALL MATCH. `covalence-pure-eval` stays
  wasm32-clean (wasmtime is target-gated out; verified). Audit: all sound.
- **F2a** (d3d71699): `mk_u32`/`mk_u64`/`as_u32`/`as_u64` in the hol-eval literal
  facade (float-literal prerequisite; routes through the facade so it survives
  the literal redesign).

**Soundness caveat (documented):** bit-for-bit agreement holds under the WASM
**deterministic profile** (NaN canonicalization on). Against a non-canonicalizing
engine / raw x86, an invalid-op NaN sign diverges from our canonical NaN. Our
ops target the deterministic profile by design.

## Next — PAUSED behind the defs-out-of-core priority

Architecture decided (recommended, precedent = how `int` works), **awaiting a
final go**: **two-layer** — (1) declared bit-level ops `f32.addBits : u32→u32→u32`
+ a `FloatCert` admitted family (TCB, mirrors FixedWidthCert) dispatching to the
base `F32Add` CanonRule; (2) typed ops `f32.add : f32→f32→f32` DEFINED via twins
over the bit ops + rep/abs (untrusted), built incrementally (only what ball
arithmetic needs). Then:

- **F2b** (TCB): bit ops + `FloatCert` + `ToHolF32`/`ToHolF64`.
- **F2c** (untrusted): twin-defined typed f64 ops for ball arithmetic.
- **F3** folded into F2b.
- **F4**: ball arithmetic (`ball := f64 × f64`, concrete outward-rounded ops now;
  enclosure theorems `x∈a,y∈b ⟹ x•y∈ball_add a b` proved incrementally as
  `Thm<CoreHol,_>` — the pure-tier-validates-eval-tier test story).

NB: F2/F3 float certs are exactly the kind of `defs::`-coupled cert family the
defs-out-of-core plan reworks — so doing defs-out FIRST means floats land on the
clean (base-op-keyed) cert architecture, not the old one. That's why floats are
paused behind it.
