# Handoff: f32/f64 + ball arithmetic

**Goal:** f32/f64 support → ball arithmetic → statistics. A float IS its
bit-pattern; `f32 := u32` / `f64 := u64` newtypes + NaN-canonical base wrappers.
Full course F0–F5 in memory `float-ball-track`.

## Done + merged (audited)

- **F0** — full WASM f32/f64 op inventory in
  `crates/kernel/base/trusted/src/float.rs`: sqrt/min/max/abs/neg/copysign,
  ceil/floor/trunc/nearest, IEEE compares, promote/demote, trunc_sat convert,
  reinterpret. Single NaN-canonicalization point (arithmetic routes through it;
  abs/neg/copysign/reinterpret are payload-preserving bit moves).
- **F1** — 62 ops admitted into `Builtins` via `crates/kernel/base/eval/src/
  float.rs`; native-only wasmtime differential suite
  (`tests/differential_float.rs`) — bit-for-bit vs a real engine over ±0/±inf/
  NaN(canonical+signaling+payload)/subnormal/trunc_sat-boundary/tie operands, all
  match. `covalence-pure-eval` stays wasm32-clean (wasmtime target-gated out).
- **F2a** — `mk_u32`/`mk_u64`/`as_u32`/`as_u64` in the hol-eval literal facade.
- **F2b (TCB)** — bit-level ops `f32.addBits : u32→u32→u32` + the `FloatCert`
  admitted family (mirrors FixedWidthCert) dispatching to the base `F32Add`
  CanonRule + `ToHolF32`/`ToHolF64` (`hol/eval/src/typed_float.rs`, `certs.rs`,
  `defs/floats.rs`). Symbolic landers so far: the binaries add/mul only (see
  eval `SKELETONS.md` for the sub/div/min/max/copysign, unary, compare, and
  conversion shapes still to add).
- **F2c (data)** — typed ops `f32.add : f32→f32→f32` defined via twins over the
  bit ops + rep/abs; ball groundwork in `crates/kernel/hol/init/src/init/ball.rs`
  (`ball := f64 × f64` midpoint–radius, outward-rounded `ball.add`, eval driver —
  data + evaluation only, formula provisional until F4 proves it).

**Soundness caveat (documented):** bit-for-bit agreement holds under the WASM
deterministic profile (NaN canonicalization on). Against a non-canonicalizing
engine / raw x86, an invalid-op NaN sign diverges from our canonical NaN. Our
ops target the deterministic profile by design.

## Open — F4 enclosure theorems

The containment contract `x ∈ X ∧ y ∈ Y ⟹ x + y ∈ ball.add X Y` is unproved
(`init/ball.rs`; init `SKELETONS.md` §F4). Needs a real-side ball-membership
predicate + IEEE rounding-error lemmas over the typed f64 ops — proved
incrementally as `Thm<CoreHol,_>` (the pure-tier-validates-eval-tier story).
The same rounding-error lemmas back the correctly-rounded decimal→binary f64
enclosure work. F5 = statistics on top.
