//! Native-only **float differential suite**: for every WASM `f32`/`f64` op the
//! catalogue exposes, compile a tiny WASM module using that instruction, run it
//! in wasmtime (the WASM **deterministic profile** — NaN canonicalization on,
//! round-to-nearest-even), and assert **bit-for-bit** agreement with the
//! corresponding float [`CanonRule`](covalence_pure::CanonRule). A divergence is
//! a *soundness* finding: our CanonRules claim to denote WASM semantics, and the
//! covalence-core float family certificates mint `⊢ f32.add a b = c` from them.
//!
//! wasmtime is a **dev-dependency, target-gated to `not(wasm32)`** (see
//! `Cargo.toml`) so `covalence-pure-eval` itself never depends on it and stays
//! wasm32-clean. This file only builds under a native target.
#![cfg(not(target_arch = "wasm32"))]

use covalence_pure::{CanonRule, F32, F64};
use covalence_pure_eval::*;
use covalence_wasm::compile_wat;
use covalence_wasm::engine::wasmtime::{Config, Engine, Instance, Module, Store, Val};

// ---------------------------------------------------------------------------
// wasmtime harness (deterministic profile)
// ---------------------------------------------------------------------------

/// An engine with **NaN canonicalization** on — Cranelift replaces every
/// arithmetic NaN result with the single canonical NaN (`0x7fc0_0000` /
/// `0x7ff8_..0`, positive), matching `F32::canon`/`F64::canon` and making
/// execution deterministic across hosts. This is the "WASM deterministic
/// profile" the float ops commit to.
fn engine() -> Engine {
    let mut cfg = Config::new();
    cfg.cranelift_nan_canonicalization(true);
    Engine::new(&cfg).expect("engine")
}

/// Compile a one-function WAT module (via covalence-wasm's `compile_wat`, then
/// `Module::from_binary` — not wasmtime's own WAT path).
fn module(eng: &Engine, wat: &str) -> Module {
    let bytes = compile_wat(wat).expect("compile_wat");
    Module::from_binary(eng, &bytes).expect("from_binary")
}

/// Instantiate `module` (no imports) and call its exported `op` with `args`.
fn call(eng: &Engine, m: &Module, args: &[Val]) -> Val {
    let mut store = Store::new(eng, ());
    let inst = Instance::new(&mut store, m, &[]).expect("instantiate");
    let f = inst.get_func(&mut store, "op").expect("export op");
    let mut out = [Val::I32(0)];
    f.call(&mut store, args, &mut out).expect("call op");
    out[0]
}

fn as_f32(v: &Val) -> u32 {
    match v {
        Val::F32(b) => *b,
        other => panic!("expected f32, got {other:?}"),
    }
}
fn as_f64(v: &Val) -> u64 {
    match v {
        Val::F64(b) => *b,
        other => panic!("expected f64, got {other:?}"),
    }
}
fn as_i32(v: &Val) -> i32 {
    match v {
        Val::I32(x) => *x,
        other => panic!("expected i32, got {other:?}"),
    }
}
fn as_i64(v: &Val) -> i64 {
    match v {
        Val::I64(x) => *x,
        other => panic!("expected i64, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Adversarial operand banks (as raw bits)
// ---------------------------------------------------------------------------

/// f32 bit patterns: ±0, ±1, rounding ties (0.5/1.5/2.5), ±max-normal, both
/// subnormal extremes, ±inf, canonical/signaling/payload NaNs (incl. a negative
/// NaN), and the int-saturation boundaries (2^31, 2^31−1, −2^31, 2^32, 2^63,
/// 2^64, −2^63) for `trunc_sat`.
const F32_BITS: &[u32] = &[
    0x0000_0000, // +0.0
    0x8000_0000, // -0.0
    0x3f80_0000, // 1.0
    0xbf80_0000, // -1.0
    0x3f00_0000, // 0.5
    0x3fc0_0000, // 1.5
    0x4020_0000, // 2.5
    0xbf00_0000, // -0.5   (trunc/ceil/nearest -> -0.0: sign-of-zero)
    0xbfc0_0000, // -1.5   (nearest ties-to-even -> -2.0)
    0xc020_0000, // -2.5   (nearest ties-to-even -> -2.0)
    0x7f7f_ffff, // max normal
    0xff7f_ffff, // -max normal
    0x0000_0001, // smallest subnormal
    0x007f_ffff, // largest subnormal
    0x8000_0001, // smallest negative subnormal
    0x7f80_0000, // +inf
    0xff80_0000, // -inf
    0x7fc0_0000, // canonical qNaN
    0x7f80_0001, // signaling NaN
    0x7fc0_1234, // qNaN with payload
    0xffc0_5678, // negative qNaN with payload
    0x4f00_0000, // 2^31          (> i32::MAX)
    0x4eff_ffff, // 2147483520    (< i32::MAX)
    0xcf00_0000, // -2^31         (= i32::MIN)
    0x4f80_0000, // 2^32          (> u32::MAX)
    0x5f00_0000, // 2^63
    0xdf00_0000, // -2^63
    0x5f80_0000, // 2^64
    0x42f6_e979, // 123.456
];

/// f64 bit patterns, analogous to [`F32_BITS`] (with 2^53±1 rounding boundaries
/// and 32/63/64-bit int-saturation edges for `trunc_sat`).
const F64_BITS: &[u64] = &[
    0x0000_0000_0000_0000, // +0.0
    0x8000_0000_0000_0000, // -0.0
    0x3ff0_0000_0000_0000, // 1.0
    0xbff0_0000_0000_0000, // -1.0
    0x3fe0_0000_0000_0000, // 0.5
    0xbfe0_0000_0000_0000, // -0.5   (trunc/ceil/nearest -> -0.0: sign-of-zero)
    0xbff8_0000_0000_0000, // -1.5   (nearest ties-to-even -> -2.0)
    0xc004_0000_0000_0000, // -2.5   (nearest ties-to-even -> -2.0)
    0x3ff8_0000_0000_0000, // 1.5
    0x4004_0000_0000_0000, // 2.5
    0x7fef_ffff_ffff_ffff, // max normal
    0xffef_ffff_ffff_ffff, // -max normal
    0x0000_0000_0000_0001, // smallest subnormal
    0x000f_ffff_ffff_ffff, // largest subnormal
    0x7ff0_0000_0000_0000, // +inf
    0xfff0_0000_0000_0000, // -inf
    0x7ff8_0000_0000_0000, // canonical qNaN
    0x7ff0_0000_0000_0001, // signaling NaN
    0x7ff8_0000_1234_5678, // qNaN with payload
    0xfff8_0000_0abc_def0, // negative qNaN with payload
    0x41e0_0000_0000_0000, // 2^31
    0x41df_ffff_ffc0_0000, // 2147483647.0 (i32::MAX)
    0xc1e0_0000_0000_0000, // -2^31
    0x41f0_0000_0000_0000, // 2^32
    0x43e0_0000_0000_0000, // 2^63
    0xc3e0_0000_0000_0000, // -2^63
    0x43f0_0000_0000_0000, // 2^64
    0x4020_0000_0000_0000, // 8.0
    0x3fbf_9add_3746_f65f, // 0.1234
];

const I32_OPS: &[i32] = &[
    0,
    1,
    -1,
    2,
    -2,
    100,
    -100,
    i32::MIN,
    i32::MAX,
    i32::MIN + 1,
    i32::MAX - 1,
    16_777_217, // 2^24 + 1 (not exactly f32-representable ⇒ exercises rounding)
    -16_777_217,
    0x0123_4567,
];
const I64_OPS: &[i64] = &[
    0,
    1,
    -1,
    i64::MIN,
    i64::MAX,
    i64::MIN + 1,
    i64::MAX - 1,
    9_007_199_254_740_993, // 2^53 + 1 (not exactly f64-representable)
    -9_007_199_254_740_993,
    16_777_217, // 2^24 + 1 (f32 rounding)
    0x0123_4567_89ab_cdef,
];
const U32_OPS: &[u32] = &[
    0,
    1,
    2,
    100,
    u32::MAX,
    u32::MAX - 1,
    0x8000_0000,
    16_777_217,
];
const U64_OPS: &[u64] = &[
    0,
    1,
    u64::MAX,
    u64::MAX - 1,
    0x8000_0000_0000_0000,
    9_007_199_254_740_993, // 2^53 + 1
    16_777_217,
];

// ---------------------------------------------------------------------------
// f32 / f64 arithmetic + min/max/copysign (binary → same width)
// ---------------------------------------------------------------------------

fn check_f32_binop(eng: &Engine, instr: &str, ours: impl Fn(F32, F32) -> F32) {
    let m = module(
        eng,
        &format!(
            "(module (func (export \"op\") (param f32 f32) (result f32) local.get 0 local.get 1 {instr}))"
        ),
    );
    for &a in F32_BITS {
        for &b in F32_BITS {
            let w = as_f32(&call(eng, &m, &[Val::F32(a), Val::F32(b)]));
            let o = ours(F32::from_bits(a), F32::from_bits(b)).to_bits();
            assert_eq!(
                w, o,
                "{instr}: a={a:#010x} b={b:#010x} wasm={w:#010x} ours={o:#010x}"
            );
        }
    }
}

fn check_f64_binop(eng: &Engine, instr: &str, ours: impl Fn(F64, F64) -> F64) {
    let m = module(
        eng,
        &format!(
            "(module (func (export \"op\") (param f64 f64) (result f64) local.get 0 local.get 1 {instr}))"
        ),
    );
    for &a in F64_BITS {
        for &b in F64_BITS {
            let w = as_f64(&call(eng, &m, &[Val::F64(a), Val::F64(b)]));
            let o = ours(F64::from_bits(a), F64::from_bits(b)).to_bits();
            assert_eq!(
                w, o,
                "{instr}: a={a:#018x} b={b:#018x} wasm={w:#018x} ours={o:#018x}"
            );
        }
    }
}

#[test]
fn f32_binops() {
    let eng = engine();
    check_f32_binop(&eng, "f32.add", |a, b| F32Add.eval(&(a, b)).unwrap());
    check_f32_binop(&eng, "f32.sub", |a, b| F32Sub.eval(&(a, b)).unwrap());
    check_f32_binop(&eng, "f32.mul", |a, b| F32Mul.eval(&(a, b)).unwrap());
    check_f32_binop(&eng, "f32.div", |a, b| F32Div.eval(&(a, b)).unwrap());
    check_f32_binop(&eng, "f32.min", |a, b| F32Min.eval(&(a, b)).unwrap());
    check_f32_binop(&eng, "f32.max", |a, b| F32Max.eval(&(a, b)).unwrap());
    check_f32_binop(&eng, "f32.copysign", |a, b| {
        F32Copysign.eval(&(a, b)).unwrap()
    });
}

#[test]
fn f64_binops() {
    let eng = engine();
    check_f64_binop(&eng, "f64.add", |a, b| F64Add.eval(&(a, b)).unwrap());
    check_f64_binop(&eng, "f64.sub", |a, b| F64Sub.eval(&(a, b)).unwrap());
    check_f64_binop(&eng, "f64.mul", |a, b| F64Mul.eval(&(a, b)).unwrap());
    check_f64_binop(&eng, "f64.div", |a, b| F64Div.eval(&(a, b)).unwrap());
    check_f64_binop(&eng, "f64.min", |a, b| F64Min.eval(&(a, b)).unwrap());
    check_f64_binop(&eng, "f64.max", |a, b| F64Max.eval(&(a, b)).unwrap());
    check_f64_binop(&eng, "f64.copysign", |a, b| {
        F64Copysign.eval(&(a, b)).unwrap()
    });
}

// ---------------------------------------------------------------------------
// unary → same width (sqrt / abs / neg / rounding)
// ---------------------------------------------------------------------------

fn check_f32_unop(eng: &Engine, instr: &str, ours: impl Fn(F32) -> F32) {
    let m = module(
        eng,
        &format!("(module (func (export \"op\") (param f32) (result f32) local.get 0 {instr}))"),
    );
    for &a in F32_BITS {
        let w = as_f32(&call(eng, &m, &[Val::F32(a)]));
        let o = ours(F32::from_bits(a)).to_bits();
        assert_eq!(w, o, "{instr}: a={a:#010x} wasm={w:#010x} ours={o:#010x}");
    }
}

fn check_f64_unop(eng: &Engine, instr: &str, ours: impl Fn(F64) -> F64) {
    let m = module(
        eng,
        &format!("(module (func (export \"op\") (param f64) (result f64) local.get 0 {instr}))"),
    );
    for &a in F64_BITS {
        let w = as_f64(&call(eng, &m, &[Val::F64(a)]));
        let o = ours(F64::from_bits(a)).to_bits();
        assert_eq!(w, o, "{instr}: a={a:#018x} wasm={w:#018x} ours={o:#018x}");
    }
}

#[test]
fn f32_unops() {
    let eng = engine();
    check_f32_unop(&eng, "f32.sqrt", |a| F32Sqrt.eval(&a).unwrap());
    check_f32_unop(&eng, "f32.abs", |a| F32Abs.eval(&a).unwrap());
    check_f32_unop(&eng, "f32.neg", |a| F32Neg.eval(&a).unwrap());
    check_f32_unop(&eng, "f32.ceil", |a| F32Ceil.eval(&a).unwrap());
    check_f32_unop(&eng, "f32.floor", |a| F32Floor.eval(&a).unwrap());
    check_f32_unop(&eng, "f32.trunc", |a| F32Trunc.eval(&a).unwrap());
    check_f32_unop(&eng, "f32.nearest", |a| F32Nearest.eval(&a).unwrap());
}

#[test]
fn f64_unops() {
    let eng = engine();
    check_f64_unop(&eng, "f64.sqrt", |a| F64Sqrt.eval(&a).unwrap());
    check_f64_unop(&eng, "f64.abs", |a| F64Abs.eval(&a).unwrap());
    check_f64_unop(&eng, "f64.neg", |a| F64Neg.eval(&a).unwrap());
    check_f64_unop(&eng, "f64.ceil", |a| F64Ceil.eval(&a).unwrap());
    check_f64_unop(&eng, "f64.floor", |a| F64Floor.eval(&a).unwrap());
    check_f64_unop(&eng, "f64.trunc", |a| F64Trunc.eval(&a).unwrap());
    check_f64_unop(&eng, "f64.nearest", |a| F64Nearest.eval(&a).unwrap());
}

// ---------------------------------------------------------------------------
// comparisons (binary → i32 boolean)
// ---------------------------------------------------------------------------

fn check_f32_cmp(eng: &Engine, instr: &str, ours: impl Fn(F32, F32) -> bool) {
    let m = module(
        eng,
        &format!(
            "(module (func (export \"op\") (param f32 f32) (result i32) local.get 0 local.get 1 {instr}))"
        ),
    );
    for &a in F32_BITS {
        for &b in F32_BITS {
            let w = as_i32(&call(eng, &m, &[Val::F32(a), Val::F32(b)]));
            let o = i32::from(ours(F32::from_bits(a), F32::from_bits(b)));
            assert_eq!(w, o, "{instr}: a={a:#010x} b={b:#010x} wasm={w} ours={o}");
        }
    }
}

fn check_f64_cmp(eng: &Engine, instr: &str, ours: impl Fn(F64, F64) -> bool) {
    let m = module(
        eng,
        &format!(
            "(module (func (export \"op\") (param f64 f64) (result i32) local.get 0 local.get 1 {instr}))"
        ),
    );
    for &a in F64_BITS {
        for &b in F64_BITS {
            let w = as_i32(&call(eng, &m, &[Val::F64(a), Val::F64(b)]));
            let o = i32::from(ours(F64::from_bits(a), F64::from_bits(b)));
            assert_eq!(w, o, "{instr}: a={a:#018x} b={b:#018x} wasm={w} ours={o}");
        }
    }
}

#[test]
fn f32_compares() {
    let eng = engine();
    check_f32_cmp(&eng, "f32.eq", |a, b| F32Eq.eval(&(a, b)).unwrap());
    check_f32_cmp(&eng, "f32.ne", |a, b| F32Ne.eval(&(a, b)).unwrap());
    check_f32_cmp(&eng, "f32.lt", |a, b| F32Lt.eval(&(a, b)).unwrap());
    check_f32_cmp(&eng, "f32.gt", |a, b| F32Gt.eval(&(a, b)).unwrap());
    check_f32_cmp(&eng, "f32.le", |a, b| F32Le.eval(&(a, b)).unwrap());
    check_f32_cmp(&eng, "f32.ge", |a, b| F32Ge.eval(&(a, b)).unwrap());
}

#[test]
fn f64_compares() {
    let eng = engine();
    check_f64_cmp(&eng, "f64.eq", |a, b| F64Eq.eval(&(a, b)).unwrap());
    check_f64_cmp(&eng, "f64.ne", |a, b| F64Ne.eval(&(a, b)).unwrap());
    check_f64_cmp(&eng, "f64.lt", |a, b| F64Lt.eval(&(a, b)).unwrap());
    check_f64_cmp(&eng, "f64.gt", |a, b| F64Gt.eval(&(a, b)).unwrap());
    check_f64_cmp(&eng, "f64.le", |a, b| F64Le.eval(&(a, b)).unwrap());
    check_f64_cmp(&eng, "f64.ge", |a, b| F64Ge.eval(&(a, b)).unwrap());
}

// ---------------------------------------------------------------------------
// width conversions: promote / demote
// ---------------------------------------------------------------------------

#[test]
fn promote_demote() {
    let eng = engine();
    let prom = module(
        &eng,
        "(module (func (export \"op\") (param f32) (result f64) local.get 0 f64.promote_f32))",
    );
    for &a in F32_BITS {
        let w = as_f64(&call(&eng, &prom, &[Val::F32(a)]));
        let o = F64PromoteF32.eval(&F32::from_bits(a)).unwrap().to_bits();
        assert_eq!(
            w, o,
            "f64.promote_f32: a={a:#010x} wasm={w:#018x} ours={o:#018x}"
        );
    }
    let dem = module(
        &eng,
        "(module (func (export \"op\") (param f64) (result f32) local.get 0 f32.demote_f64))",
    );
    for &a in F64_BITS {
        let w = as_f32(&call(&eng, &dem, &[Val::F64(a)]));
        let o = F32DemoteF64.eval(&F64::from_bits(a)).unwrap().to_bits();
        assert_eq!(
            w, o,
            "f32.demote_f64: a={a:#018x} wasm={w:#010x} ours={o:#010x}"
        );
    }
}

// ---------------------------------------------------------------------------
// reinterpret (raw bit moves; NaN payloads preserved, no canonicalization)
// ---------------------------------------------------------------------------

#[test]
fn reinterpret() {
    let eng = engine();
    // f32.reinterpret_i32
    let m = module(
        &eng,
        "(module (func (export \"op\") (param i32) (result f32) local.get 0 f32.reinterpret_i32))",
    );
    for &bits in F32_BITS {
        let i = bits as i32;
        let w = as_f32(&call(&eng, &m, &[Val::I32(i)]));
        let o = F32ReinterpretI32.eval(&i).unwrap().to_bits();
        assert_eq!(w, o, "f32.reinterpret_i32: {i:#010x}");
    }
    // i32.reinterpret_f32
    let m = module(
        &eng,
        "(module (func (export \"op\") (param f32) (result i32) local.get 0 i32.reinterpret_f32))",
    );
    for &bits in F32_BITS {
        let w = as_i32(&call(&eng, &m, &[Val::F32(bits)]));
        let o = I32ReinterpretF32.eval(&F32::from_bits(bits)).unwrap();
        assert_eq!(w, o, "i32.reinterpret_f32: {bits:#010x}");
    }
    // f64.reinterpret_i64
    let m = module(
        &eng,
        "(module (func (export \"op\") (param i64) (result f64) local.get 0 f64.reinterpret_i64))",
    );
    for &bits in F64_BITS {
        let i = bits as i64;
        let w = as_f64(&call(&eng, &m, &[Val::I64(i)]));
        let o = F64ReinterpretI64.eval(&i).unwrap().to_bits();
        assert_eq!(w, o, "f64.reinterpret_i64: {i:#018x}");
    }
    // i64.reinterpret_f64
    let m = module(
        &eng,
        "(module (func (export \"op\") (param f64) (result i64) local.get 0 i64.reinterpret_f64))",
    );
    for &bits in F64_BITS {
        let w = as_i64(&call(&eng, &m, &[Val::F64(bits)]));
        let o = I64ReinterpretF64.eval(&F64::from_bits(bits)).unwrap();
        assert_eq!(w, o, "i64.reinterpret_f64: {bits:#018x}");
    }
}

// ---------------------------------------------------------------------------
// float → int, saturating (trunc_sat)
// ---------------------------------------------------------------------------

#[test]
fn trunc_sat_f32() {
    let eng = engine();
    let s32 = module(
        &eng,
        "(module (func (export \"op\") (param f32) (result i32) local.get 0 i32.trunc_sat_f32_s))",
    );
    let u32m = module(
        &eng,
        "(module (func (export \"op\") (param f32) (result i32) local.get 0 i32.trunc_sat_f32_u))",
    );
    let s64 = module(
        &eng,
        "(module (func (export \"op\") (param f32) (result i64) local.get 0 i64.trunc_sat_f32_s))",
    );
    let u64m = module(
        &eng,
        "(module (func (export \"op\") (param f32) (result i64) local.get 0 i64.trunc_sat_f32_u))",
    );
    for &bits in F32_BITS {
        let v = F32::from_bits(bits);
        assert_eq!(
            as_i32(&call(&eng, &s32, &[Val::F32(bits)])),
            I32TruncSatF32.eval(&v).unwrap(),
            "i32.trunc_sat_f32_s: {bits:#010x}"
        );
        assert_eq!(
            as_i32(&call(&eng, &u32m, &[Val::F32(bits)])) as u32,
            U32TruncSatF32.eval(&v).unwrap(),
            "i32.trunc_sat_f32_u: {bits:#010x}"
        );
        assert_eq!(
            as_i64(&call(&eng, &s64, &[Val::F32(bits)])),
            I64TruncSatF32.eval(&v).unwrap(),
            "i64.trunc_sat_f32_s: {bits:#010x}"
        );
        assert_eq!(
            as_i64(&call(&eng, &u64m, &[Val::F32(bits)])) as u64,
            U64TruncSatF32.eval(&v).unwrap(),
            "i64.trunc_sat_f32_u: {bits:#010x}"
        );
    }
}

#[test]
fn trunc_sat_f64() {
    let eng = engine();
    let s32 = module(
        &eng,
        "(module (func (export \"op\") (param f64) (result i32) local.get 0 i32.trunc_sat_f64_s))",
    );
    let u32m = module(
        &eng,
        "(module (func (export \"op\") (param f64) (result i32) local.get 0 i32.trunc_sat_f64_u))",
    );
    let s64 = module(
        &eng,
        "(module (func (export \"op\") (param f64) (result i64) local.get 0 i64.trunc_sat_f64_s))",
    );
    let u64m = module(
        &eng,
        "(module (func (export \"op\") (param f64) (result i64) local.get 0 i64.trunc_sat_f64_u))",
    );
    for &bits in F64_BITS {
        let v = F64::from_bits(bits);
        assert_eq!(
            as_i32(&call(&eng, &s32, &[Val::F64(bits)])),
            I32TruncSatF64.eval(&v).unwrap(),
            "i32.trunc_sat_f64_s: {bits:#018x}"
        );
        assert_eq!(
            as_i32(&call(&eng, &u32m, &[Val::F64(bits)])) as u32,
            U32TruncSatF64.eval(&v).unwrap(),
            "i32.trunc_sat_f64_u: {bits:#018x}"
        );
        assert_eq!(
            as_i64(&call(&eng, &s64, &[Val::F64(bits)])),
            I64TruncSatF64.eval(&v).unwrap(),
            "i64.trunc_sat_f64_s: {bits:#018x}"
        );
        assert_eq!(
            as_i64(&call(&eng, &u64m, &[Val::F64(bits)])) as u64,
            U64TruncSatF64.eval(&v).unwrap(),
            "i64.trunc_sat_f64_u: {bits:#018x}"
        );
    }
}

// ---------------------------------------------------------------------------
// int → float (convert; rounds to nearest-even, never NaN)
// ---------------------------------------------------------------------------

#[test]
fn convert_to_f32() {
    let eng = engine();
    let cs32 = module(
        &eng,
        "(module (func (export \"op\") (param i32) (result f32) local.get 0 f32.convert_i32_s))",
    );
    let cu32 = module(
        &eng,
        "(module (func (export \"op\") (param i32) (result f32) local.get 0 f32.convert_i32_u))",
    );
    let cs64 = module(
        &eng,
        "(module (func (export \"op\") (param i64) (result f32) local.get 0 f32.convert_i64_s))",
    );
    let cu64 = module(
        &eng,
        "(module (func (export \"op\") (param i64) (result f32) local.get 0 f32.convert_i64_u))",
    );
    for &i in I32_OPS {
        assert_eq!(
            as_f32(&call(&eng, &cs32, &[Val::I32(i)])),
            F32ConvertI32.eval(&i).unwrap().to_bits(),
            "f32.convert_i32_s: {i}"
        );
    }
    for &u in U32_OPS {
        assert_eq!(
            as_f32(&call(&eng, &cu32, &[Val::I32(u as i32)])),
            F32ConvertU32.eval(&u).unwrap().to_bits(),
            "f32.convert_i32_u: {u}"
        );
    }
    for &i in I64_OPS {
        assert_eq!(
            as_f32(&call(&eng, &cs64, &[Val::I64(i)])),
            F32ConvertI64.eval(&i).unwrap().to_bits(),
            "f32.convert_i64_s: {i}"
        );
    }
    for &u in U64_OPS {
        assert_eq!(
            as_f32(&call(&eng, &cu64, &[Val::I64(u as i64)])),
            F32ConvertU64.eval(&u).unwrap().to_bits(),
            "f32.convert_i64_u: {u}"
        );
    }
}

#[test]
fn convert_to_f64() {
    let eng = engine();
    let cs32 = module(
        &eng,
        "(module (func (export \"op\") (param i32) (result f64) local.get 0 f64.convert_i32_s))",
    );
    let cu32 = module(
        &eng,
        "(module (func (export \"op\") (param i32) (result f64) local.get 0 f64.convert_i32_u))",
    );
    let cs64 = module(
        &eng,
        "(module (func (export \"op\") (param i64) (result f64) local.get 0 f64.convert_i64_s))",
    );
    let cu64 = module(
        &eng,
        "(module (func (export \"op\") (param i64) (result f64) local.get 0 f64.convert_i64_u))",
    );
    for &i in I32_OPS {
        assert_eq!(
            as_f64(&call(&eng, &cs32, &[Val::I32(i)])),
            F64ConvertI32.eval(&i).unwrap().to_bits(),
            "f64.convert_i32_s: {i}"
        );
    }
    for &u in U32_OPS {
        assert_eq!(
            as_f64(&call(&eng, &cu32, &[Val::I32(u as i32)])),
            F64ConvertU32.eval(&u).unwrap().to_bits(),
            "f64.convert_i32_u: {u}"
        );
    }
    for &i in I64_OPS {
        assert_eq!(
            as_f64(&call(&eng, &cs64, &[Val::I64(i)])),
            F64ConvertI64.eval(&i).unwrap().to_bits(),
            "f64.convert_i64_s: {i}"
        );
    }
    for &u in U64_OPS {
        assert_eq!(
            as_f64(&call(&eng, &cu64, &[Val::I64(u as i64)])),
            F64ConvertU64.eval(&u).unwrap().to_bits(),
            "f64.convert_i64_u: {u}"
        );
    }
}
