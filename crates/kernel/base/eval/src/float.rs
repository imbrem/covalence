//! WASM `f32`/`f64` float builtins — the catalogue overlay for the float
//! [`CanonRule`](covalence_pure::CanonRule)s that live in the TCB
//! (`covalence-pure-trusted::float`).
//!
//! Unlike `nat`/`int`/`bytes`/`fixed`, the float ops are **not defined here**:
//! their value sorts ([`F32`](covalence_pure::F32)/[`F64`](covalence_pure::F64),
//! bitwise-`Eq` with a single NaN-canonicalization point) and their `Op` +
//! `CanonRule` impls are trusted (a float *is* its bit-pattern, so leaf equality
//! and the WASM deterministic-NaN profile must be audited in one place). This
//! module only re-exports them and attaches the untrusted [`NamedRule`] overlay
//! (the dotted catalogue label — `"f32.add"`, `"f64.sqrt"`, `"s32.trunc_sat.f64"`,
//! …) so [`Builtins`](crate::Builtins) can admit them alongside the integer ops.
//!
//! Every body is **total** on bit-patterns (floats have no unrepresentable
//! result — arithmetic canonicalizes NaN, `trunc_sat`/`convert` saturate), so no
//! float op ever refuses (`None`). Bit-for-bit agreement with wasmtime is pinned
//! by the native-only differential suite (`tests/differential_float.rs`).

use crate::NamedRule;

// Re-export the trusted float ops so consumers reach them through the catalogue
// crate (identity is still the `TypeId`; the label below is a diagnostic overlay).
pub use covalence_pure::{
    F32Abs, F32Add, F32Ceil, F32ConvertI32, F32ConvertI64, F32ConvertU32, F32ConvertU64,
    F32Copysign, F32DemoteF64, F32Div, F32Eq, F32Floor, F32Ge, F32Gt, F32Le, F32Lt, F32Max, F32Min,
    F32Mul, F32Ne, F32Nearest, F32Neg, F32ReinterpretI32, F32Sqrt, F32Sub, F32Trunc, F64Abs,
    F64Add, F64Ceil, F64ConvertI32, F64ConvertI64, F64ConvertU32, F64ConvertU64, F64Copysign,
    F64Div, F64Eq, F64Floor, F64Ge, F64Gt, F64Le, F64Lt, F64Max, F64Min, F64Mul, F64Ne, F64Nearest,
    F64Neg, F64PromoteF32, F64ReinterpretI64, F64Sqrt, F64Sub, F64Trunc, I32ReinterpretF32,
    I32TruncSatF32, I32TruncSatF64, I64ReinterpretF64, I64TruncSatF32, I64TruncSatF64,
    U32TruncSatF32, U32TruncSatF64, U64TruncSatF32, U64TruncSatF64,
};

/// Attach the dotted catalogue label to a (foreign, trusted) float op — the
/// untrusted [`NamedRule`] overlay only (rule identity stays the `TypeId`).
macro_rules! float_name {
    ($($op:ident => $label:literal),* $(,)?) => {
        $(
            impl NamedRule for $op {
                fn name() -> String {
                    String::from($label)
                }
            }
        )*
    };
}

float_name! {
    // arithmetic
    F32Add => "f32.add",
    F32Sub => "f32.sub",
    F32Mul => "f32.mul",
    F32Div => "f32.div",
    F64Add => "f64.add",
    F64Sub => "f64.sub",
    F64Mul => "f64.mul",
    F64Div => "f64.div",
    // min / max / copysign
    F32Min => "f32.min",
    F32Max => "f32.max",
    F32Copysign => "f32.copysign",
    F64Min => "f64.min",
    F64Max => "f64.max",
    F64Copysign => "f64.copysign",
    // unary (sqrt / abs / neg / rounding)
    F32Sqrt => "f32.sqrt",
    F32Abs => "f32.abs",
    F32Neg => "f32.neg",
    F32Ceil => "f32.ceil",
    F32Floor => "f32.floor",
    F32Trunc => "f32.trunc",
    F32Nearest => "f32.nearest",
    F64Sqrt => "f64.sqrt",
    F64Abs => "f64.abs",
    F64Neg => "f64.neg",
    F64Ceil => "f64.ceil",
    F64Floor => "f64.floor",
    F64Trunc => "f64.trunc",
    F64Nearest => "f64.nearest",
    // comparisons (IEEE 754 ordering)
    F32Eq => "f32.eq",
    F32Ne => "f32.ne",
    F32Lt => "f32.lt",
    F32Gt => "f32.gt",
    F32Le => "f32.le",
    F32Ge => "f32.ge",
    F64Eq => "f64.eq",
    F64Ne => "f64.ne",
    F64Lt => "f64.lt",
    F64Gt => "f64.gt",
    F64Le => "f64.le",
    F64Ge => "f64.ge",
    // width conversions
    F64PromoteF32 => "f64.promote",
    F32DemoteF64 => "f32.demote",
    // reinterpret (raw bit moves; the int side uses the signed `sN` tag)
    F32ReinterpretI32 => "f32.reinterpret.s32",
    I32ReinterpretF32 => "s32.reinterpret.f32",
    F64ReinterpretI64 => "f64.reinterpret.s64",
    I64ReinterpretF64 => "s64.reinterpret.f64",
    // float → int, saturating (WASM `trunc_sat`)
    I32TruncSatF32 => "s32.trunc_sat.f32",
    U32TruncSatF32 => "u32.trunc_sat.f32",
    I64TruncSatF32 => "s64.trunc_sat.f32",
    U64TruncSatF32 => "u64.trunc_sat.f32",
    I32TruncSatF64 => "s32.trunc_sat.f64",
    U32TruncSatF64 => "u32.trunc_sat.f64",
    I64TruncSatF64 => "s64.trunc_sat.f64",
    U64TruncSatF64 => "u64.trunc_sat.f64",
    // int → float (WASM `convert`)
    F32ConvertI32 => "f32.convert.s32",
    F32ConvertU32 => "f32.convert.u32",
    F32ConvertI64 => "f32.convert.s64",
    F32ConvertU64 => "f32.convert.u64",
    F64ConvertI32 => "f64.convert.s32",
    F64ConvertU32 => "f64.convert.u32",
    F64ConvertI64 => "f64.convert.s64",
    F64ConvertU64 => "f64.convert.u64",
}
