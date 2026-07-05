//! # `covalence-pure-eval` — the `Builtins` base language
//!
//! Every native computation the kernel trusts, as an enumerable set of
//! [`CanonRule`](covalence_pure::CanonRule)s over [`covalence_types`] values (`Nat` / `Int` / `Bytes` /
//! the fixed-width `u8`…`u64`, `s8`…`s64` = `i8`…`i64`), gathered under one
//! ZST language, [`Builtins`]. This crate knows **nothing of HOL** — it
//! depends only on `covalence-pure` and `covalence-types` (the
//! `covalence-pure-eval -> covalence-core` edge is BANNED in
//! `scripts/dep-graph.mjs`; the dev-dependency used by the differential
//! tests is not a graph edge).
//!
//! ## Trust story
//!
//! Each op is a ZST implementing [`Op`](covalence_pure::Op) + [`CanonRule`](covalence_pure::CanonRule): *writing*
//! `App<F, _>` is always sound (uninterpreted ⇒ inert); *reducing* it via
//! [`canon`](covalence_pure::canon) is gated on the op's `TypeId` being
//! admitted by the language, and [`Builtins`] admits exactly the rules
//! enumerated in its static [`Manifest`] (pinned by the golden test against
//! `docs/deps/builtins-manifest.txt`). The audit surface is therefore: this
//! crate's `eval` bodies, one op at a time.
//!
//! ## Semantics — identical to `builtins.rs` by transcription
//!
//! The bodies transcribe `covalence-core`'s `builtins.rs`
//! (`eval_prim`/`reduce_int_op`) exactly, including the FORCED edge-case
//! conventions (`n mod 0 = n`, `x / 0 = 0`, `x rem 0 = x` — forced by the
//! catalogue ops' let-style definitional bodies; any divergence could mint
//! `⊢ False`). This is enforced by the differential suite
//! (`tests/differential.rs`) while the legacy kernel reducer still exists.
//!
//! ## Refusal vs. totality vs. OOM
//!
//! [`CanonRule::eval`](covalence_pure::CanonRule::eval) is **fallible** (returns
//! `Option`): an op computes the true answer where the result is representable,
//! **REFUSES** (`None`) where the answer is detectably unrepresentable, and panics
//! ONLY on genuine allocation failure (we attempt and the allocator aborts). No op
//! ever clamps an arbitrary-precision `Nat` to `usize`. Concretely:
//!
//! - `nat.shl` (`a·2^s`): `0` for `a = 0`; the true product where `s` fits `usize`
//!   (may OOM-panic on a huge but representable result); `None` when `a ≠ 0` and `s`
//!   exceeds `usize` (result has ≥ 2^64 bits — unrepresentable).
//! - `nat.pow` (`base^exp`): `0`/`1` for `base ∈ {0, 1}`; the true power where `exp`
//!   fits `u32` (OOM-panic acceptable); `None` when `exp` exceeds `u32`.
//! - `nat.shr` (`⌊a/2^s⌋`) is **total** — `0` for any `s ≥ 2^64` (any representable
//!   `a` has bit-length ≪ 2^64), so it never refuses.
//! - `bytes.at`/`bytes.slice` are **total** over `Nat` indices/lengths (out-of-range
//!   saturates to `0` / the empty or clamped-to-real-length subslice); `bytes.cat`/
//!   `bytes.consNat` may OOM-panic on allocation only.

use std::any::TypeId;

use covalence_pure::{LangMeta, Language, Manifest, RuleMeta, RuleRecord};

/// Declare one builtin op: a ZST implementing [`Op`](covalence_pure::Op) + [`CanonRule`](covalence_pure::CanonRule) +
/// [`NamedRule`]. The label is the kernel catalogue's dotted symbol (an
/// untrusted name overlay — identity is the `TypeId`).
macro_rules! canon_op {
    (
        $(#[$doc:meta])*
        $name:ident($label:literal): $in:ty => $out:ty,
        |$arg:pat_param| $body:expr
    ) => {
        $(#[$doc])*
        #[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
        pub struct $name;

        impl covalence_pure::Op for $name {
            type In = $in;
            type Out = $out;
        }

        impl covalence_pure::CanonRule for $name {
            fn eval(&self, arg: &Self::In) -> Option<Self::Out> {
                let $arg = arg;
                Some($body)
            }
        }

        impl NamedRule for $name {
            fn name() -> String {
                String::from($label)
            }
        }
    };
}

/// Like [`canon_op!`] but the `$body` **already yields `Option<$out>`** — for a
/// [`CanonRule`](covalence_pure::CanonRule) that REFUSES (returns `None`) on a
/// detectably unrepresentable input rather than computing a value. Used by the
/// fallible arbitrary-precision ops (`nat.shl`/`nat.pow`).
macro_rules! canon_op_partial {
    (
        $(#[$doc:meta])*
        $name:ident($label:literal): $in:ty => $out:ty,
        |$arg:pat_param| $body:expr
    ) => {
        $(#[$doc])*
        #[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
        pub struct $name;

        impl covalence_pure::Op for $name {
            type In = $in;
            type Out = $out;
        }

        impl covalence_pure::CanonRule for $name {
            fn eval(&self, arg: &Self::In) -> Option<Self::Out> {
                let $arg = arg;
                $body
            }
        }

        impl NamedRule for $name {
            fn name() -> String {
                String::from($label)
            }
        }
    };
}

pub mod bytes;
pub mod fixed;
pub mod int;
pub mod nat;

pub use bytes::{BytesAt, BytesCat, BytesConsNat, BytesLen, BytesSlice};
pub use fixed::{
    FwAdd, FwAnd, FwDiv, FwFromInt, FwFromNat, FwGe, FwGt, FwLe, FwLt, FwMul, FwNeg, FwNot, FwOr,
    FwRem, FwRepr, FwShl, FwShr, FwSub, FwToInt, FwToNat, FwXor, Sext, Zext,
};
pub use int::{
    IntAbs, IntAdd, IntDiv, IntLe, IntLt, IntMod, IntMul, IntNeg, IntPred, IntSgn, IntSub, IntSucc,
};
pub use nat::{
    NatAdd, NatBitAnd, NatBitOr, NatBitXor, NatDiv, NatFromBytesBe, NatFromBytesLe, NatLe, NatLt,
    NatMod, NatMul, NatPow, NatPred, NatShl, NatShr, NatSub, NatSucc, NatToBytesBe, NatToBytesLe,
    NatToInt,
};

/// Untrusted name overlay for the manifest projection: the kernel
/// catalogue's dotted label for a rule (`"nat.add"`, `"u8.zext.s16"`, …).
/// Names are for goldens/diagnostics only — rule identity is always the
/// `TypeId` ([`Manifest`] stores no names).
pub trait NamedRule {
    /// The dotted catalogue label.
    fn name() -> String;
}

/// One [`RuleRecord`] for rule type `T`.
const fn rule_record<T: 'static>() -> RuleRecord {
    RuleRecord {
        ty: TypeId::of::<T>(),
        metadata: RuleMeta,
    }
}

/// `(label, TypeId)` for rule type `T`.
fn name_of<T: NamedRule + 'static>() -> (String, TypeId) {
    (T::name(), TypeId::of::<T>())
}

/// Expands the whole rule inventory twice in lockstep: once as the static
/// [`RuleRecord`] slice (the manifest — `TypeId`s only), once as the
/// name-projected [`manifest_names`] (the untrusted overlay used by the
/// golden test). Keeping both expansions inside ONE macro invocation makes
/// order/1:1 drift impossible.
macro_rules! builtins_manifest {
    (
        simple { $($S:ty),* $(,)? }
        fw { $($T:ty),* $(,)? }
        casts { $($Src:ty => [$($Dst:ty),* $(,)?]);* $(;)? }
    ) => {
        /// Every rule [`Builtins`] admits, in catalogue order (nat, int,
        /// bytes, then the fixed-width families per representation, then
        /// the 8×8 `zext`/`sext` cast grid). A `const` (not a `static`) so
        /// [`BUILTINS_MANIFEST`] can embed it in const context.
        const BUILTINS_RULES: &[RuleRecord] = &[
            $(rule_record::<$S>(),)*
            $(
                rule_record::<FwAdd<$T>>(),
                rule_record::<FwSub<$T>>(),
                rule_record::<FwMul<$T>>(),
                rule_record::<FwDiv<$T>>(),
                rule_record::<FwRem<$T>>(),
                rule_record::<FwAnd<$T>>(),
                rule_record::<FwOr<$T>>(),
                rule_record::<FwXor<$T>>(),
                rule_record::<FwShl<$T>>(),
                rule_record::<FwShr<$T>>(),
                rule_record::<FwLt<$T>>(),
                rule_record::<FwLe<$T>>(),
                rule_record::<FwGt<$T>>(),
                rule_record::<FwGe<$T>>(),
                rule_record::<FwNeg<$T>>(),
                rule_record::<FwNot<$T>>(),
                rule_record::<FwToNat<$T>>(),
                rule_record::<FwToInt<$T>>(),
                rule_record::<FwFromNat<$T>>(),
                rule_record::<FwFromInt<$T>>(),
            )*
            $($(
                rule_record::<Zext<$Src, $Dst>>(),
                rule_record::<Sext<$Src, $Dst>>(),
            )*)*
        ];

        /// The dotted label + `TypeId` of every entry of the [`Builtins`]
        /// manifest, in the same order. Untrusted overlay — see
        /// [`NamedRule`].
        pub fn manifest_names() -> Vec<(String, TypeId)> {
            vec![
                $(name_of::<$S>(),)*
                $(
                    name_of::<FwAdd<$T>>(),
                    name_of::<FwSub<$T>>(),
                    name_of::<FwMul<$T>>(),
                    name_of::<FwDiv<$T>>(),
                    name_of::<FwRem<$T>>(),
                    name_of::<FwAnd<$T>>(),
                    name_of::<FwOr<$T>>(),
                    name_of::<FwXor<$T>>(),
                    name_of::<FwShl<$T>>(),
                    name_of::<FwShr<$T>>(),
                    name_of::<FwLt<$T>>(),
                    name_of::<FwLe<$T>>(),
                    name_of::<FwGt<$T>>(),
                    name_of::<FwGe<$T>>(),
                    name_of::<FwNeg<$T>>(),
                    name_of::<FwNot<$T>>(),
                    name_of::<FwToNat<$T>>(),
                    name_of::<FwToInt<$T>>(),
                    name_of::<FwFromNat<$T>>(),
                    name_of::<FwFromInt<$T>>(),
                )*
                $($(
                    name_of::<Zext<$Src, $Dst>>(),
                    name_of::<Sext<$Src, $Dst>>(),
                )*)*
            ]
        }
    };
}

builtins_manifest! {
    simple {
        NatSucc, NatPred, NatAdd, NatMul, NatSub, NatDiv, NatMod, NatPow, NatShl, NatShr,
        NatBitAnd, NatBitOr, NatBitXor, NatLe, NatLt,
        NatToInt, NatToBytesLe, NatToBytesBe, NatFromBytesLe, NatFromBytesBe,
        IntSucc, IntPred, IntNeg, IntAbs, IntSgn,
        IntAdd, IntMul, IntSub, IntDiv, IntMod, IntLe, IntLt,
        BytesCat, BytesConsNat, BytesLen, BytesAt, BytesSlice,
    }
    fw { u8, u16, u32, u64, i8, i16, i32, i64 }
    casts {
        u8  => [u8, u16, u32, u64, i8, i16, i32, i64];
        u16 => [u8, u16, u32, u64, i8, i16, i32, i64];
        u32 => [u8, u16, u32, u64, i8, i16, i32, i64];
        u64 => [u8, u16, u32, u64, i8, i16, i32, i64];
        i8  => [u8, u16, u32, u64, i8, i16, i32, i64];
        i16 => [u8, u16, u32, u64, i8, i16, i32, i64];
        i32 => [u8, u16, u32, u64, i8, i16, i32, i64];
        i64 => [u8, u16, u32, u64, i8, i16, i32, i64];
    }
}

/// The TCB manifest of [`Builtins`]: no parents, exactly the catalogue's
/// `RuleRecord`s admitted. A `pub const` so a language that **extends**
/// [`Builtins`] (e.g. `covalence-core`'s `CoreLang`, through the audited
/// core-on-pure seam) can embed this manifest *by value* as a parent in its
/// own static [`Manifest::extends`] list — keeping the combined tree
/// enumerable from one place.
pub const BUILTINS_MANIFEST: Manifest = Manifest {
    ty: TypeId::of::<Builtins>(),
    extends: &[],
    admits: BUILTINS_RULES,
    metadata: LangMeta,
};

/// The base language of native computation: a stateless (ZST) theory that
/// admits exactly the [`CanonRule`](covalence_pure::CanonRule)s in its static manifest — the
/// enumerable, diffable record of every native computation the kernel will
/// ever trust.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Builtins;

impl Language for Builtins {
    /// Flat membership test over the manifest's rule records — the
    /// manifest is the single source of truth (`admits(r) ⟺ r ∈ MANIFEST`).
    fn admits(&self, rule: TypeId) -> bool {
        BUILTINS_RULES.iter().any(|r| r.ty == rule)
    }

    /// `Builtins` extends nothing (only the implicit base `()`).
    fn extends(&self, _parent: TypeId) -> bool {
        false
    }

    /// Stateless: any two values are the same theory.
    fn union(self, _other: Self) -> Option<Self> {
        Some(self)
    }

    const MANIFEST: Option<&'static Manifest> = Some(&BUILTINS_MANIFEST);
}
