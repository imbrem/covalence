//! The `defs/` **D3 residue** — the structural TYPE catalogue the
//! literal leaves force into core, plus the spec machinery.
//!
//! The term-op catalogue (nat/int/fixed-width/bytes arithmetic, the
//! `fun`/`set`/`rel`/`rat`/`text`/`floats`/`result` families, the
//! higher-order `list` ops, the `.cov` bootstrap) **moved to
//! `covalence-hol-eval::defs`** (stage E2 of
//! `notes/vibes/handoff/defs-out-of-core.md`), which re-exports this
//! module flatly — downstream code imports the catalogue from there.
//!
//! ## What stays here, and why
//!
//! The literal `TermKind` variants (`Nat`/`Int`/`SmallInt`/`Blob`) need
//! their TYPES from `type_of`, so the type specs and their carrier
//! closure stay: `bits` (`u8`…`s512`) → `list` → `option`/`stream` →
//! `coprod`/`unit`/`fail`; `bytes := list u8`; `int := (nat × nat)/~`
//! (whose relation needs `prod` + `nat.add`); and the term ops those
//! type BODIES mention (`nat.{succ,pred,add,le,lt,rec}`, `iter`, `nil`,
//! `cons`, `listFoldr`, `listLength`, `finite`, the stream accessors,
//! `cond`) together with the `logic` connectives they quantify with.
//! This residue is a recorded skeleton (the generated open-work index): it dies with
//! the literal leaves when the lazy toHOL base expressions land.
//!
//! ## Trust status
//!
//! Code here is *semi-trusted*: a bug cannot forge a `Thm` (the
//! `Thm`-constructing rules live in `crate::thm`), and since stage E2
//! the computation certificates live in `covalence-hol-eval` — so a
//! wrong residue definition here can no longer be recognized by an
//! in-TCB dispatch table. What remains load-bearing is that the type
//! specs mean what the literal semantics assume (e.g. `int`'s quotient
//! relation really is the Grothendieck relation).
//!
//! ## Definitions
//!
//! A `TermSpec` has an optional definition body (`tm`): `let_term!` (a
//! let-style lambda body) or `spec_term!` (a def-style Hilbert-ε
//! selector predicate). Everything residual is *defined* (no
//! declaration-only stubs remain in core; those moved with the
//! catalogue). The definition does not affect efficiency: closed
//! literal computation goes through the eval-tier certificate path,
//! independent of `tm`.

#[macro_use]
mod macros;

mod bits;
mod blob;
mod canonical;
mod cond;
mod coprod;
mod fail;
mod int;
mod list;
pub(crate) mod logic;
mod nat;
mod option;
mod prod;
mod quotient;
pub mod sigs;
mod spec;
mod stream;
pub(crate) mod symbol;
mod unit;

pub use bits::{
    bit_spec, bit_ty, bits_len, bits_len_spec, bits_spec, bits_ty, s1_spec, s1_ty, s2_spec, s2_ty,
    s4_spec, s4_ty, s8_spec, s8_ty, s16_spec, s16_ty, s32_spec, s32_ty, s64_spec, s64_ty,
    s128_spec, s128_ty, s256_spec, s256_ty, s512_spec, s512_ty, u2_spec, u2_ty, u4_spec, u4_ty,
    u8_spec, u8_ty, u16_spec, u16_ty, u32_spec, u32_ty, u64_spec, u64_ty, u128_spec, u128_ty,
    u256_spec, u256_ty, u512_spec, u512_ty,
};
pub use blob::bytes_spec;
pub use canonical::Canonical;
pub use cond::{cond, cond_spec};
pub use coprod::{
    coprod, coprod_case, coprod_case_spec, coprod_spec, inl, inl_spec, inr, inr_spec,
};
pub use fail::{fail, fail_spec};
pub use int::int_ty_spec;
pub use list::{
    cons, cons_spec, list, list_foldr, list_foldr_spec, list_length, list_length_spec, list_spec,
    nil, nil_spec,
};
pub use logic::{
    and, and_spec, exists, exists_spec, fal, fal_spec, forall, forall_spec, iff, iff_spec, imp,
    imp_spec, not, not_spec, or, or_spec, tru, tru_spec,
};
pub use nat::{
    iter, iter_spec, nat_add, nat_add_spec, nat_le, nat_le_spec, nat_lt, nat_lt_spec, nat_pred,
    nat_pred_spec, nat_rec, nat_rec_spec, nat_succ,
};
pub use option::{
    is_some, is_some_spec, none, none_spec, option, option_case, option_case_spec, option_spec,
    some, some_spec, unwrap, unwrap_spec,
};
pub use prod::{
    fst, fst_spec, pair, pair_spec, prod, prod_spec, signed1, signed1_spec, signed2, signed2_spec,
    snd, snd_spec,
};
pub use spec::{TermSpec, TypeSpec};
pub use stream::{
    finite, finite_spec, stream, stream_at, stream_at_spec, stream_const, stream_const_spec,
    stream_head, stream_head_spec, stream_mk, stream_mk_spec, stream_spec, stream_tail,
    stream_tail_spec,
};
pub use symbol::{Symbol, SymbolRef, TrustedCmp, TrustedSymbol};
pub use unit::{unit_nil, unit_nil_spec, unit_spec};

#[cfg(test)]
mod tests {
    use super::*;

    // The bulk of the catalogue round-trip tests moved with the term
    // catalogue to `covalence-hol-eval::defs` (stage E2). Only the
    // machinery test needing the crate-private `TypeSpec::raw` stays.
    #[test]
    fn typespec_construction_round_trips() {
        let spec = TypeSpec::raw(
            Canonical::Set,
            Some(crate::ty::Type::fun(
                crate::ty::Type::tfree("a"),
                crate::ty::Type::bool(),
            )),
            None,
        );
        assert_eq!(spec.symbol().label(), "set");
        assert!(spec.ty().is_some());
        assert!(spec.tm().is_none());
    }
}
