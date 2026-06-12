//! `blob := list u8`, plus the bytes-operations TermSpec constants
//! `bytesCat`, `bytesConsNat`, `bytesLen`, `bytesAt`, `bytesSlice`.

use std::sync::LazyLock;

use crate::term::Type;

use super::canonical::Canonical;
use super::coprod::u8_ty;
use super::helpers::any;
use super::list::list;
use super::spec::TypeSpec;

/// `blob := list u8`.
pub fn blob_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> = LazyLock::new(|| {
        let carrier = list(u8_ty());
        TypeSpec::new(Canonical::Blob, Some(carrier.clone()), Some(any(&carrier)))
    });
    LAZY.clone()
}
/// `blob` as a 0-ary Type.
pub fn blob_ty() -> Type {
    static LAZY: LazyLock<Type> = LazyLock::new(|| list(u8_ty()));
    LAZY.clone()
}

// ---- Bytes operations as TermSpec constants ----

fn bytes_bin_op_ty() -> Type {
    Type::fun(Type::bytes(), Type::fun(Type::bytes(), Type::bytes()))
}

term_decl! {
    /// `bytesCat : bytes → bytes → bytes` — concatenation. Closed
    /// forms reduce via `builtins::reduce_spec`.
    bytes_cat_spec, bytes_cat, Canonical::BytesCat, bytes_bin_op_ty()
}

term_decl! {
    /// `bytesConsNat : nat → bytes → bytes` — cons a nat (mod 256)
    /// onto the front of a bytes value.
    bytes_cons_nat_spec, bytes_cons_nat, Canonical::BytesConsNat,
    Type::fun(Type::nat(), Type::fun(Type::bytes(), Type::bytes()))
}

term_decl! {
    /// `bytesLen : bytes → nat`.
    bytes_len_spec, bytes_len, Canonical::BytesLen,
    Type::fun(Type::bytes(), Type::nat())
}

term_decl! {
    /// `bytesAt : bytes → nat → nat` — byte at index, 0 if OOB.
    bytes_at_spec, bytes_at, Canonical::BytesAt,
    Type::fun(Type::bytes(), Type::fun(Type::nat(), Type::nat()))
}

term_decl! {
    /// `bytesSlice : bytes → nat → nat → bytes` — saturating slice.
    bytes_slice_spec, bytes_slice, Canonical::BytesSlice,
    Type::fun(
        Type::bytes(),
        Type::fun(Type::nat(), Type::fun(Type::nat(), Type::bytes())),
    )
}
