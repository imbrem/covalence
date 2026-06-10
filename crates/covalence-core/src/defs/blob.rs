//! `blob := list u8`.

use std::sync::LazyLock;

use crate::term::Type;

use super::canonical::Canonical;
use super::spec::{TypeSpec, TypeSpecHandle};
use super::coprod::u8_ty;
use super::helpers::any;
use super::option::option;

static BLOB_LAZY: LazyLock<TypeSpecHandle> = LazyLock::new(|| {
    let carrier = Type::fun(Type::nat(), option(u8_ty()));
    let carrier_for_pred = carrier.clone();
    TypeSpecHandle::new(TypeSpec {
        symbol: Canonical::Blob,
        ty: Some(carrier),
        // TODO: eventually-none predicate at α := u8.
        tm: Some(any(&carrier_for_pred)),
    })
});

/// `blob := list u8`.
pub fn blob_spec() -> TypeSpecHandle {
    BLOB_LAZY.clone()
}
/// `blob` as a 0-ary Type.
pub fn blob_ty() -> Type {
    Type::spec(blob_spec(), vec![])
}
