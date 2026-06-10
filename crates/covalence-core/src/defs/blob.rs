//! `blob := list u8`.

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
