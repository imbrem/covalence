//! `bytes := list u8` — the TYPE of `TermKind::Blob` literals.
//!
//! D3 residue: only the type spec lives here (a `Blob` literal's
//! `type_of` returns it). The bytes *operations* (`bytesCat`,
//! `bytesConsNat`, `bytesLen`, `bytesAt`, `bytesSlice`) moved to the
//! untrusted catalogue in `covalence-hol-eval::defs::blob`.

use std::sync::LazyLock;

use super::bits::u8_ty;
use super::canonical::Canonical;
use super::list::list;
use super::spec::TypeSpec;

/// `bytes := list u8` — the type of `TermKind::Blob` literals.
/// Derived TypeSpec (Canonical::Bytes); was the kernel-primitive
/// `TypeKind::Bytes` before the spec migration.
pub fn bytes_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> = LazyLock::new(|| {
        let carrier = list(u8_ty());
        TypeSpec::newtype(Canonical::Bytes, carrier)
    });
    LAZY.clone()
}
