//! `real` — placeholder for Dedekind cuts of rationals.

use std::sync::LazyLock;

use crate::term::Type;

use super::canonical::Canonical;
use super::helpers::any;
use super::rat::rat_ty;
use super::spec::TypeSpec;

/// `real` — placeholder; will become `{ rat } close ratLe`.
pub fn real_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> = LazyLock::new(|| {
        let rat = rat_ty();
        let carrier = Type::fun(rat, Type::bool());
        TypeSpec::new(Canonical::Real, Some(carrier.clone()), Some(any(&carrier)))
    });
    LAZY.clone()
}
/// `real` as a 0-ary Type.
pub fn real_ty() -> Type {
    static LAZY: LazyLock<Type> = LazyLock::new(|| Type::spec(real_spec(), vec![]));
    LAZY.clone()
}
