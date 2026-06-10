//! `stream 'a := nat → 'a`.

use std::sync::LazyLock;

use crate::term::Type;

use super::canonical::Canonical;
use super::helpers::any;
use super::spec::TypeSpec;

/// `stream 'a := nat → 'a`.
pub fn stream_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let carrier = Type::fun(Type::nat(), alpha);
        TypeSpec::new(Canonical::Stream, Some(carrier.clone()), Some(any(&carrier)))
    });
    LAZY.clone()
}
/// `stream α`.
pub fn stream(alpha: Type) -> Type {
    Type::spec(stream_spec(), vec![alpha])
}
