//! `stream 'a := nat → 'a`.

use std::sync::LazyLock;

use crate::term::Type;

use super::canonical::Canonical;
use super::spec::{TypeSpec, TypeSpecHandle};
use super::helpers::any;

static STREAM_LAZY: LazyLock<TypeSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    let carrier = Type::fun(Type::nat(), alpha);
    TypeSpecHandle::new(TypeSpec {
        symbol: Canonical::Stream,
        ty: Some(carrier.clone()),
        tm: Some(any(&carrier)),
    })
});

/// `stream 'a := nat → 'a`.
pub fn stream_spec() -> TypeSpecHandle {
    STREAM_LAZY.clone()
}
/// `stream α`.
pub fn stream(alpha: Type) -> Type {
    Type::spec(stream_spec(), vec![alpha])
}
