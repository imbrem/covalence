//! `real := { rat } close ratLe` — Dedekind cuts of the rationals.
//!
//! A real is a non-empty subset of `rat` that's closed under
//! `ratLe`. Concretely the selector predicate built by
//! `close_spec` is:
//!
//! ```text
//!     λS:rat→bool. (∀x y. ratLe x y ⟹ S x ⟹ S y) ∧ (∃x. S x)
//! ```
//!
//! With `ratLe x y` meaning `x ≤ y`, this says "S is upward closed
//! under `≤` and non-empty" — i.e. `S` is an *upper Dedekind cut*.
//! (The dual *lower* cut and the upper cut both define the reals;
//! we follow the convention `close ratLe` from the type-hierarchy
//! design doc.)
//!
//! `ratLe` is declaration-only — it lives in `defs/rat.rs`. Once
//! the rationals get a concrete construction, `ratLe` becomes a
//! proved definition; for now it's a kernel-axiomatised constant.

use std::sync::LazyLock;

use crate::term::Type;

use super::canonical::Canonical;
use super::rat::{rat_le, rat_ty};
use super::spec::TypeSpec;

/// `real := close rat ratLe` — Dedekind cuts. Carrier is `rat → bool`;
/// selector predicate enforces upward closure under `ratLe` plus
/// non-emptiness.
pub fn real_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> = LazyLock::new(|| {
        TypeSpec::close(Canonical::Real, rat_ty(), rat_le())
    });
    LAZY.clone()
}
/// `real` as a 0-ary Type.
pub fn real_ty() -> Type {
    static LAZY: LazyLock<Type> = LazyLock::new(|| Type::spec(real_spec(), vec![]));
    LAZY.clone()
}
