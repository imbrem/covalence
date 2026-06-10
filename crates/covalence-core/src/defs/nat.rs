//! Term-level nat arithmetic / comparison / coercion.

use std::sync::LazyLock;

use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::spec::{TermSpec, TermSpecHandle};

fn nat_bin_op(symbol: Canonical) -> TermSpecHandle {
    let nat = Type::nat();
    TermSpecHandle::new(TermSpec {
        symbol,
        ty: Some(Type::fun(nat.clone(), Type::fun(nat.clone(), nat))),
        tm: None,
    })
}

fn nat_cmp_op(symbol: Canonical) -> TermSpecHandle {
    let nat = Type::nat();
    TermSpecHandle::new(TermSpec {
        symbol,
        ty: Some(Type::fun(nat.clone(), Type::fun(nat, Type::bool()))),
        tm: None,
    })
}

static NAT_ADD_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| nat_bin_op(Canonical::NatAdd));
static NAT_MUL_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| nat_bin_op(Canonical::NatMul));
static NAT_SUB_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| nat_bin_op(Canonical::NatSub));
static NAT_DIV_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| nat_bin_op(Canonical::NatDiv));
static NAT_MOD_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| nat_bin_op(Canonical::NatMod));
static NAT_POW_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| nat_bin_op(Canonical::NatPow));
static NAT_LE_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| nat_cmp_op(Canonical::NatLe));
static NAT_LT_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| nat_cmp_op(Canonical::NatLt));
static NAT_TO_INT_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| {
    TermSpecHandle::new(TermSpec {
        symbol: Canonical::NatToInt,
        ty: Some(Type::fun(Type::nat(), Type::int())),
        tm: None,
    })
});

/// `natAdd : nat → nat → nat`.
pub fn nat_add_spec() -> TermSpecHandle {
    NAT_ADD_LAZY.clone()
}
pub fn nat_add() -> Term {
    Term::term_spec(nat_add_spec(), vec![])
}
/// `natMul : nat → nat → nat`.
pub fn nat_mul_spec() -> TermSpecHandle {
    NAT_MUL_LAZY.clone()
}
pub fn nat_mul() -> Term {
    Term::term_spec(nat_mul_spec(), vec![])
}
/// `natSub : nat → nat → nat` (saturating).
pub fn nat_sub_spec() -> TermSpecHandle {
    NAT_SUB_LAZY.clone()
}
pub fn nat_sub() -> Term {
    Term::term_spec(nat_sub_spec(), vec![])
}
/// `natDiv : nat → nat → nat` (Euclidean).
pub fn nat_div_spec() -> TermSpecHandle {
    NAT_DIV_LAZY.clone()
}
pub fn nat_div() -> Term {
    Term::term_spec(nat_div_spec(), vec![])
}
/// `natMod : nat → nat → nat` (Euclidean).
pub fn nat_mod_spec() -> TermSpecHandle {
    NAT_MOD_LAZY.clone()
}
pub fn nat_mod() -> Term {
    Term::term_spec(nat_mod_spec(), vec![])
}
/// `natPow : nat → nat → nat`.
pub fn nat_pow_spec() -> TermSpecHandle {
    NAT_POW_LAZY.clone()
}
pub fn nat_pow() -> Term {
    Term::term_spec(nat_pow_spec(), vec![])
}
/// `natLe : nat → nat → bool`.
pub fn nat_le_spec() -> TermSpecHandle {
    NAT_LE_LAZY.clone()
}
pub fn nat_le() -> Term {
    Term::term_spec(nat_le_spec(), vec![])
}
/// `natLt : nat → nat → bool`.
pub fn nat_lt_spec() -> TermSpecHandle {
    NAT_LT_LAZY.clone()
}
pub fn nat_lt() -> Term {
    Term::term_spec(nat_lt_spec(), vec![])
}
/// `natToInt : nat → int`.
pub fn nat_to_int_spec() -> TermSpecHandle {
    NAT_TO_INT_LAZY.clone()
}
pub fn nat_to_int() -> Term {
    Term::term_spec(nat_to_int_spec(), vec![])
}
