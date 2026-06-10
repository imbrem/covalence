//! Term-level nat arithmetic / comparison / coercion.

use std::sync::LazyLock;

use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::spec::TermSpec;

fn nat_bin_op(symbol: Canonical) -> TermSpec {
    let nat = Type::nat();
    TermSpec::new(
        symbol,
        Some(Type::fun(nat.clone(), Type::fun(nat.clone(), nat))),
        None,
    )
}

fn nat_cmp_op(symbol: Canonical) -> TermSpec {
    let nat = Type::nat();
    TermSpec::new(
        symbol,
        Some(Type::fun(nat.clone(), Type::fun(nat, Type::bool()))),
        None,
    )
}

/// `natAdd : nat → nat → nat`.
pub fn nat_add_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| nat_bin_op(Canonical::NatAdd));
    LAZY.clone()
}
pub fn nat_add() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(nat_add_spec(), vec![]));
    LAZY.clone()
}

/// `natMul : nat → nat → nat`.
pub fn nat_mul_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| nat_bin_op(Canonical::NatMul));
    LAZY.clone()
}
pub fn nat_mul() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(nat_mul_spec(), vec![]));
    LAZY.clone()
}

/// `natSub : nat → nat → nat` (saturating).
pub fn nat_sub_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| nat_bin_op(Canonical::NatSub));
    LAZY.clone()
}
pub fn nat_sub() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(nat_sub_spec(), vec![]));
    LAZY.clone()
}

/// `natDiv : nat → nat → nat` (Euclidean).
pub fn nat_div_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| nat_bin_op(Canonical::NatDiv));
    LAZY.clone()
}
pub fn nat_div() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(nat_div_spec(), vec![]));
    LAZY.clone()
}

/// `natMod : nat → nat → nat` (Euclidean).
pub fn nat_mod_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| nat_bin_op(Canonical::NatMod));
    LAZY.clone()
}
pub fn nat_mod() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(nat_mod_spec(), vec![]));
    LAZY.clone()
}

/// `natPow : nat → nat → nat`.
pub fn nat_pow_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| nat_bin_op(Canonical::NatPow));
    LAZY.clone()
}
pub fn nat_pow() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(nat_pow_spec(), vec![]));
    LAZY.clone()
}

/// `natLe : nat → nat → bool`.
pub fn nat_le_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| nat_cmp_op(Canonical::NatLe));
    LAZY.clone()
}
pub fn nat_le() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(nat_le_spec(), vec![]));
    LAZY.clone()
}

/// `natLt : nat → nat → bool`.
pub fn nat_lt_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| nat_cmp_op(Canonical::NatLt));
    LAZY.clone()
}
pub fn nat_lt() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(nat_lt_spec(), vec![]));
    LAZY.clone()
}

/// `natToInt : nat → int`.
pub fn nat_to_int_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        TermSpec::new(
            Canonical::NatToInt,
            Some(Type::fun(Type::nat(), Type::int())),
            None,
        )
    });
    LAZY.clone()
}
pub fn nat_to_int() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(nat_to_int_spec(), vec![]));
    LAZY.clone()
}
