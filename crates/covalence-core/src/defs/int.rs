//! Term-level int arithmetic / comparison / coercion.
//!
//! NOTE: In the long run `int` itself should be a derived **type**
//! (a `TypeSpec` built from `nat` via `signed1`/`signed2` or
//! `fieldOfFractions`), not a primitive `Type::int()`. For now the
//! term specs continue to use `Type::int()` as a placeholder until
//! the type-level derivation lands.

use std::sync::LazyLock;

use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::spec::TermSpec;

fn int_bin_op(symbol: Canonical) -> TermSpec {
    let int = Type::int();
    TermSpec::new(
        symbol,
        Some(Type::fun(int.clone(), Type::fun(int.clone(), int))),
        None,
    )
}

fn int_cmp_op(symbol: Canonical) -> TermSpec {
    let int = Type::int();
    TermSpec::new(
        symbol,
        Some(Type::fun(int.clone(), Type::fun(int, Type::bool()))),
        None,
    )
}

/// `intAdd : int → int → int`.
pub fn int_add_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| int_bin_op(Canonical::IntAdd));
    LAZY.clone()
}
pub fn int_add() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(int_add_spec(), vec![]));
    LAZY.clone()
}

/// `intMul : int → int → int`.
pub fn int_mul_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| int_bin_op(Canonical::IntMul));
    LAZY.clone()
}
pub fn int_mul() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(int_mul_spec(), vec![]));
    LAZY.clone()
}

/// `intSub : int → int → int`.
pub fn int_sub_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| int_bin_op(Canonical::IntSub));
    LAZY.clone()
}
pub fn int_sub() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(int_sub_spec(), vec![]));
    LAZY.clone()
}

/// `intDiv : int → int → int`.
pub fn int_div_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| int_bin_op(Canonical::IntDiv));
    LAZY.clone()
}
pub fn int_div() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(int_div_spec(), vec![]));
    LAZY.clone()
}

/// `intMod : int → int → int`.
pub fn int_mod_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| int_bin_op(Canonical::IntMod));
    LAZY.clone()
}
pub fn int_mod() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(int_mod_spec(), vec![]));
    LAZY.clone()
}

/// `intLe : int → int → bool`.
pub fn int_le_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| int_cmp_op(Canonical::IntLe));
    LAZY.clone()
}
pub fn int_le() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(int_le_spec(), vec![]));
    LAZY.clone()
}

/// `intLt : int → int → bool`.
pub fn int_lt_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| int_cmp_op(Canonical::IntLt));
    LAZY.clone()
}
pub fn int_lt() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(int_lt_spec(), vec![]));
    LAZY.clone()
}

/// `intNeg : int → int`.
pub fn int_neg_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        TermSpec::new(
            Canonical::IntNeg,
            Some(Type::fun(Type::int(), Type::int())),
            None,
        )
    });
    LAZY.clone()
}
pub fn int_neg() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(int_neg_spec(), vec![]));
    LAZY.clone()
}

/// `intAbs : int → nat`.
pub fn int_abs_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        TermSpec::new(
            Canonical::IntAbs,
            Some(Type::fun(Type::int(), Type::nat())),
            None,
        )
    });
    LAZY.clone()
}
pub fn int_abs() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(int_abs_spec(), vec![]));
    LAZY.clone()
}

/// `intSgn : int → int`.
pub fn int_sgn_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        TermSpec::new(
            Canonical::IntSgn,
            Some(Type::fun(Type::int(), Type::int())),
            None,
        )
    });
    LAZY.clone()
}
pub fn int_sgn() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(int_sgn_spec(), vec![]));
    LAZY.clone()
}
