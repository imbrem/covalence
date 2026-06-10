//! Term-level int arithmetic / comparison / coercion.

use std::sync::LazyLock;

use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::spec::{TermSpec, TermSpecHandle};

fn int_bin_op(symbol: Canonical) -> TermSpecHandle {
    let int = Type::int();
    TermSpecHandle::new(TermSpec {
        symbol,
        ty: Some(Type::fun(int.clone(), Type::fun(int.clone(), int))),
        tm: None,
    })
}

fn int_cmp_op(symbol: Canonical) -> TermSpecHandle {
    let int = Type::int();
    TermSpecHandle::new(TermSpec {
        symbol,
        ty: Some(Type::fun(int.clone(), Type::fun(int, Type::bool()))),
        tm: None,
    })
}

static INT_ADD_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| int_bin_op(Canonical::IntAdd));
static INT_MUL_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| int_bin_op(Canonical::IntMul));
static INT_SUB_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| int_bin_op(Canonical::IntSub));
static INT_DIV_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| int_bin_op(Canonical::IntDiv));
static INT_MOD_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| int_bin_op(Canonical::IntMod));
static INT_LE_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| int_cmp_op(Canonical::IntLe));
static INT_LT_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| int_cmp_op(Canonical::IntLt));
static INT_NEG_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| {
    TermSpecHandle::new(TermSpec {
        symbol: Canonical::IntNeg,
        ty: Some(Type::fun(Type::int(), Type::int())),
        tm: None,
    })
});
static INT_ABS_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| {
    TermSpecHandle::new(TermSpec {
        symbol: Canonical::IntAbs,
        ty: Some(Type::fun(Type::int(), Type::nat())),
        tm: None,
    })
});
static INT_SGN_LAZY: LazyLock<TermSpecHandle> = LazyLock::new(|| {
    TermSpecHandle::new(TermSpec {
        symbol: Canonical::IntSgn,
        ty: Some(Type::fun(Type::int(), Type::int())),
        tm: None,
    })
});

/// `intAdd : int → int → int`.
pub fn int_add_spec() -> TermSpecHandle {
    INT_ADD_LAZY.clone()
}
pub fn int_add() -> Term {
    Term::term_spec(int_add_spec(), vec![])
}
/// `intMul : int → int → int`.
pub fn int_mul_spec() -> TermSpecHandle {
    INT_MUL_LAZY.clone()
}
pub fn int_mul() -> Term {
    Term::term_spec(int_mul_spec(), vec![])
}
/// `intSub : int → int → int`.
pub fn int_sub_spec() -> TermSpecHandle {
    INT_SUB_LAZY.clone()
}
pub fn int_sub() -> Term {
    Term::term_spec(int_sub_spec(), vec![])
}
/// `intDiv : int → int → int`.
pub fn int_div_spec() -> TermSpecHandle {
    INT_DIV_LAZY.clone()
}
pub fn int_div() -> Term {
    Term::term_spec(int_div_spec(), vec![])
}
/// `intMod : int → int → int`.
pub fn int_mod_spec() -> TermSpecHandle {
    INT_MOD_LAZY.clone()
}
pub fn int_mod() -> Term {
    Term::term_spec(int_mod_spec(), vec![])
}
/// `intLe : int → int → bool`.
pub fn int_le_spec() -> TermSpecHandle {
    INT_LE_LAZY.clone()
}
pub fn int_le() -> Term {
    Term::term_spec(int_le_spec(), vec![])
}
/// `intLt : int → int → bool`.
pub fn int_lt_spec() -> TermSpecHandle {
    INT_LT_LAZY.clone()
}
pub fn int_lt() -> Term {
    Term::term_spec(int_lt_spec(), vec![])
}
/// `intNeg : int → int`.
pub fn int_neg_spec() -> TermSpecHandle {
    INT_NEG_LAZY.clone()
}
pub fn int_neg() -> Term {
    Term::term_spec(int_neg_spec(), vec![])
}
/// `intAbs : int → nat`.
pub fn int_abs_spec() -> TermSpecHandle {
    INT_ABS_LAZY.clone()
}
pub fn int_abs() -> Term {
    Term::term_spec(int_abs_spec(), vec![])
}
/// `intSgn : int → int`.
pub fn int_sgn_spec() -> TermSpecHandle {
    INT_SGN_LAZY.clone()
}
pub fn int_sgn() -> Term {
    Term::term_spec(int_sgn_spec(), vec![])
}
