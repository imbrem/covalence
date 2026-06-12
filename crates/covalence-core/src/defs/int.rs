//! `int := signed2 nat` type spec, plus term-level int arithmetic /
//! comparison / coercion.

use std::sync::LazyLock;

use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::helpers::any;
use super::prod::signed2;
use super::sigs;
use super::spec::{TermSpec, TypeSpec};

// ============================================================================
// `int` as a derived TypeSpec
// ============================================================================

/// `int := signed2 nat` — the type of integer literals
/// (`TermKind::Int`). Derived TypeSpec (Canonical::Int); was the
/// kernel-primitive `TypeKind::Int` before the spec migration.
pub fn int_ty_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> = LazyLock::new(|| {
        let carrier = signed2(Type::nat());
        TypeSpec::new(Canonical::Int, Some(carrier.clone()), Some(any(&carrier)))
    });
    LAZY.clone()
}

fn int_bin_op(symbol: Canonical) -> TermSpec {
    TermSpec::new(symbol, Some(sigs::int_int_to_int()), None)
}

fn int_cmp_op(symbol: Canonical) -> TermSpec {
    TermSpec::new(symbol, Some(sigs::int_int_to_bool()), None)
}

// ============================================================================
// intSucc / intPred — TermSpec constants over int. `builtins::reduce_spec`
// matches on them for closed-form reduction.
// ============================================================================

term_decl! {
    /// `intSucc : int → int` — `λz. z + 1`. Reduces on literals via
    /// `builtins::reduce_spec`.
    int_succ_spec, int_succ, Canonical::IntSucc, sigs::int_to_int()
}

term_decl! {
    /// `intPred : int → int` — `λz. z − 1`.
    int_pred_spec, int_pred, Canonical::IntPred, sigs::int_to_int()
}

/// `0 : int` — the canonical integer-zero literal. Reused by
/// `nat_to_int`'s definitional body and downstream proofs.
pub fn int_zero() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::int_lit(covalence_types::Int::zero()));
    LAZY.clone()
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
            Some(sigs::int_to_int()),
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
            Some(sigs::int_to_nat()),
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
            Some(sigs::int_to_int()),
            None,
        )
    });
    LAZY.clone()
}
pub fn int_sgn() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(int_sgn_spec(), vec![]));
    LAZY.clone()
}
