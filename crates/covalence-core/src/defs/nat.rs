//! Term-level nat arithmetic / comparison / coercion.

use std::sync::LazyLock;

use crate::term::Term;

use super::canonical::Canonical;
use super::sigs;
use super::spec::TermSpec;

fn nat_bin_op(symbol: Canonical) -> TermSpec {
    TermSpec::new(symbol, Some(sigs::nat_nat_to_nat()), None)
}

fn nat_cmp_op(symbol: Canonical) -> TermSpec {
    TermSpec::new(symbol, Some(sigs::nat_nat_to_bool()), None)
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

/// `natShl : nat → nat → nat` — left shift.
pub fn nat_shl_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| nat_bin_op(Canonical::NatShl));
    LAZY.clone()
}
pub fn nat_shl() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(nat_shl_spec(), vec![]));
    LAZY.clone()
}

/// `natShr : nat → nat → nat` — right shift.
pub fn nat_shr_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| nat_bin_op(Canonical::NatShr));
    LAZY.clone()
}
pub fn nat_shr() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(nat_shr_spec(), vec![]));
    LAZY.clone()
}

/// `natBitAnd : nat → nat → nat`.
pub fn nat_bit_and_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| nat_bin_op(Canonical::NatBitAnd));
    LAZY.clone()
}
pub fn nat_bit_and() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(nat_bit_and_spec(), vec![]));
    LAZY.clone()
}

/// `natBitOr : nat → nat → nat`.
pub fn nat_bit_or_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| nat_bin_op(Canonical::NatBitOr));
    LAZY.clone()
}
pub fn nat_bit_or() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(nat_bit_or_spec(), vec![]));
    LAZY.clone()
}

/// `natBitXor : nat → nat → nat`.
pub fn nat_bit_xor_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| nat_bin_op(Canonical::NatBitXor));
    LAZY.clone()
}
pub fn nat_bit_xor() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(nat_bit_xor_spec(), vec![]));
    LAZY.clone()
}

/// `natToBytesLe : nat → blob`.
pub fn nat_to_bytes_le_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        TermSpec::new(
            Canonical::NatToBytesLe,
            Some(sigs::nat_to_bytes()),
            None,
        )
    });
    LAZY.clone()
}
pub fn nat_to_bytes_le() -> Term {
    static LAZY: LazyLock<Term> =
        LazyLock::new(|| Term::term_spec(nat_to_bytes_le_spec(), vec![]));
    LAZY.clone()
}

/// `natToBytesBe : nat → blob`.
pub fn nat_to_bytes_be_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        TermSpec::new(
            Canonical::NatToBytesBe,
            Some(sigs::nat_to_bytes()),
            None,
        )
    });
    LAZY.clone()
}
pub fn nat_to_bytes_be() -> Term {
    static LAZY: LazyLock<Term> =
        LazyLock::new(|| Term::term_spec(nat_to_bytes_be_spec(), vec![]));
    LAZY.clone()
}

/// `natFromBytesLe : blob → nat`.
pub fn nat_from_bytes_le_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        TermSpec::new(
            Canonical::NatFromBytesLe,
            Some(sigs::bytes_to_nat()),
            None,
        )
    });
    LAZY.clone()
}
pub fn nat_from_bytes_le() -> Term {
    static LAZY: LazyLock<Term> =
        LazyLock::new(|| Term::term_spec(nat_from_bytes_le_spec(), vec![]));
    LAZY.clone()
}

/// `natFromBytesBe : blob → nat`.
pub fn nat_from_bytes_be_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        TermSpec::new(
            Canonical::NatFromBytesBe,
            Some(sigs::bytes_to_nat()),
            None,
        )
    });
    LAZY.clone()
}
pub fn nat_from_bytes_be() -> Term {
    static LAZY: LazyLock<Term> =
        LazyLock::new(|| Term::term_spec(nat_from_bytes_be_spec(), vec![]));
    LAZY.clone()
}

/// `natToInt : nat → int`.
pub fn nat_to_int_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        TermSpec::new(Canonical::NatToInt, Some(sigs::nat_to_int()), None)
    });
    LAZY.clone()
}
pub fn nat_to_int() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(nat_to_int_spec(), vec![]));
    LAZY.clone()
}
