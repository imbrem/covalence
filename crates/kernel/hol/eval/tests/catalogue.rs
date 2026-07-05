//! Catalogue coverage: [`covalence_hol_eval::reduce`] decides exactly the
//! documented closed-form catalogue — every family, every fixed-width tag,
//! the 8×8 cast grid — and refuses everything else. The successor of the S5
//! differential suite (which pinned `reduce` against the now-deleted legacy
//! `Thm::reduce_*` kernel rule): shape/coverage is asserted here, exact
//! result values are pinned in `tests/audit_reduce.rs` (the S8 port of the
//! retired in-kernel audit suite) and in `covalence-pure-eval`'s own tests.

use covalence_core::seam::Lit;
use covalence_core::{IntTag, SmallIntLiteral, Term, Thm, defs};
use covalence_hol_eval::{delta, mk_blob, mk_int, mk_nat, prove_true, reduce, reduce_with};
use covalence_types::Nat;

fn nat(n: u64) -> Term {
    mk_nat(Nat::from(n))
}

fn int(n: i64) -> Term {
    mk_int(n as i128)
}

fn blob(bs: &[u8]) -> Term {
    mk_blob(bs.to_vec())
}

/// Canonically-encoded fixed-width literal from a signed value (mask to
/// width, sign-extend signed payloads — the kernel `store` convention).
fn sm(tag: IntTag, v: i128) -> Term {
    let w = tag.width();
    let m = if w >= 128 {
        u128::MAX
    } else {
        (1u128 << w) - 1
    };
    let low = (v as u128) & m;
    let bits = if tag.is_signed() && (low & (1u128 << (w - 1))) != 0 {
        (low | !m) as u64
    } else {
        low as u64
    };
    Term::small_int(SmallIntLiteral::new(tag, bits))
}

fn app1(f: Term, a: Term) -> Term {
    Term::app(f, a)
}

fn app2(f: Term, a: Term, b: Term) -> Term {
    Term::app(Term::app(f, a), b)
}

fn app3(f: Term, a: Term, b: Term, c: Term) -> Term {
    Term::app(Term::app(Term::app(f, a), b), c)
}

fn hol_eq(lhs: Term, rhs: Term) -> Term {
    let alpha = lhs.type_of().expect("eq lhs must be well-typed");
    Term::app(Term::app(Term::eq_op(alpha), lhs), rhs)
}

/// THE coverage assertion: `t` cert-reduces to a hypothesis-free equation
/// `⊢ t = v` with a closed literal `v`.
#[track_caller]
fn check_reduces(t: Term) {
    let thm = reduce(&t).unwrap_or_else(|| panic!("expected cert-reducible: {t}"));
    assert!(thm.hyps().is_empty(), "cert facts are hypothesis-free: {t}");
    let (lhs, rhs) = thm
        .concl()
        .as_eq()
        .unwrap_or_else(|| panic!("cert conclusion must be an equation: {t}"));
    assert_eq!(lhs, &t, "conclusion LHS must be the redex itself");
    assert!(
        Lit::from_term(rhs).is_some(),
        "conclusion RHS must be a closed literal: {t} = {rhs}"
    );
}

/// The negative twin: the driver must refuse `t`.
#[track_caller]
fn check_refuses(t: Term) {
    assert!(reduce(&t).is_none(), "expected cert-refusal: {t}");
}

// ============================================================================
// nat
// ============================================================================

#[test]
fn nat_family() {
    // succ (the kernel primitive) + pred saturation.
    check_reduces(app1(defs::nat_succ(), nat(0)));
    check_reduces(app1(defs::nat_succ(), nat(41)));
    check_reduces(app1(Term::succ(), nat(7)));
    check_reduces(app1(defs::nat_pred(), nat(0)));
    check_reduces(app1(defs::nat_pred(), nat(7)));

    for (a, b) in [(0u64, 0u64), (3, 4), (255, 1), (10, 0), (2, 5), (17, 5)] {
        check_reduces(app2(defs::nat_add(), nat(a), nat(b)));
        check_reduces(app2(defs::nat_mul(), nat(a), nat(b)));
        // Saturating subtraction; Euclidean div/mod with the FORCED
        // `n / 0 = 0`, `n mod 0 = n` conventions (values pinned in
        // tests/audit_reduce.rs).
        check_reduces(app2(defs::nat_sub(), nat(a), nat(b)));
        check_reduces(app2(defs::nat_div(), nat(a), nat(b)));
        check_reduces(app2(defs::nat_mod(), nat(a), nat(b)));
        check_reduces(app2(defs::nat_bit_and(), nat(a), nat(b)));
        check_reduces(app2(defs::nat_bit_or(), nat(a), nat(b)));
        check_reduces(app2(defs::nat_bit_xor(), nat(a), nat(b)));
        check_reduces(app2(defs::nat_le(), nat(a), nat(b)));
        check_reduces(app2(defs::nat_lt(), nat(a), nat(b)));
    }

    check_reduces(app2(defs::nat_pow(), nat(2), nat(10)));
    check_reduces(app2(defs::nat_pow(), nat(7), nat(0)));
    check_reduces(app2(defs::nat_shl(), nat(1), nat(4)));
    check_reduces(app2(defs::nat_shr(), nat(16), nat(2)));

    // Oversize pow exponent / left-shift amount on a non-zero operand: the
    // true result is unrepresentable, so the cert REFUSES (`None`) rather
    // than clamp/truncate. `nat.shr` is TOTAL (an over-usize shift is larger
    // than any bit-length ⇒ 0), and `0 << huge = 0` is total too.
    let huge = mk_nat(Nat::from(u64::MAX) + Nat::from(1u32));
    check_refuses(app2(defs::nat_pow(), nat(2), huge.clone()));
    check_refuses(app2(defs::nat_shl(), nat(1), huge.clone()));
    check_reduces(app2(defs::nat_shr(), nat(1), huge.clone()));
    check_reduces(app2(defs::nat_shl(), nat(0), huge));
}

// ============================================================================
// int
// ============================================================================

#[test]
fn int_family() {
    for v in [-9i64, -7, -1, 0, 1, 9, 12] {
        check_reduces(app1(defs::int_succ(), int(v)));
        check_reduces(app1(defs::int_pred(), int(v)));
        check_reduces(app1(defs::int_neg(), int(v)));
        check_reduces(app1(defs::int_abs(), int(v)));
        check_reduces(app1(defs::int_sgn(), int(v)));
    }
    for (a, b) in [
        (-3i64, 4i64),
        (3, 7),
        (-2, -3),
        (17, 5),
        (-17, 5),
        (17, -5),
        (10, 0),
        (-10, 0),
        (0, 0),
    ] {
        check_reduces(app2(defs::int_add(), int(a), int(b)));
        check_reduces(app2(defs::int_sub(), int(a), int(b)));
        check_reduces(app2(defs::int_mul(), int(a), int(b)));
        // Truncating division, remainder takes the dividend's sign, and the
        // FORCED `a / 0 = 0`, `a mod 0 = a` conventions.
        check_reduces(app2(defs::int_div(), int(a), int(b)));
        check_reduces(app2(defs::int_mod(), int(a), int(b)));
        check_reduces(app2(defs::int_le(), int(a), int(b)));
        check_reduces(app2(defs::int_lt(), int(a), int(b)));
    }
}

// ============================================================================
// nat ↔ int / bytes coercions
// ============================================================================

#[test]
fn coercion_family() {
    check_reduces(app1(defs::nat_to_int(), nat(0)));
    check_reduces(app1(defs::nat_to_int(), nat(42)));
    for v in [0u64, 1, 255, 256, 65_536] {
        check_reduces(app1(defs::nat_to_bytes_le(), nat(v)));
        check_reduces(app1(defs::nat_to_bytes_be(), nat(v)));
    }
    for bs in [&[][..], &[0][..], &[0, 1][..], &[1, 0][..], &[7, 8, 9][..]] {
        check_reduces(app1(defs::nat_from_bytes_le(), blob(bs)));
        check_reduces(app1(defs::nat_from_bytes_be(), blob(bs)));
    }
}

// ============================================================================
// bytes
// ============================================================================

#[test]
fn bytes_family() {
    check_reduces(app2(defs::bytes_cat(), blob(&[1, 2]), blob(&[3, 4, 5])));
    check_reduces(app2(defs::bytes_cat(), blob(&[]), blob(&[])));
    // consNat reduces the nat operand mod 256.
    check_reduces(app2(defs::bytes_cons_nat(), nat(257), blob(&[9])));
    check_reduces(app2(defs::bytes_cons_nat(), nat(65), blob(&[])));
    check_reduces(app1(defs::bytes_len(), blob(&[1, 2, 3])));
    check_reduces(app1(defs::bytes_len(), blob(&[])));
    // at: in-bounds and out-of-bounds (reads 0).
    check_reduces(app2(defs::bytes_at(), blob(&[7, 8, 9]), nat(1)));
    check_reduces(app2(defs::bytes_at(), blob(&[7, 8, 9]), nat(99)));
    // slice saturates.
    let bs = blob(&[10, 20, 30, 40, 50]);
    check_reduces(app3(defs::bytes_slice(), bs.clone(), nat(1), nat(3)));
    check_reduces(app3(defs::bytes_slice(), bs.clone(), nat(3), nat(100)));
    check_reduces(app3(defs::bytes_slice(), bs, nat(9), nat(1)));
}

// ============================================================================
// Fixed-width: the whole registry (8 tags × ops, the 8×8 cast grid)
// ============================================================================

#[test]
fn fixed_width_ops_all_tags() {
    use defs::IntOp::{self, *};
    const BIN: [IntOp; 10] = [Add, Sub, Mul, Div, Rem, And, Or, Xor, Shl, Shr];
    const CMP: [IntOp; 4] = [Lt, Le, Gt, Ge];
    const UN: [IntOp; 2] = [Neg, Not];

    let pairs: [(i128, i128); 8] = [
        (0, 0),
        (1, 2),
        (200, 100),
        (5, 8),
        (200, 7),
        (-7, 2),
        (-1, 1),
        (5, 0), // div/rem by zero: x / 0 = 0, x rem 0 = x (FORCED)
    ];

    for tag in IntTag::ALL {
        for op in BIN {
            for (a, b) in pairs {
                check_reduces(app2(defs::int_op(tag, op), sm(tag, a), sm(tag, b)));
            }
        }
        for op in CMP {
            for (a, b) in pairs {
                check_reduces(app2(defs::int_op(tag, op), sm(tag, a), sm(tag, b)));
            }
        }
        for op in UN {
            for v in [0i128, 1, -1, 200, 5] {
                check_reduces(app1(defs::int_op(tag, op), sm(tag, v)));
            }
        }
        // Mismatched operand tag: refuse.
        let other = if tag == IntTag::U8 {
            IntTag::U16
        } else {
            IntTag::U8
        };
        check_refuses(app2(defs::int_op(tag, Add), sm(tag, 1), sm(other, 1)));
    }
}

#[test]
fn fixed_width_conversions_all_tags() {
    for tag in IntTag::ALL {
        for v in [0i128, 1, -1, 200] {
            check_reduces(app1(defs::int_to_nat(tag), sm(tag, v)));
            check_reduces(app1(defs::int_to_int(tag), sm(tag, v)));
        }
        for n in [0u64, 1, 255, 300, 65_536] {
            check_reduces(app1(defs::int_from_nat(tag), nat(n)));
        }
        for z in [-300i64, -1, 0, 1, 255, 300] {
            check_reduces(app1(defs::int_from_int(tag), int(z)));
        }
    }
}

#[test]
fn fixed_width_cast_grid() {
    for src in IntTag::ALL {
        for dst in IntTag::ALL {
            for v in [0i128, 1, -1, 200, 0x1FF] {
                check_reduces(app1(defs::int_zext(src, dst), sm(src, v)));
                check_reduces(app1(defs::int_sext(src, dst), sm(src, v)));
            }
        }
    }
}

// ============================================================================
// Literal (dis)equality
// ============================================================================

#[test]
fn literal_equality_all_kinds() {
    // bool
    check_reduces(hol_eq(Term::bool_lit(true), Term::bool_lit(true)));
    check_reduces(hol_eq(Term::bool_lit(true), Term::bool_lit(false)));
    // nat
    check_reduces(hol_eq(nat(5), nat(5)));
    check_reduces(hol_eq(nat(0), nat(5)));
    // int
    check_reduces(hol_eq(int(-3), int(-3)));
    check_reduces(hol_eq(int(-3), int(3)));
    // fixed-width
    check_reduces(hol_eq(sm(IntTag::U8, 200), sm(IntTag::U8, 200)));
    check_reduces(hol_eq(sm(IntTag::U8, 200), sm(IntTag::U8, 201)));
    check_reduces(hol_eq(sm(IntTag::S64, -1), sm(IntTag::S64, -1)));
    // bytes
    check_reduces(hol_eq(blob(&[1, 2]), blob(&[1, 2])));
    check_reduces(hol_eq(blob(&[1, 2]), blob(&[3])));
    check_reduces(hol_eq(blob(&[]), blob(&[])));
}

// ============================================================================
// Refusals
// ============================================================================

#[test]
fn refusals() {
    // Partial application.
    check_refuses(defs::nat_add());
    check_refuses(app1(defs::nat_add(), nat(1)));
    // Over-application.
    check_refuses(app3(defs::nat_add(), nat(1), nat(2), nat(3)));
    // Open argument.
    check_refuses(app2(
        defs::nat_add(),
        nat(1),
        Term::free("x", covalence_core::Type::nat()),
    ));
    // Open literal equation.
    check_refuses(hol_eq(nat(5), Term::free("n", covalence_core::Type::nat())));
    // Wrong literal kind for the op.
    check_refuses(app2(defs::nat_add(), nat(1), int(1)));
    // A user-built spec that merely shares the label/type/body is a
    // different allocation — pointer-identity keying must refuse it.
    let canonical = defs::nat_add_spec();
    let fake = covalence_core::TermSpec::new_untrusted(
        "natAdd",
        canonical.ty().cloned(),
        canonical.tm().cloned(),
    );
    check_refuses(app2(Term::term_spec(fake, Vec::new()), nat(1), nat(2)));
    // A non-catalogue head.
    let nat_ty = covalence_core::Type::nat();
    check_refuses(app1(
        Term::const_("f", covalence_core::Type::fun(nat_ty.clone(), nat_ty)),
        nat(5),
    ));
}

// ============================================================================
// The rest of the surface: reduce_with / prove_true / delta
// ============================================================================

#[test]
fn reduce_with_interns_and_matches() {
    let mut cons = covalence_core::HashCons::<()>::new();
    let t = app2(defs::nat_add(), nat(3), nat(4));
    let via_cons = reduce_with(&t, &mut cons).expect("reduces");
    let plain = reduce(&t).expect("reduces");
    assert_eq!(via_cons.concl(), plain.concl());
}

#[test]
fn prove_true_decides_closed_goals() {
    // A comparison that computes to T.
    let goal = app2(defs::nat_le(), nat(3), nat(5));
    let thm = prove_true(&goal).expect("3 ≤ 5 proves");
    assert!(thm.hyps().is_empty());
    assert_eq!(thm.concl(), &goal);

    // A literal equation that computes to T.
    let goal = hol_eq(nat(4), nat(4));
    let thm = prove_true(&goal).expect("4 = 4 proves");
    assert_eq!(thm.concl(), &goal);

    // Computes to F: refuses.
    assert!(prove_true(&app2(defs::nat_le(), nat(7), nat(5))).is_err());
    // Not closed / not reducible: refuses.
    assert!(prove_true(&Term::free("p", covalence_core::Type::bool())).is_err());
}

#[test]
fn delta_passthrough_matches_unfold_term_spec() {
    // A let-style catalogue spec unfolds identically through the passthrough.
    let t = defs::nat_pred();
    let via_delta = delta(&t).expect("nat.pred unfolds");
    let via_kernel: Thm = Thm::unfold_term_spec(t).expect("nat.pred unfolds");
    assert_eq!(via_delta.concl(), via_kernel.concl());
}
