//! End-to-end demonstration that a consumer can build **terms and theorems**
//! entirely through the [`Hol`] + [`Nat`] trait API — no `covalence_core::Term`
//! / `TermKind` constructors, no `covalence_init::init::nat` accessors named
//! directly. This is the "minimal-porting" proof: everything below is written
//! against `H: Hol + Nat` and would carry over verbatim to any other backend
//! that implements the two traits.

use covalence_hol_api::{Hol, Nat, NativeHol};

/// A backend-generic derivation: from `⊢ ∀a b. a + b = b + a` (the `Nat`
/// backend's commutativity lemma) specialise both quantifiers to numerals and
/// conclude `⊢ m + n = n + m`, returning the theorem. Written purely against
/// the traits.
fn commute_numerals<H: Hol + Nat>(hol: &H, m: u64, n: u64) -> H::Thm {
    let comm = hol.add_comm().expect("add_comm");
    let lm = hol.lit(m);
    let ln = hol.lit(n);
    let step1 = hol.all_elim(comm, lm).expect("spec a");
    hol.all_elim(step1, ln).expect("spec b")
}

/// The specialised theorem's conclusion is exactly `m + n = n + m`, with both
/// sides built through [`Nat::add`] / [`Nat::lit`].
#[test]
fn add_comm_specialises_through_the_traits() {
    let hol = NativeHol;
    let thm = commute_numerals(&hol, 2, 3);

    let (lhs, rhs) = hol
        .dest_eq(&hol.concl(&thm))
        .expect("conclusion is an equation");

    let two = hol.lit(2);
    let three = hol.lit(3);
    let expect_lhs = hol.add(two.clone(), three.clone()).expect("2 + 3");
    let expect_rhs = hol.add(three, two).expect("3 + 2");

    assert_eq!(lhs, expect_lhs);
    assert_eq!(rhs, expect_rhs);
    assert!(hol.hyps(&thm).is_empty());
}

/// Build nat terms — `S 0` via [`Nat::succ`]/[`Nat::zero`] and a numeral via
/// [`Nat::lit`] — and specialise the `a + 0 = a` recursion equation to a
/// numeral, all through the trait surface. Exercises term builders + theorem
/// accessors + the generic `Hol` rules together.
#[test]
fn succ_and_add_agree_through_the_traits() {
    let hol = NativeHol;

    // `S 0` is `nat.succ` applied to `0`, well-typed, built via the traits.
    let s_zero = hol.succ(hol.zero()).expect("S 0");
    assert_eq!(hol.type_of(&s_zero).unwrap(), hol.nat_ty());
    // reflexivity closes over it — a genuine `⊢ S 0 = S 0`.
    let refl = hol.refl(s_zero.clone()).expect("refl");
    let (l, r) = hol.dest_eq(&hol.concl(&refl)).unwrap();
    assert_eq!(l, s_zero);
    assert_eq!(r, s_zero);

    // `⊢ ∀a. a + 0 = a`, specialise to the numeral `1`, get `⊢ 1 + 0 = 1`.
    let one = hol.lit(1);
    let add_zero = hol.add_zero().expect("add_zero");
    let at_one = hol.all_elim(add_zero, one.clone()).expect("spec add_zero");
    let (lhs, rhs) = hol.dest_eq(&hol.concl(&at_one)).unwrap();
    assert_eq!(lhs, hol.add(one.clone(), hol.zero()).unwrap());
    assert_eq!(rhs, one);
}

/// A tiny generic helper proving `⊢ x + 0 = x` for any variable name, purely
/// through the trait API — the kind of reusable lemma a migrated consumer
/// module writes.
fn add_zero_at<H: Hol + Nat>(hol: &H, name: &str) -> H::Thm {
    let x = hol.var(name, hol.nat_ty());
    let thm = hol.add_zero().expect("add_zero");
    hol.all_elim(thm, x).expect("spec")
}

#[test]
fn generic_helper_over_hol_nat() {
    let hol = NativeHol;
    let thm = add_zero_at(&hol, "k");
    let k = hol.var("k", hol.nat_ty());
    let (lhs, rhs) = hol.dest_eq(&hol.concl(&thm)).unwrap();
    assert_eq!(lhs, hol.add(k.clone(), hol.zero()).unwrap());
    assert_eq!(rhs, k);
    assert!(hol.hyps(&thm).is_empty());
}

mod narrow_capabilities {
    use covalence_hol_api::nat::{
        NatAdditiveLaws, NatArithmetic, NatFreeness, NatMultiplicativeLaws, NatOrder,
        NatRecursionLaws, NatSyntax,
    };
    use covalence_hol_api::{Hol, NativeHol};

    /// Construction-only consumers do not need to require any Peano laws.
    fn build_two<N: NatSyntax>(nat: &N) -> N::Term {
        nat.succ(nat.succ(nat.zero()).expect("first successor"))
            .expect("second successor")
    }

    /// Algebraic consumers can ask for just addition and its laws, without
    /// requiring multiplication laws, freeness, recursion, or a decision oracle.
    fn commute_two<N: NatAdditiveLaws>(nat: &N) -> N::Thm {
        let comm = nat.add_comm().expect("add_comm");
        let two = build_two(nat);
        let step = nat.all_elim(comm, two.clone()).expect("spec a");
        nat.all_elim(step, two).expect("spec b")
    }

    #[test]
    fn independently_usable() {
        let hol = NativeHol;
        let two = build_two(&hol);
        assert_eq!(hol.type_of(&two).unwrap(), NatSyntax::nat_ty(&hol));
        let two_lt_three = NatOrder::lt(&hol, two.clone(), NatSyntax::lit(&hol, 3)).expect("2 < 3");
        assert_eq!(hol.type_of(&two_lt_three).unwrap(), hol.bool_ty());
        assert!(hol.hyps(&commute_two(&hol)).is_empty());

        fn complete_native_capabilities<N>(_: &N)
        where
            N: NatArithmetic
                + NatOrder
                + NatFreeness
                + NatRecursionLaws
                + NatAdditiveLaws
                + NatMultiplicativeLaws,
        {
        }
        complete_native_capabilities(&hol);
    }
}

#[test]
fn native_nat_legacy_surface_forwards_to_logic_capabilities() {
    use covalence_hol_api::{
        NatArithmetic as LegacyArithmetic, NatSyntax as LegacySyntax, NativeHol,
        logic::nat::{NatArithmetic as LogicArithmetic, NatSyntax as LogicSyntax},
    };

    let hol = NativeHol;
    let legacy_two = LegacySyntax::lit(&hol, 2);
    let logic_two = LogicSyntax::nat_literal(&hol, 2);
    assert_eq!(legacy_two, logic_two);

    let legacy_four =
        LegacyArithmetic::add(&hol, legacy_two.clone(), legacy_two).expect("legacy addition");
    let logic_four =
        LogicArithmetic::nat_add(&hol, logic_two.clone(), logic_two).expect("logic addition");
    assert_eq!(legacy_four, logic_four);
}
