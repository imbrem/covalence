//! The literal-endgame **never-materialize** proof-of-mechanism (stage EG1;
//! design: `notes/vibes/literal-endgame-design.md`).
//!
//! Proves the additive `Thm<L, C>` mechanism end-to-end on `nat`: a
//! `core::Thm` whose conclusion mentions `toHOL(big_nat)` values that are
//! **never materialized** into a succ-tower (nor even into today's numeral
//! literal). The theorem's conclusion operand is the base expression
//! `NatAddEqE` — `nat.add (toHOL a) (toHOL b) = toHOL (a+b)` — with `a`, `b`,
//! `a+b` held as native `Nat` bignums under the uninterpreted `ToHolNat` op.
//!
//! The machine-checked guarantee (the point of the whole wave): the count of
//! materialized `Term` nodes in the symbolic conclusion is a fixed constant,
//! **independent of the magnitude of `a`/`b`** — the three naturals live as
//! native `Nat` leaves, not as `Term`s. So once the literal leaves are deleted
//! (stage EG5) and `toHOL n` denotes the succ-tower `Succ^n(Zero)`, this path
//! stays O(1) while eager materialization would be O(n).

use covalence_core::{Term, TermKind, Type, defs};
use covalence_hol_eval::{HolApp, ToHolNat, nat_add_thm, nat_add_thm_symbolic};
use covalence_pure::{App, Val};
use covalence_types::Nat;

/// Total `Term` node count. Walks only `App`/`Abs` spines (a numeral, whatever
/// its magnitude, is a single leaf here — the very property under test), so if
/// a value's succ-tower were ever materialized this count would explode with
/// the value. It never does.
fn term_nodes(t: &Term) -> usize {
    1 + match t.kind() {
        TermKind::App(f, x) => term_nodes(f) + term_nodes(x),
        TermKind::Abs(_, body) => term_nodes(body),
        _ => 0,
    }
}

/// Destructure the symbolic `NatAddEqE` conclusion into its three native `Nat`
/// leaves and its two materialized `Term` constant leaves (`nat.add`, `= at
/// nat`) — reading the base-expression structure directly, forcing nothing.
///
/// Shape (from `tohol_ops::nat_add_eq_expr`):
/// `((= (nat.add (toHOL a) (toHOL b))) (toHOL sum))`.
#[allow(clippy::type_complexity)]
fn destructure(concl: &covalence_hol_eval::NatAddEqE) -> (&Nat, &Nat, &Nat, &Term, &Term) {
    let App(HolApp, (eq_applied, tohol_sum)) = concl;
    let App(HolApp, (eq_op_leaf, lhs)) = eq_applied;
    let App(HolApp, (add_applied, tohol_b)) = lhs;
    let App(HolApp, (add_op_leaf, tohol_a)) = add_applied;
    let App(ToHolNat, Val(a_nat)) = tohol_a;
    let App(ToHolNat, Val(b_nat)) = tohol_b;
    let App(ToHolNat, Val(sum_nat)) = tohol_sum;
    (a_nat, b_nat, sum_nat, &eq_op_leaf.0, &add_op_leaf.0)
}

/// THE proof-of-mechanism: a symbolic theorem over an astronomically large
/// value keeps its three naturals as native `Nat`s and materializes only the
/// two fixed operator constants (`nat.add`, `= at nat`).
#[test]
fn nat_add_symbolic_never_materializes() {
    // A value whose succ-tower `Succ^a(Zero)` (post-EG5) would be physically
    // impossible to build: 2^128 - 1.
    let a = Nat::from(u128::MAX);
    let b = Nat::from(u128::MAX);
    let sum = a.clone() + b.clone();

    let thm = nat_add_thm_symbolic(a.clone(), b.clone())
        .expect("symbolic nat.add derivation of a huge value");

    assert!(
        thm.sym_hyps().is_empty(),
        "symbolic certificates are hypothesis-free"
    );

    let (a_nat, b_nat, sum_nat, eq_leaf, add_leaf) = destructure(thm.sym_concl());

    // (1) The three naturals live symbolically as NATIVE `Nat`s under `toHOL` —
    //     no `Term` numeral (let alone a succ-tower) is ever built for them.
    assert_eq!(a_nat, &a, "toHOL leaf a holds the native bignum");
    assert_eq!(b_nat, &b, "toHOL leaf b holds the native bignum");
    assert_eq!(
        sum_nat, &sum,
        "toHOL leaf sum holds a + b, computed natively"
    );

    // (2) The ONLY materialized `Term`s are the two fixed operator constants,
    //     each a single leaf independent of the input magnitude.
    assert_eq!(
        eq_leaf,
        &Term::eq_op(Type::nat()),
        "materialized `= at nat`"
    );
    assert_eq!(add_leaf, &defs::nat_add(), "materialized `nat.add`");
    assert_eq!(term_nodes(eq_leaf), 1, "`=` leaf is a single node");
    assert_eq!(term_nodes(add_leaf), 1, "`nat.add` leaf is a single node");
}

/// The never-materialize property is **magnitude-independent**: the symbolic
/// conclusion's materialized-`Term` footprint is identical for a tiny value and
/// an astronomically huge one. Were the succ-tower ever built, `term_nodes` of
/// the huge case would explode; it stays a fixed constant.
#[test]
fn symbolic_footprint_is_magnitude_independent() {
    let footprint = |a: Nat, b: Nat| -> usize {
        let thm = nat_add_thm_symbolic(a, b).expect("symbolic derivation");
        let (_, _, _, eq_leaf, add_leaf) = destructure(thm.sym_concl());
        term_nodes(eq_leaf) + term_nodes(add_leaf)
    };

    let small = footprint(Nat::from(2u32), Nat::from(3u32));
    let huge = footprint(Nat::from(u128::MAX), Nat::from(u128::MAX));

    assert_eq!(
        small, huge,
        "symbolic materialized-term footprint is a magnitude-independent constant"
    );
}

/// AUDIT HARDENING (medium: `from_pure_sym` drops `check_sequent`, so its
/// soundness rests on every IsThm-minting rule self-flooring to a well-typed
/// HOL-bool sequent). The symbolic lander [`nat_add_thm_symbolic`] and the
/// concrete lander [`nat_add_thm`] mint the SAME `NatAddCert`; the concrete one
/// lands via `from_pure` → `check_sequent`, the symbolic one via the
/// floor-skipping `from_pure_sym`. So the concrete lander SUCCEEDING for a given
/// input is a machine-checked witness that this cert's (reified) conclusion is a
/// well-typed HOL-bool sequent — i.e. the symbolic lander self-floors.
///
/// **EG2+ obligation:** every new symbolic lander MUST carry an analogous
/// floored witness (a concrete sibling that passes `check_sequent`, or an
/// equivalent well-typedness proof). This test pins the obligation for nat.add.
#[test]
fn nat_add_symbolic_lander_self_floors() {
    for (a, b) in [(2u32, 3u32), (0, 0), (255, 1), (1_000_000, 7)] {
        // Concrete sibling floors (check_sequent accepts a well-typed bool concl).
        nat_add_thm(a.into(), b.into())
            .expect("concrete NatAddCert lander passes the well-typedness floor");
        // Symbolic sibling lands the same cert without forcing.
        nat_add_thm_symbolic(a.into(), b.into()).expect("symbolic lander");
    }
}
