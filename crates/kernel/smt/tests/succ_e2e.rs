//! End-to-end: the SAME infeasible bound chain the eval path refutes
//! (`5 ≤ x ∧ x ≤ y ∧ y ≤ 2 ⟹ ⊥`), replayed by [`refute_chain`] over the
//! **eval-TCB-free** `succ`-tower `nat` backend.
//!
//! This is the payoff of parameterising the [`Discharger`]: `refute_chain` is
//! generic over the order carrier `L` AND the closed-comparison discharger `D`,
//! so swapping `(NativeHol, EvalDischarger)` for `(SuccHol, SuccDischarger)`
//! reuses the *entire* chain-composition machinery and closes the terminal
//! `5 ≤ 2` by pure induction — no `covalence-hol-eval` computation cert.

use covalence_hol_api::{Discharger, Hol, LinOrder, Strict, SuccDischarger, SuccHol};
use covalence_kernel_smt::{Edge, refute_chain};

/// `⊢ ⊥` proves an arbitrary goal — the refutation is genuine falsity.
fn assert_is_falsity(l: &SuccHol, bot: <SuccHol as Hol>::Thm) {
    let q = l.var("q_goal", l.bool_ty());
    let anything = l.false_elim(bot, q.clone()).expect("⊥ proves anything");
    assert_eq!(l.concl(&anything), q, "the refutation is genuine falsity");
}

fn le_edge(l: &SuccHol, a: &<SuccHol as Hol>::Term, b: &<SuccHol as Hol>::Term) -> Edge<SuccHol> {
    let atom = LinOrder::le(l, a.clone(), b.clone()).expect("build a ≤ b");
    Edge::new(
        a.clone(),
        b.clone(),
        l.assume(atom).expect("assume"),
        Strict::Le,
    )
}

/// `5 ≤ x ∧ x ≤ y ∧ y ≤ 2 ⟹ ⊥` — the terminal `5 ≤ 2` is a false comparison
/// of `succ`-tower literals, discharged by `SuccDischarger` by pure induction.
#[test]
fn bound_chain_closes_on_succ_literal_no_eval() {
    let l = SuccHol;
    let d = SuccDischarger;
    let nat_ty = l.type_of(&d.lit(&l, 0)).expect("nat type of literal");

    let x = l.var("x", nat_ty.clone());
    let y = l.var("y", nat_ty);
    let five = d.lit(&l, 5);
    let two = d.lit(&l, 2);

    let edges = [
        le_edge(&l, &five, &x),
        le_edge(&l, &x, &y),
        le_edge(&l, &y, &two),
    ];
    let bot = refute_chain(&l, &d, &edges).expect("succ-tower refutation");
    assert_eq!(l.hyps(&bot).len(), 3, "the three assumed bounds remain");
    assert_is_falsity(&l, bot);
}

/// A satisfiable bound chain `2 ≤ x ∧ x ≤ 5` must NOT refute — `SuccDischarger`
/// fails on the true comparison `2 ≤ 5`, so no `⊢ ⊥` is minted.
#[test]
fn satisfiable_succ_chain_does_not_refute() {
    let l = SuccHol;
    let d = SuccDischarger;
    let nat_ty = l.type_of(&d.lit(&l, 0)).expect("nat type");
    let x = l.var("x", nat_ty);
    let two = d.lit(&l, 2);
    let five = d.lit(&l, 5);
    let edges = [le_edge(&l, &two, &x), le_edge(&l, &x, &five)];
    assert!(refute_chain(&l, &d, &edges).is_err());
}
