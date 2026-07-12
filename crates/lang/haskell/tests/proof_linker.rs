//! **The proof-format flagship: dialect theorems + separate S-expr proofs,
//! linked by name and checked end-to-end through the abstract `Hol`/`Nat`
//! traits.**
//!
//! `examples/nat_theorems.hs` declares theorems whose statements are EQUATION
//! expressions (`a == a`, `0 + m == m`, `a + b == b + a`); `nat_theorems.proof`
//! supplies proofs for two of them, keyed by name. This test:
//!
//! 1. lowers each statement to a HOL `Term : bool` (free vars ∀-closed);
//! 2. replays the matching proof through `NativeHol` to build a real `Thm`;
//! 3. checks the produced conclusion α-equals the lowered statement
//!    (`refl_a`, `add_base_thm` — genuinely PROVED);
//! 4. reports the proof-less `add_comm_thm` as a HOLE; and
//! 5. rejects a deliberately WRONG proof.
//!
//! The replayer/linker names no backend type except through `H: Hol + Nat`, so
//! the concrete kernel is chosen only where the test picks `NativeHol` as `H`.
#![cfg(feature = "hol-typed")]

use std::collections::BTreeSet;

use covalence_haskell::ast::{Item, Theorem};
use covalence_haskell::parse::parse_items;
use covalence_haskell::proof::{
    Lemmas, LinkOutcome, ProofSet, link_theorem, lower_theorem_statement,
};
use covalence_haskell::typed::Env;
use covalence_hol_api::{Hol, Nat, NativeHol};

const THEOREMS: &str = include_str!("../examples/nat_theorems.hs");
const PROOFS: &str = include_str!("../examples/nat_theorems.proof");

/// A typing env for the nat theorems: every statement variable is `nat`. (There
/// is no inference; the demo types all free variables as naturals.)
fn nat_env(h: &NativeHol) -> Env<NativeHol> {
    let mut env = Env::new();
    for v in ["a", "b", "m", "n"] {
        env.bind(v, Nat::nat_ty(h));
    }
    env
}

/// The theorem items of the example module.
fn theorems() -> Vec<Theorem> {
    parse_items(THEOREMS)
        .expect("dialect theorems parse")
        .into_iter()
        .filter_map(|it| match it {
            Item::Thm(t) => Some(t),
            Item::Def(_) => None,
        })
        .collect()
}

/// Lower a theorem's statement to a proposition, ∀-closing all free variables
/// (no ambient theory ops in the nat demo).
fn lower(h: &NativeHol, env: &Env<NativeHol>, t: &Theorem) -> covalence_hol_api::Term {
    lower_theorem_statement(h, env, &t.statement, &BTreeSet::new()).expect("statement lowers")
}

#[test]
fn statements_are_equations_not_types() {
    // `0 + m == m` lowers to the proposition `∀m. 0 + m = m` — a `bool` term,
    // NOT a type. This is the load-bearing framing check.
    let h = NativeHol;
    let env = nat_env(&h);
    let thms = theorems();
    let add_base = thms.iter().find(|t| t.name == "add_base_thm").unwrap();
    let prop = lower(&h, &env, add_base);
    assert_eq!(
        h.type_of(&prop).unwrap(),
        h.bool_ty(),
        "statement is a bool"
    );

    // It equals the ∀-closed `add_base` accessor conclusion (`∀m. 0 + m = m`).
    let add_base_thm = h.add_base().unwrap();
    assert_eq!(
        prop,
        h.concl(&add_base_thm),
        "lowered statement == ∀m. 0 + m = m"
    );
}

#[test]
fn proved_theorems_link_and_check() {
    let h = NativeHol;
    let env = nat_env(&h);
    let lemmas = Lemmas::with_nat_accessors(&h).expect("nat accessors");
    let proofs = ProofSet::parse(PROOFS).expect("proof file parses");

    for name in ["refl_a", "add_base_thm"] {
        let t = theorems().into_iter().find(|t| t.name == name).unwrap();
        let stmt = lower(&h, &env, &t);
        match link_theorem(&h, &lemmas, &proofs, &t.name, &stmt, t.axiom) {
            LinkOutcome::Proved(thm) => {
                // The checked theorem's conclusion IS the statement.
                assert_eq!(h.concl(&thm), stmt, "{name}: conclusion == statement");
            }
            other => panic!("{name} should be Proved, got {other:?}"),
        }
    }
}

#[test]
fn refl_conclusion_is_forall_a_eq() {
    // Spell out the `refl_a` result: `∀a. a = a`, built by the replayer.
    let h = NativeHol;
    let env = nat_env(&h);
    let lemmas = Lemmas::with_nat_accessors(&h).unwrap();
    let proofs = ProofSet::parse(PROOFS).unwrap();
    let t = theorems().into_iter().find(|t| t.name == "refl_a").unwrap();
    let stmt = lower(&h, &env, &t);

    // Reference: ∀a. a = a.
    let a = h.var("a", Nat::nat_ty(&h));
    let a_eq_a = h.eq(a.clone(), a).unwrap();
    let forall = h.forall("a", Nat::nat_ty(&h), a_eq_a).unwrap();
    assert_eq!(stmt, forall, "statement is ∀a. a = a");

    match link_theorem(&h, &lemmas, &proofs, &t.name, &stmt, t.axiom) {
        LinkOutcome::Proved(thm) => assert_eq!(h.concl(&thm), forall),
        other => panic!("expected Proved, got {other:?}"),
    }
}

#[test]
fn missing_proof_is_a_hole() {
    let h = NativeHol;
    let env = nat_env(&h);
    let lemmas = Lemmas::with_nat_accessors(&h).unwrap();
    let proofs = ProofSet::parse(PROOFS).unwrap();

    // `add_comm_thm` has NO proof in the file → a reported hole, not fatal.
    let t = theorems()
        .into_iter()
        .find(|t| t.name == "add_comm_thm")
        .unwrap();
    let stmt = lower(&h, &env, &t);
    assert!(
        matches!(
            link_theorem(&h, &lemmas, &proofs, &t.name, &stmt, t.axiom),
            LinkOutcome::Hole
        ),
        "add_comm_thm should be a hole"
    );
    // And the proof set really has no entry for it.
    assert!(proofs.get("add_comm_thm").is_none());
}

#[test]
fn wrong_proof_is_rejected() {
    let h = NativeHol;
    let env = nat_env(&h);
    let lemmas = Lemmas::with_nat_accessors(&h).unwrap();

    // A proof whose conclusion does NOT match `add_base_thm`'s statement
    // (`∀m. 0 + m = m`): it proves `∀a. a = a` instead. Replay SUCCEEDS (it is a
    // valid derivation) but the conclusion mismatches, so the linker REJECTS it.
    let wrong = "(proof add_base_thm (refl (var a nat)) (all-intro #1 a nat))";
    let proofs = ProofSet::parse(wrong).unwrap();

    let t = theorems()
        .into_iter()
        .find(|t| t.name == "add_base_thm")
        .unwrap();
    let stmt = lower(&h, &env, &t);
    match link_theorem(&h, &lemmas, &proofs, &t.name, &stmt, t.axiom) {
        LinkOutcome::Mismatch(msg) => {
            assert!(msg.contains("does not match"), "reason: {msg}");
        }
        other => panic!("wrong proof must be rejected, got {other:?}"),
    }
}

#[test]
fn ill_formed_proof_is_rejected_not_a_hole() {
    // A proof that cites an unknown lemma fails to replay → Mismatch (rejected),
    // distinct from a missing proof (Hole).
    let h = NativeHol;
    let env = nat_env(&h);
    let lemmas = Lemmas::with_nat_accessors(&h).unwrap();
    let proofs = ProofSet::parse("(proof refl_a (lemma no_such_lemma))").unwrap();

    let t = theorems().into_iter().find(|t| t.name == "refl_a").unwrap();
    let stmt = lower(&h, &env, &t);
    assert!(matches!(
        link_theorem(&h, &lemmas, &proofs, &t.name, &stmt, t.axiom),
        LinkOutcome::Mismatch(_)
    ));
}
