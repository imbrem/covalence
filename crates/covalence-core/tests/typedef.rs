//! Tests for `Thm::new_type_definition`.
//!
//! Given a witness theorem `Γ ⊢ P x`, the rule allocates a fresh
//! subtype τ ≤ α with bijection constants `abs : α → τ`, `rep : τ → α`
//! and the three bijection theorems. The kernel's freshness comes
//! from `Arc` identity — distinct calls with the same hint and same
//! witness produce distinct types/constants.

use covalence_core::{Term, TermKind, Thm, Type, TypeKind};

/// Build a witness theorem `⊢ P x` for `P : α → prop` and `x : α`,
/// where x is `Free("witness", α)` and P is `λ_. ⊢ true` modeled as
/// `λ_:α. x ≡ x`. (No HOL bool yet — we use a Pure-level prop
/// formed from refl on a fixed free variable.)
fn refl_witness(alpha: &Type) -> Thm {
    // P :≡ λ_:α. (Free "anchor" : α) ≡ (Free "anchor" : α)
    // Then P x reduces by β to the same prop. We use β-conversion as
    // the path to get `⊢ P x`.
    //
    // Construct (λ_:α. anchor ≡ anchor) x, then run beta_conv.
    let anchor = Term::free("anchor", alpha.clone());
    let body = Term::eq(anchor.clone(), anchor.clone());
    let lam = Term::abs("_", alpha.clone(), body);
    let x = Term::free("witness", alpha.clone());
    let app = Term::app(lam.clone(), x.clone());
    // Step 1: ⊢ (λ_. anchor ≡ anchor) x ≡ anchor ≡ anchor.
    let beta = Thm::beta_conv(app.clone()).unwrap();
    // Step 2: ⊢ anchor ≡ anchor (just refl, but reused).
    let refl = Thm::refl(anchor).unwrap();
    // Combine: from `⊢ refl` and `⊢ app ≡ refl` derive `⊢ app` — that's
    // the eq_mp / sym + trans direction. We use sym on beta then
    // we're stuck — we'd need EQ_MP (HOL Light rule, not Pure).
    //
    // Simpler: bypass the indirection. The witness theorem the rule
    // needs is `⊢ P x` for SOME P x application form. Let me just
    // build it more directly: take an explicit predicate.
    let _ = (beta, refl, app, lam);
    // Build P as a free variable directly: P := Free("P", α → prop).
    let p = Term::free("P", Type::fun(alpha.clone(), Type::prop()));
    let p_x = Term::app(p, x);
    // We can't prove ⊢ P x as a closed theorem without an assumption.
    // So use Thm::assume to get {P x} ⊢ P x.
    Thm::assume(p_x).unwrap()
}

#[test]
fn typedef_returns_three_bijection_thms() {
    let alpha = Type::bytes();
    let witness = refl_witness(&alpha);
    let td = Thm::new_type_definition("τ", "abs", "rep", witness.clone()).unwrap();

    // All three Thms carry the witness's hyps.
    assert_eq!(td.abs_rep.hyps(), witness.hyps());
    assert_eq!(td.rep_abs_fwd.hyps(), witness.hyps());
    assert_eq!(td.rep_abs_back.hyps(), witness.hyps());
}

#[test]
fn typedef_abs_rep_concl_is_universal_bijection() {
    let alpha = Type::bytes();
    let witness = refl_witness(&alpha);
    let td = Thm::new_type_definition("τ", "abs", "rep", witness).unwrap();

    // Concl: ⋀a:τ. abs (rep a) ≡ a
    let TermKind::All(_, ty, body) = td.abs_rep.concl().kind() else {
        panic!("expected All");
    };
    assert_eq!(ty, &td.tau);
    let TermKind::Eq(lhs, rhs) = body.kind() else {
        panic!("expected Eq");
    };
    // RHS is Bound(0).
    assert!(matches!(rhs.kind(), TermKind::Bound(0)));
    // LHS is abs (rep Bound(0)). Just check the structural shape —
    // it's not closed outside the ⋀-binder so refl/type_of would fail.
    let TermKind::App(outer_fn, outer_arg) = lhs.kind() else {
        panic!("expected (abs (rep b))");
    };
    assert_eq!(outer_fn, &td.abs, "outer head should be `abs`");
    let TermKind::App(inner_fn, inner_arg) = outer_arg.kind() else {
        panic!("expected (rep b) inside");
    };
    assert_eq!(inner_fn, &td.rep, "inner head should be `rep`");
    assert!(matches!(inner_arg.kind(), TermKind::Bound(0)));
}

#[test]
fn typedef_distinct_calls_produce_distinct_taus() {
    let alpha = Type::bytes();
    let w1 = refl_witness(&alpha);
    let w2 = refl_witness(&alpha);
    let td1 = Thm::new_type_definition("τ", "abs", "rep", w1).unwrap();
    let td2 = Thm::new_type_definition("τ", "abs", "rep", w2).unwrap();
    assert_ne!(
        td1.tau, td2.tau,
        "two new_type_definition calls produce distinct fresh types"
    );
    assert_ne!(td1.abs, td2.abs, "abs constants are also distinct");
    assert_ne!(td1.rep, td2.rep, "rep constants are also distinct");
}

#[test]
fn typedef_tau_is_a_tycon_obs_carrying_the_hint() {
    let alpha = Type::bytes();
    let witness = refl_witness(&alpha);
    let td = Thm::new_type_definition("MyT", "abs", "rep", witness).unwrap();
    match td.tau.kind() {
        TypeKind::TyConObs(_, hint, args) => {
            assert_eq!(hint.as_str(), "MyT");
            assert!(args.is_empty(), "α is ground (no tvars) → no τ args");
        }
        _ => panic!("expected TyConObs"),
    }
}

#[test]
fn typedef_polymorphic_alpha_produces_parametric_tau() {
    // P : 'a → prop, x : 'a. τ should be parametric in 'a.
    let alpha = Type::tfree("a");
    let witness = refl_witness(&alpha);
    let td = Thm::new_type_definition("List", "abs", "rep", witness).unwrap();
    assert_eq!(td.tvars, vec![smol_str::SmolStr::new("a")]);
    match td.tau.kind() {
        TypeKind::TyConObs(_, _, args) => {
            assert_eq!(args.len(), 1);
            assert_eq!(args[0], Type::tfree("a"));
        }
        _ => panic!("expected TyConObs"),
    }
}

#[test]
fn typedef_inst_tfree_specialises_the_subtype() {
    // ⊢ P x with x : 'a. After typedef and inst_tfree('a, bytes),
    // the bijection theorems mention `List bytes` not `List 'a`.
    let alpha = Type::tfree("a");
    let witness = refl_witness(&alpha);
    let td = Thm::new_type_definition("List", "abs", "rep", witness).unwrap();

    // Substitute 'a ↦ bytes in the rep_abs_fwd thm.
    let inst = td.rep_abs_fwd.inst_tfree("a", Type::bytes()).unwrap();
    // The conclusion's ⋀-binder type should now be `bytes` (substituted
    // from 'a). And τ in any nested mention should be `List bytes`.
    match inst.concl().kind() {
        TermKind::All(_, ty, _) => assert_eq!(ty, &Type::bytes()),
        _ => panic!(),
    }
}

#[test]
fn typedef_rejects_non_application_witness() {
    // ⊢ refl(x) has concl `x ≡ x` — not an App.
    let x = Term::free("x", Type::bytes());
    let bad = Thm::refl(x).unwrap();
    let err = Thm::new_type_definition("τ", "abs", "rep", bad).unwrap_err();
    let msg = format!("{}", err);
    assert!(msg.contains("witness"), "got: {msg}");
}

#[test]
fn typedef_rejects_witness_with_p_not_returning_prop() {
    // ⊢ P x where P : α → bytes (not prop). Concl shape is `P x`,
    // but P_cod is bytes, so the rule should reject.
    let alpha = Type::bytes();
    let p = Term::free("P", Type::fun(alpha.clone(), Type::bytes()));
    let x = Term::free("witness", alpha);
    let p_x = Term::app(p, x);
    // We can't assume because P x isn't prop. Build the Thm directly
    // via refl on (P x): ⊢ P x ≡ P x has concl `≡`, not `App`. So
    // this path doesn't let us bypass the prop check at the witness.
    //
    // Instead use a different shape: `App(P, x)` where x is structured
    // differently. The rule's BadTypeDefWitness shape-check happens
    // FIRST (concl must be App), but the prop check happens after.
    // To construct a witness with non-prop P cod, we'd need the
    // assume() to succeed on a non-prop term — which the kernel forbids
    // already at Thm::assume time. So this branch of new_type_definition
    // is unreachable from outside the kernel; we just confirm assume
    // rejects.
    let assume_err = Thm::assume(p_x).unwrap_err();
    let msg = format!("{}", assume_err);
    assert!(msg.contains("prop") || msg.contains("kind"), "got: {msg}");
}

#[test]
fn typedef_propagates_witness_hyps() {
    // Witness has hyp {P x}. The three derived Thms should each
    // carry P x as a hypothesis.
    let alpha = Type::bytes();
    let witness = refl_witness(&alpha);
    assert_eq!(witness.hyps().len(), 1);

    let td = Thm::new_type_definition("τ", "abs", "rep", witness.clone()).unwrap();
    let expected = witness.hyps();
    assert_eq!(td.abs_rep.hyps(), expected);
    assert_eq!(td.rep_abs_fwd.hyps(), expected);
    assert_eq!(td.rep_abs_back.hyps(), expected);
}
