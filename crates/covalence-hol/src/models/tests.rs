//! The **objective function** (binary pass/fail): ONE abstract `add_comm`
//! proof, written against the `Nat` interface, checks at BOTH models and
//! yields a genuine theorem at each carrier — plus the literal-lift demo.

use super::*;

/// A theorem is *genuine* iff it has no hypotheses and no oracle observations.
fn assert_genuine(thm: &Thm, what: &str) {
    assert!(thm.hyps().is_empty(), "{what}: must be hypothesis-free");
    assert!(thm.has_no_obs(), "{what}: must be oracle-free");
}

#[test]
fn nat_self_model_axioms_are_genuine() {
    let m = NatSelf.nat_model().expect("nat/self model");
    assert_genuine(&m.zero_add, "nat/self zero.add");
    assert_genuine(&m.add_zero, "nat/self add.zero");
    assert_genuine(&m.succ_add, "nat/self succ.add");
    assert_genuine(&m.add_succ, "nat/self add.succ");
}

#[test]
fn nat_unary_model_axioms_are_genuine() {
    // The NEW content the second model forces — each over `list unit`.
    let m = NatUnary.nat_model().expect("nat/unary model");
    assert_genuine(&m.zero_add, "nat/unary zero.add");
    assert_genuine(&m.add_zero, "nat/unary add.zero");
    assert_genuine(&m.succ_add, "nat/unary succ.add");
    assert_genuine(&m.add_succ, "nat/unary add.succ (the unit-singleton one)");
}

/// THE OBJECTIVE FUNCTION: the same `add_comm.cov` proves commutativity at
/// BOTH carriers — `nat` for `nat/self`, `list unit` (append) for `nat/unary`
/// — each a genuine, distinct kernel theorem.
#[test]
fn add_comm_replays_across_both_models() {
    let self_model = NatSelf.nat_model().expect("nat/self model");
    let unary_model = NatUnary.nat_model().expect("nat/unary model");

    let self_thm = prove_add_comm(&self_model).expect("add_comm at nat/self");
    let unary_thm = prove_add_comm(&unary_model).expect("add_comm at nat/unary");

    // Both are GENUINE hyp-free theorems.
    assert_genuine(&self_thm, "add_comm @ nat/self");
    assert_genuine(&unary_thm, "add_comm @ nat/unary");

    // They are about DIFFERENT carriers — distinct theorems from one source.
    let self_s = format!("{}", self_thm.concl());
    let unary_s = format!("{}", unary_thm.concl());
    assert_ne!(
        self_s, unary_s,
        "the two replays must yield carrier-specific theorems"
    );
    // `nat/self` is about kernel `nat` addition.
    assert!(
        self_s.contains("nat.add") || self_s.contains('+'),
        "nat/self add_comm mentions nat addition: {self_s}"
    );
    // `nat/unary` is about `list` append (`list.cat`).
    assert!(
        unary_s.contains("list.cat") || unary_s.contains("cat"),
        "nat/unary add_comm mentions list append: {unary_s}"
    );
}

/// Literal lifting is model-relative and fallible: `lift_int(3)` differs per
/// model (`nat` literal vs unary `cons unit.nil … nil` conversion).
#[test]
fn lift_int_is_model_relative() {
    let three = Int::from(3i64);

    // nat/self: the built-in nat literal `3`.
    let self_lift = NatSelf.lift_int(&three).expect("nat/self lifts 3");
    assert_eq!(self_lift.type_of().expect("typed"), Type::nat());

    // nat/unary: the unary conversion `cons unit.nil (cons unit.nil (cons unit.nil nil))`.
    let unary_lift = NatUnary.lift_int(&three).expect("nat/unary lifts 3");
    assert_eq!(
        unary_lift.type_of().expect("typed"),
        unary::carrier(),
        "unary lift lands in `list unit`"
    );
    // It really is three `succ`s deep (length-3 list of units).
    let s = format!("{unary_lift}");
    assert_eq!(
        s.matches("unit.nil").count(),
        3,
        "lift_int(3) = three unit.nil cons cells: {s}"
    );

    // The two lifts are genuinely different terms.
    assert_ne!(format!("{self_lift}"), format!("{unary_lift}"));
}

/// The `#in MODEL …` SURFACE form: one `.cov` script with two `#in` blocks
/// replays the IDENTICAL `add.comm` proof body in both models, dispatching
/// `m.induct`/`m.add`/the axioms per model. Demonstrates the surface-level
/// model dispatch (not just the Rust `prove_add_comm` harness).
#[test]
fn in_surface_form_dispatches_per_model() {
    let self_env = NatSelf.nat_model().expect("nat/self model").env();
    let unary_env = NatUnary.nat_model().expect("nat/unary model").env();
    let theory = crate::script::run(
        include_str!("dispatch.cov"),
        move |name| match name {
            "core" => Some(Env::core()),
            "nat-self" => Some(self_env.clone()),
            "nat-unary" => Some(unary_env.clone()),
            _ => None,
        },
        |_| None,
    )
    .expect("dispatch.cov parses")
    .resolve_blocking()
    .expect("dispatch.cov checks at both models");

    let names: Vec<&str> = theory.thms.iter().map(|nt| nt.name.as_str()).collect();
    assert!(names.contains(&"nat-self.add.comm"), "got {names:?}");
    assert!(names.contains(&"nat-unary.add.comm"), "got {names:?}");
    for nt in &theory.thms {
        assert_genuine(&nt.thm, &nt.name);
    }
    // The two replays prove carrier-specific statements.
    let s = theory
        .thms
        .iter()
        .find(|nt| nt.name == "nat-self.add.comm")
        .map(|nt| format!("{}", nt.thm.concl()))
        .unwrap();
    let uu = theory
        .thms
        .iter()
        .find(|nt| nt.name == "nat-unary.add.comm")
        .map(|nt| format!("{}", nt.thm.concl()))
        .unwrap();
    assert_ne!(s, uu);
    assert!(s.contains("nat.add") || s.contains('+'));
    assert!(uu.contains("list.cat") || uu.contains("cat"));
}

/// THE FUSION OBJECTIVE: `declared.cov` declares the `Nat` signature + theory
/// as data (`#sig`/`#thy`), declares `nat/self` + `nat/unary` as models
/// (`#model`), certifies each `M ⊨ NatAddTheory` (`#models`), and replays the SAME
/// abstract `add.comm` proof at both via `(#in M …)` — sourcing ops from the
/// declared model and axioms from the satisfaction certificate, NOT a hand-built
/// Rust `NatModel::env()`. Each replay is a genuine, hyp/oracle-free theorem at
/// its own carrier.
#[test]
fn declared_sig_thy_model_replays_add_comm() {
    let theory = run_declared().expect("declared.cov runs end to end");

    let names: Vec<&str> = theory.thms.iter().map(|nt| nt.name.as_str()).collect();
    // The satisfaction certificates landed (M.axname), per model.
    for ax in ["zero.add", "add.zero", "succ.add", "add.succ"] {
        assert!(
            names.contains(&format!("nat/self.{ax}").as_str()),
            "nat/self certificate `{ax}` missing: {names:?}"
        );
        assert!(
            names.contains(&format!("nat/unary.{ax}").as_str()),
            "nat/unary certificate `{ax}` missing: {names:?}"
        );
    }
    // The two replayed `add.comm` theorems landed.
    assert!(names.contains(&"nat/self.add.comm"), "got {names:?}");
    assert!(names.contains(&"nat/unary.add.comm"), "got {names:?}");

    // EVERY produced theorem is genuine (hyp- and oracle-free) — the kernel
    // re-derived all of it from the declared data.
    for nt in &theory.thms {
        assert_genuine(&nt.thm, &nt.name);
    }

    // The two replays prove CARRIER-SPECIFIC statements (one source, two facts).
    let self_s = theory
        .thms
        .iter()
        .find(|nt| nt.name == "nat/self.add.comm")
        .map(|nt| format!("{}", nt.thm.concl()))
        .unwrap();
    let unary_s = theory
        .thms
        .iter()
        .find(|nt| nt.name == "nat/unary.add.comm")
        .map(|nt| format!("{}", nt.thm.concl()))
        .unwrap();
    assert_ne!(self_s, unary_s);
    assert!(
        self_s.contains("nat.add") || self_s.contains('+'),
        "nat/self add.comm is about nat addition: {self_s}"
    );
    assert!(
        unary_s.contains("list.cat") || unary_s.contains("cat"),
        "nat/unary add.comm is about list append: {unary_s}"
    );

    // The DECLARED replays must match the hand-built Track 1 results exactly —
    // the declared path produces the same theorems `prove_add_comm` does.
    let self_ref = prove_add_comm(&NatSelf.nat_model().unwrap()).unwrap();
    let unary_ref = prove_add_comm(&NatUnary.nat_model().unwrap()).unwrap();
    assert_eq!(self_s, format!("{}", self_ref.concl()));
    assert_eq!(unary_s, format!("{}", unary_ref.concl()));
}

/// A logic legitimately REJECTS a literal kind it cannot lower (here: a
/// string at a `Nat` model) — a diagnostic, not a silent coercion.
#[test]
fn lift_rejects_unsupported_literal() {
    assert!(NatSelf.lift_string("hi").is_err());
    assert!(NatUnary.lift_bytes(&[1, 2, 3]).is_err());
    // A negative int is not a Nat — rejected at both.
    let neg = Int::from(-1i64);
    assert!(NatSelf.lift_int(&neg).is_err());
    assert!(NatUnary.lift_int(&neg).is_err());
}
