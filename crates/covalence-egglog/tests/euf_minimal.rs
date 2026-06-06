//! Integration tests for `KernelEgglogBridge`.
//!
//! Exercises the *stable boundary*: trait + driver + `KernelEgglogBridge`
//! impl against `covalence_kernel::Kernel`. Currently wired:
//! [`Justification::Fiat`], [`Justification::Trans`], [`Justification::Sym`].
//! The remaining justifications (`Rule`, `MergeFn`, `Congr`) should surface
//! [`BridgeError::NotImplemented`] tagged with the variant name so a future
//! Stage knows exactly what to wire next.

use covalence_egglog::{
    BridgeError, EgglogBridge, KernelEgglogBridge, Proof, ProofStore, Proposition, Term, TermDag,
    ingest_proof_store,
    proof::Justification,
};
use covalence_kernel::Kernel;
use covalence_types::Decision;

// =====================================================================
// Decision starts at Unknown
// =====================================================================

#[test]
fn fresh_bridge_decision_is_unknown() {
    let mut kernel = Kernel::new();
    let bridge = KernelEgglogBridge::new(&mut kernel);
    assert_eq!(bridge.decision(), Decision::Unknown);
}

// =====================================================================
// Sort + constructor declarations register
// =====================================================================

#[test]
fn declare_sort_and_constructor_succeed() {
    let mut kernel = Kernel::new();
    let mut bridge = KernelEgglogBridge::new(&mut kernel);

    bridge.declare_sort("U").unwrap();
    bridge.declare_constructor("a", &[], "U").unwrap();
    bridge.declare_constructor("b", &[], "U").unwrap();
    bridge.declare_constructor("f", &["U"], "U").unwrap();

    assert!(bridge.lookup_sort("U").is_some());
    assert!(bridge.lookup_constructor_ty("a").is_some());
    assert!(bridge.lookup_constructor_ty("b").is_some());
    assert!(bridge.lookup_constructor_ty("f").is_some());
}

// =====================================================================
// Declaring a constructor whose result sort is unknown fails loud
// =====================================================================

#[test]
fn unknown_result_sort_rejected() {
    let mut kernel = Kernel::new();
    let mut bridge = KernelEgglogBridge::new(&mut kernel);
    let err = bridge
        .declare_constructor("a", &[], "Nope")
        .expect_err("undeclared result sort should fail");
    assert!(matches!(err, BridgeError::UnknownSort(s) if s == "Nope"));
}

// =====================================================================
// Fiat on a fresh top-level union — Layer-A's smallest end-to-end path
// =====================================================================

#[test]
fn fiat_top_level_union_closes() {
    // Build:
    //   sort U; constants a, b : U.
    //   Fiat-justified proof of `a = b`.
    // Expect: ingest_proof_store returns a P::Thm for the Fiat proof.
    let mut kernel = Kernel::new();
    let mut bridge = KernelEgglogBridge::new(&mut kernel);
    bridge.declare_sort("U").unwrap();
    bridge.declare_constructor("a", &[], "U").unwrap();
    bridge.declare_constructor("b", &[], "U").unwrap();

    let mut dag = TermDag::new();
    let t_a = dag.alloc(Term::Const("a".into()));
    let t_b = dag.alloc(Term::Const("b".into()));

    let mut store = ProofStore::new();
    let p0 = store.alloc(Proof {
        proposition: Proposition::new(t_a, t_b),
        justification: Justification::Fiat,
    });

    let _thm = ingest_proof_store(&mut bridge, &store, &dag, p0)
        .expect("Fiat ingestion should succeed");
}

// =====================================================================
// Fiat on a reflexive equality — primitive `t = t` discharged by refl
// =====================================================================

#[test]
fn fiat_reflexive_discharges_via_refl() {
    let mut kernel = Kernel::new();
    let mut bridge = KernelEgglogBridge::new(&mut kernel);
    bridge.declare_sort("U").unwrap();
    bridge.declare_constructor("a", &[], "U").unwrap();

    let mut dag = TermDag::new();
    let t_a = dag.alloc(Term::Const("a".into()));

    let mut store = ProofStore::new();
    let p0 = store.alloc(Proof {
        // `lhs == rhs` as TermIds — same arena node, so the bridge's
        // materialise produces equal `P::Term` handles and Fiat discharges
        // via `refl` rather than pushing an assumption.
        proposition: Proposition::new(t_a, t_a),
        justification: Justification::Fiat,
    });

    let _thm = ingest_proof_store(&mut bridge, &store, &dag, p0)
        .expect("reflexive Fiat should close via refl");
}

// =====================================================================
// Fiat over an application term — exercises materialise() on App nodes
// =====================================================================

#[test]
fn fiat_over_unary_application() {
    // `f : U -> U`, `a, b : U`, Fiat-justified `f(a) = f(b)`. The bridge
    // builds `(comb f a)` and `(comb f b)` and assumes their equality.
    let mut kernel = Kernel::new();
    let mut bridge = KernelEgglogBridge::new(&mut kernel);
    bridge.declare_sort("U").unwrap();
    bridge.declare_constructor("a", &[], "U").unwrap();
    bridge.declare_constructor("b", &[], "U").unwrap();
    bridge.declare_constructor("f", &["U"], "U").unwrap();

    let mut dag = TermDag::new();
    let t_a = dag.alloc(Term::Const("a".into()));
    let t_b = dag.alloc(Term::Const("b".into()));
    let t_fa = dag.alloc(Term::App("f".into(), vec![t_a]));
    let t_fb = dag.alloc(Term::App("f".into(), vec![t_b]));

    let mut store = ProofStore::new();
    let p0 = store.alloc(Proof {
        proposition: Proposition::new(t_fa, t_fb),
        justification: Justification::Fiat,
    });

    let _thm = ingest_proof_store(&mut bridge, &store, &dag, p0)
        .expect("Fiat over application terms should close");
}

// =====================================================================
// App with wrong arity — loud structured failure
// =====================================================================

#[test]
fn arity_mismatch_rejected() {
    let mut kernel = Kernel::new();
    let mut bridge = KernelEgglogBridge::new(&mut kernel);
    bridge.declare_sort("U").unwrap();
    bridge.declare_constructor("a", &[], "U").unwrap();
    bridge.declare_constructor("f", &["U"], "U").unwrap();

    let mut dag = TermDag::new();
    let t_a = dag.alloc(Term::Const("a".into()));
    // `f` is unary, but we apply it to two args.
    let t_bad = dag.alloc(Term::App("f".into(), vec![t_a, t_a]));

    let mut store = ProofStore::new();
    let p0 = store.alloc(Proof {
        proposition: Proposition::new(t_bad, t_bad),
        justification: Justification::Fiat,
    });

    let err = ingest_proof_store(&mut bridge, &store, &dag, p0)
        .expect_err("arity mismatch should surface");
    assert!(matches!(err, BridgeError::ArityMismatch { ref name, expected: 1, actual: 2 } if name == "f"));
}

// =====================================================================
// Trans — chain two grounded equations
// =====================================================================

#[test]
fn trans_chains_two_fiat_equations() {
    // `a = b` (Fiat), `b = c` (Fiat) ⊢ `a = c` (Trans).
    let mut kernel = Kernel::new();
    let mut bridge = KernelEgglogBridge::new(&mut kernel);
    bridge.declare_sort("U").unwrap();
    bridge.declare_constructor("a", &[], "U").unwrap();
    bridge.declare_constructor("b", &[], "U").unwrap();
    bridge.declare_constructor("c", &[], "U").unwrap();

    let mut dag = TermDag::new();
    let t_a = dag.alloc(Term::Const("a".into()));
    let t_b = dag.alloc(Term::Const("b".into()));
    let t_c = dag.alloc(Term::Const("c".into()));

    let mut store = ProofStore::new();
    let ab = store.alloc(Proof {
        proposition: Proposition::new(t_a, t_b),
        justification: Justification::Fiat,
    });
    let bc = store.alloc(Proof {
        proposition: Proposition::new(t_b, t_c),
        justification: Justification::Fiat,
    });
    let ac = store.alloc(Proof {
        proposition: Proposition::new(t_a, t_c),
        justification: Justification::Trans(ab, bc),
    });

    let _thm = ingest_proof_store(&mut bridge, &store, &dag, ac)
        .expect("trans should chain a=b and b=c");
}

// =====================================================================
// Sym — flip a grounded equation
// =====================================================================

#[test]
fn sym_flips_fiat_equation() {
    // `a = b` (Fiat) ⊢ `b = a` (Sym).
    let mut kernel = Kernel::new();
    let mut bridge = KernelEgglogBridge::new(&mut kernel);
    bridge.declare_sort("U").unwrap();
    bridge.declare_constructor("a", &[], "U").unwrap();
    bridge.declare_constructor("b", &[], "U").unwrap();

    let mut dag = TermDag::new();
    let t_a = dag.alloc(Term::Const("a".into()));
    let t_b = dag.alloc(Term::Const("b".into()));

    let mut store = ProofStore::new();
    let ab = store.alloc(Proof {
        proposition: Proposition::new(t_a, t_b),
        justification: Justification::Fiat,
    });
    let ba = store.alloc(Proof {
        proposition: Proposition::new(t_b, t_a),
        justification: Justification::Sym(ab),
    });

    let _thm = ingest_proof_store(&mut bridge, &store, &dag, ba)
        .expect("sym should flip a=b to b=a");
}

// =====================================================================
// Trans + Sym — combine both into a single proof
// =====================================================================

#[test]
fn trans_with_symmetrised_premise() {
    // From `a = b` and `c = b`, derive `a = c` via trans(a=b, sym(c=b)).
    let mut kernel = Kernel::new();
    let mut bridge = KernelEgglogBridge::new(&mut kernel);
    bridge.declare_sort("U").unwrap();
    bridge.declare_constructor("a", &[], "U").unwrap();
    bridge.declare_constructor("b", &[], "U").unwrap();
    bridge.declare_constructor("c", &[], "U").unwrap();

    let mut dag = TermDag::new();
    let t_a = dag.alloc(Term::Const("a".into()));
    let t_b = dag.alloc(Term::Const("b".into()));
    let t_c = dag.alloc(Term::Const("c".into()));

    let mut store = ProofStore::new();
    let ab = store.alloc(Proof {
        proposition: Proposition::new(t_a, t_b),
        justification: Justification::Fiat,
    });
    let cb = store.alloc(Proof {
        proposition: Proposition::new(t_c, t_b),
        justification: Justification::Fiat,
    });
    let bc = store.alloc(Proof {
        proposition: Proposition::new(t_b, t_c),
        justification: Justification::Sym(cb),
    });
    let ac = store.alloc(Proof {
        proposition: Proposition::new(t_a, t_c),
        justification: Justification::Trans(ab, bc),
    });

    let _thm = ingest_proof_store(&mut bridge, &store, &dag, ac)
        .expect("trans(a=b, sym(c=b)) should produce a=c");
}

// =====================================================================
// Still-unwired justifications surface NotImplemented tagged with variant
// =====================================================================

#[test]
fn congr_is_not_implemented_yet() {
    let mut kernel = Kernel::new();
    let mut bridge = KernelEgglogBridge::new(&mut kernel);
    bridge.declare_sort("U").unwrap();
    bridge.declare_constructor("a", &[], "U").unwrap();
    bridge.declare_constructor("b", &[], "U").unwrap();
    bridge.declare_constructor("f", &["U"], "U").unwrap();

    let mut dag = TermDag::new();
    let t_a = dag.alloc(Term::Const("a".into()));
    let t_b = dag.alloc(Term::Const("b".into()));
    let t_fa = dag.alloc(Term::App("f".into(), vec![t_a]));
    let t_fb = dag.alloc(Term::App("f".into(), vec![t_b]));

    let mut store = ProofStore::new();
    let ab = store.alloc(Proof {
        proposition: Proposition::new(t_a, t_b),
        justification: Justification::Fiat,
    });
    let fa_eq = store.alloc(Proof {
        proposition: Proposition::new(t_fa, t_fa),
        justification: Justification::Fiat,
    });
    let cong = store.alloc(Proof {
        proposition: Proposition::new(t_fa, t_fb),
        justification: Justification::Congr {
            proof: fa_eq,
            child_index: 0,
            child_proof: ab,
        },
    });

    let err = ingest_proof_store(&mut bridge, &store, &dag, cong)
        .expect_err("congr is not wired yet");
    assert!(matches!(err, BridgeError::NotImplemented(s) if s == "congr"));
}

#[test]
fn rule_is_not_implemented_yet() {
    use std::collections::HashMap;

    let mut kernel = Kernel::new();
    let mut bridge = KernelEgglogBridge::new(&mut kernel);
    bridge.declare_sort("U").unwrap();
    bridge.declare_constructor("a", &[], "U").unwrap();
    bridge.declare_constructor("b", &[], "U").unwrap();

    let mut dag = TermDag::new();
    let t_a = dag.alloc(Term::Const("a".into()));
    let t_b = dag.alloc(Term::Const("b".into()));

    let mut store = ProofStore::new();
    let rule_step = store.alloc(Proof {
        proposition: Proposition::new(t_a, t_b),
        justification: Justification::Rule {
            name: "my-rule".into(),
            premise_proofs: vec![],
            substitution: HashMap::new(),
        },
    });

    let err = ingest_proof_store(&mut bridge, &store, &dag, rule_step)
        .expect_err("rule is not wired yet");
    assert!(matches!(err, BridgeError::NotImplemented(s) if s == "rule:my-rule"));
}
