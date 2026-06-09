//! End-to-end smoke test for the Observer mechanism.
//!
//! Demonstrates the unforgeability story: a user-defined `O` type
//! with private constructors gates who can create observations. Pure
//! provides only the typed leaf (`Term::obs`) and well-typedness
//! checks; turning an observation into a `Thm` is the user crate's
//! responsibility, which is where the "positive-only" discipline
//! lives.
//!
//! All observation comparisons inside the kernel are by `Arc` pointer
//! identity (via [`Object`]) — never by the underlying observer's
//! `Eq` impl. So a misbehaving user impl cannot break the kernel's
//! invariants.

use bytes::Bytes;
use covalence_core::{Object, ObsEq, Term, TermKind, Thm, Type};

// ============================================================================
// A made-up oracle's observation type, with a gated constructor.
// ============================================================================

mod my_oracle {
    use super::*;
    use std::sync::atomic::{AtomicU64, Ordering};

    /// An observation made by `my_oracle`. Private fields ensure only
    /// this module can construct one.
    #[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    pub struct MyObs {
        oracle_id: u64,
        component_hash: [u8; 4],
        input: Bytes,
        output: Bytes,
    }

    static FRESH: AtomicU64 = AtomicU64::new(1);

    /// `MyObs` opts in to the kernel's `obs_eq` rule by equating any
    /// two `MyObs` applications (the ε-model strategy).
    impl ObsEq for MyObs {
        fn obs_eq(&self, _other: &Self, _: &[Term], _: &[Term], _hint: Option<&dyn covalence_core::Hint>) -> bool {
            true
        }
    }

    impl MyObs {
        /// The only way to construct a `MyObs`. Imagine this actually
        /// runs a WASM component and records the result.
        pub fn run(component_hash: [u8; 4], input: Bytes) -> Self {
            let mut output = input.to_vec();
            output.reverse();
            MyObs {
                oracle_id: FRESH.fetch_add(1, Ordering::Relaxed),
                component_hash,
                input,
                output: output.into(),
            }
        }

        pub fn output(&self) -> &Bytes {
            &self.output
        }
    }

    /// The user crate's trusted conversion. The "positive-only"
    /// discipline lives here: a `MyObs` is converted to a `Thm` whose
    /// conclusion is a positive equation `obs_leaf(input) ≡ output`.
    pub fn obs_thm(o: MyObs) -> Thm {
        let bytes_to_bytes = Type::fun(Type::bytes(), Type::bytes());
        let input_blob = Term::blob(o.input.clone());
        let output_blob = Term::blob(o.output.clone());
        let leaf: Term = Term::obs(o, bytes_to_bytes);
        let applied = Term::app(leaf, input_blob);
        let fact = Term::eq(applied, output_blob);
        Thm::assume(fact).expect("fact is closed and prop-typed")
    }
}

// ============================================================================
// Basic Term::obs behaviour
// ============================================================================

#[test]
fn observation_leaf_has_chosen_type() {
    let obs = my_oracle::MyObs::run([1, 2, 3, 4], Bytes::from_static(b"input"));
    let bytes_to_bytes = Type::fun(Type::bytes(), Type::bytes());
    let leaf = Term::obs(obs, bytes_to_bytes.clone());
    assert_eq!(leaf.type_of().unwrap(), bytes_to_bytes);
}

#[test]
fn observation_term_participates_in_app() {
    let obs = my_oracle::MyObs::run([0, 0, 0, 0], Bytes::from_static(b"hi"));
    let bytes_to_bytes = Type::fun(Type::bytes(), Type::bytes());
    let leaf = Term::obs(obs, bytes_to_bytes);
    let applied = Term::app(leaf, Term::blob(Bytes::from_static(b"hi")));
    assert_eq!(applied.type_of().unwrap(), Type::bytes());
}

#[test]
fn user_crate_can_mint_thm_from_observation() {
    let obs = my_oracle::MyObs::run([0; 4], Bytes::from_static(b"hello"));
    let output = obs.output().clone();
    let thm = my_oracle::obs_thm(obs);
    match thm.concl().kind() {
        TermKind::Eq(_, rhs) => match rhs.kind() {
            TermKind::Blob(b) => assert_eq!(b, &output),
            other => panic!("expected blob rhs, got {:?}", other),
        },
        other => panic!("expected Eq, got {:?}", other),
    }
}

#[test]
fn observations_survive_substitution_of_type_variables() {
    use covalence_core::subst::subst_tfree_in_term;
    let obs = my_oracle::MyObs::run([0; 4], Bytes::from_static(b"x"));
    let leaf = Term::obs(obs, Type::tfree("a"));
    let subst = subst_tfree_in_term(&leaf, "a", &Type::bytes());
    match subst.kind() {
        TermKind::Obs(_, ty) => assert_eq!(ty, &Type::bytes()),
        other => panic!("expected Obs, got {:?}", other),
    }
}

#[test]
fn alpha_equivalence_works_through_observations() {
    // Sharing the SAME leaf via clone — both bodies see the same Arc.
    let obs = my_oracle::MyObs::run([0; 4], Bytes::from_static(b"x"));
    let leaf = Term::obs(obs, Type::bytes());
    let a = Term::abs("x", Type::bytes(), leaf.clone());
    let b = Term::abs("y", Type::bytes(), leaf);
    assert_eq!(a, b, "α-equivalent terms sharing an Obs leaf are equal");
}

// ============================================================================
// Pointer-identity semantics
// ============================================================================

#[test]
fn distinct_obs_calls_produce_distinct_leaves() {
    // Two separate Term::obs calls — even with structurally-equal
    // inputs — produce distinct Obs leaves. This is the
    // pointer-identity invariant that makes the kernel safe even if
    // MyObs has a buggy Eq impl.
    let obs1 = my_oracle::MyObs::run([0; 4], Bytes::from_static(b"x"));
    let obs2 = obs1.clone(); // structurally equal as MyObs
    let leaf1 = Term::obs(obs1, Type::bytes());
    let leaf2 = Term::obs(obs2, Type::bytes());
    assert_ne!(leaf1, leaf2, "distinct Term::obs calls are distinct");

    // But cloning the SAME leaf preserves identity.
    let leaf1b = leaf1.clone();
    assert_eq!(leaf1, leaf1b, "Arc::clone of the same leaf is equal");
}

#[test]
fn dyn_obs_equality_uses_pointer_identity() {
    let obs = my_oracle::MyObs::run([0; 4], Bytes::from_static(b"x"));
    let d1 = Object::new(obs.clone());
    let d2 = Object::new(obs); // same input, different Object
    assert_ne!(d1, d2, "distinct Object::new calls are distinct");

    let d1b = d1.clone();
    assert_eq!(d1, d1b, "Object::clone shares Arc");
}

// ============================================================================
// has_no_obs / all_obs_match / for_each_obs
// ============================================================================

#[test]
fn has_no_obs_on_pure_term() {
    let t = Term::free("x", Type::bytes());
    assert!(t.has_no_obs());
}

#[test]
fn has_no_obs_on_obs_leaf() {
    let obs = my_oracle::MyObs::run([0; 4], Bytes::from_static(b"x"));
    let leaf = Term::obs(obs, Type::bytes());
    assert!(!leaf.has_no_obs());
}

#[test]
fn has_no_obs_on_thm_with_obs_in_hyp() {
    let obs = my_oracle::MyObs::run([0; 4], Bytes::from_static(b"x"));
    let leaf = Term::obs(obs, Type::bytes());
    let phi = Term::eq(leaf.clone(), leaf);
    let thm = Thm::assume(phi).unwrap();
    assert!(!thm.has_no_obs());
}

#[test]
fn has_no_obs_on_universal_thm() {
    let x = Term::free("x", Type::bytes());
    let thm = Thm::refl(x).unwrap();
    assert!(thm.has_no_obs(), "refl(x) is universally true");
}

#[test]
fn all_obs_match_on_homogeneous_obs() {
    let obs = my_oracle::MyObs::run([0; 4], Bytes::from_static(b"x"));
    let leaf = Term::obs(obs, Type::bytes());
    let phi = Term::eq(leaf.clone(), leaf);
    let thm = Thm::assume(phi).unwrap();
    assert!(thm.all_obs_match::<my_oracle::MyObs>());
}

#[test]
fn all_obs_match_fails_on_mismatched_type() {
    #[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    struct OtherObs(u32);

    let obs = my_oracle::MyObs::run([0; 4], Bytes::from_static(b"x"));
    let leaf = Term::obs(obs, Type::bytes());
    let phi = Term::eq(leaf.clone(), leaf);
    let thm = Thm::assume(phi).unwrap();
    assert!(!thm.all_obs_match::<OtherObs>());
}

#[test]
fn for_each_obs_collects_all_leaves() {
    let obs1 = my_oracle::MyObs::run([0; 4], Bytes::from_static(b"a"));
    let obs2 = my_oracle::MyObs::run([1; 4], Bytes::from_static(b"b"));
    let leaf1 = Term::obs(obs1, Type::bytes());
    let leaf2 = Term::obs(obs2, Type::bytes());
    // (leaf1, leaf2) appearing in an Eq
    let t = Term::eq(leaf1, leaf2);
    let thm = Thm::assume(t).unwrap();

    let mut count = 0;
    thm.for_each_obs::<my_oracle::MyObs, _>(&mut |_| count += 1)
        .unwrap();
    // 2 in concl (lhs and rhs of Eq) + 2 in hyp (same phi).
    assert_eq!(count, 4);
}

#[test]
fn for_each_obs_errs_on_type_mismatch() {
    #[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    struct OtherObs(u32);

    let obs = my_oracle::MyObs::run([0; 4], Bytes::from_static(b"x"));
    let leaf = Term::obs(obs, Type::bytes());
    let thm = Thm::refl(leaf).unwrap();

    let result = thm.for_each_obs::<OtherObs, _>(&mut |_| {});
    assert!(matches!(
        result,
        Err(covalence_core::Error::ObsDowncastTypeMismatch)
    ));
}

// ============================================================================
// Object typed downcast
// ============================================================================

#[test]
fn dyn_obs_downcast_to_correct_type() {
    let obs = my_oracle::MyObs::run([7; 4], Bytes::from_static(b"hello"));
    let expected_output = obs.output().clone();
    let d = Object::new(obs);
    let inner: &my_oracle::MyObs = d.downcast().expect("type matches");
    assert_eq!(inner.output(), &expected_output);
}

#[test]
fn dyn_obs_downcast_to_wrong_type_returns_none() {
    #[derive(Debug)]
    struct OtherObs;

    let obs = my_oracle::MyObs::run([0; 4], Bytes::from_static(b"x"));
    let d = Object::new(obs);
    assert!(d.downcast::<OtherObs>().is_none());
}

// ============================================================================
// Thm::obs_eq — kernel rule for cross-instance equality
// ============================================================================

#[test]
fn obs_eq_at_leaf_succeeds_for_same_rust_type() {
    let o1 = my_oracle::MyObs::run([0; 4], Bytes::from_static(b"a"));
    let o2 = my_oracle::MyObs::run([1; 4], Bytes::from_static(b"b"));
    let e1 = Term::obs(o1, Type::bytes());
    let e2 = Term::obs(o2, Type::bytes());
    let thm = Thm::obs_eq::<my_oracle::MyObs>(e1.clone(), e2.clone(), None).unwrap();
    assert!(thm.hyps().is_empty());
    match thm.concl().kind() {
        TermKind::Eq(a, b) => {
            assert_eq!(a, &e1);
            assert_eq!(b, &e2);
        }
        _ => panic!("expected Eq"),
    }
}

#[test]
fn obs_eq_under_applications() {
    // ((obs o1) blob_a) ≡ ((obs o2) blob_b) where both heads are MyObs
    // and both expressions have Pure type `bytes`.
    let o1 = my_oracle::MyObs::run([0; 4], Bytes::from_static(b"a"));
    let o2 = my_oracle::MyObs::run([1; 4], Bytes::from_static(b"b"));
    let f1 = Term::obs(o1, Type::fun(Type::bytes(), Type::bytes()));
    let f2 = Term::obs(o2, Type::fun(Type::bytes(), Type::bytes()));
    let e1 = Term::app(f1, Term::blob(Bytes::from_static(b"x")));
    let e2 = Term::app(f2, Term::blob(Bytes::from_static(b"y")));
    let thm = Thm::obs_eq::<my_oracle::MyObs>(e1.clone(), e2.clone(), None).unwrap();
    assert!(thm.hyps().is_empty());
    match thm.concl().kind() {
        TermKind::Eq(a, b) => {
            assert_eq!(a, &e1);
            assert_eq!(b, &e2);
        }
        _ => panic!("expected Eq"),
    }
}

#[test]
fn obs_eq_with_different_arg_arities() {
    // (obs o1) : bytes -> bytes -> bytes, applied to two args → bytes
    // (obs o2) : bytes -> bytes, applied to one arg → bytes
    // Same final Pure type, same Rust observer type.
    let bb = Type::bytes();
    let ty1 = Type::fun(bb.clone(), Type::fun(bb.clone(), bb.clone()));
    let ty2 = Type::fun(bb.clone(), bb.clone());
    let o1 = my_oracle::MyObs::run([0; 4], Bytes::from_static(b"a"));
    let o2 = my_oracle::MyObs::run([1; 4], Bytes::from_static(b"b"));
    let f1 = Term::obs(o1, ty1);
    let f2 = Term::obs(o2, ty2);
    let e1 = Term::app(
        Term::app(f1, Term::blob(Bytes::from_static(b"p"))),
        Term::blob(Bytes::from_static(b"q")),
    );
    let e2 = Term::app(f2, Term::blob(Bytes::from_static(b"r")));
    assert_eq!(e1.type_of().unwrap(), bb);
    assert_eq!(e2.type_of().unwrap(), bb);
    let thm = Thm::obs_eq::<my_oracle::MyObs>(e1, e2, None).unwrap();
    assert!(thm.hyps().is_empty());
}

#[test]
fn obs_eq_rejects_mismatched_pure_types() {
    let o1 = my_oracle::MyObs::run([0; 4], Bytes::from_static(b"a"));
    let o2 = my_oracle::MyObs::run([1; 4], Bytes::from_static(b"b"));
    let e1 = Term::obs(o1, Type::bytes());
    let e2 = Term::obs(o2, Type::tycon("bool", vec![]));
    let result = Thm::obs_eq::<my_oracle::MyObs>(e1, e2, None);
    assert!(matches!(
        result,
        Err(covalence_core::Error::TypeMismatch { .. })
    ));
}

#[test]
fn obs_eq_rejects_wrong_rust_type() {
    #[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    struct OtherObs(u32);
    impl ObsEq for OtherObs {
        fn obs_eq(&self, _: &Self, _: &[Term], _: &[Term], _hint: Option<&dyn covalence_core::Hint>) -> bool {
            true
        }
    }

    let o = my_oracle::MyObs::run([0; 4], Bytes::from_static(b"a"));
    let e1 = Term::obs(o, Type::bytes());
    let e2 = Term::obs(OtherObs(7), Type::bytes());
    let result = Thm::obs_eq::<my_oracle::MyObs>(e1, e2, None);
    assert!(matches!(
        result,
        Err(covalence_core::Error::ObsDowncastTypeMismatch)
    ));
}

#[test]
fn obs_eq_rejects_non_obs_head() {
    let e1 = Term::free("x", Type::bytes());
    let e2 = Term::free("y", Type::bytes());
    let result = Thm::obs_eq::<my_oracle::MyObs>(e1, e2, None);
    assert!(matches!(result, Err(covalence_core::Error::NotObsHead(_))));
}

#[test]
fn obs_eq_observer_can_refuse_equality() {
    // An observer that only equates two applications when their args
    // are identical Terms (extensional check via arg comparison).
    #[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    struct PickyObs(u32);
    impl ObsEq for PickyObs {
        fn obs_eq(&self, _other: &Self, my_args: &[Term], other_args: &[Term], _hint: Option<&dyn covalence_core::Hint>) -> bool {
            my_args == other_args
        }
    }

    let f_ty = Type::fun(Type::bytes(), Type::bytes());
    let o1 = PickyObs(1);
    let o2 = PickyObs(2);
    let e1 = Term::app(
        Term::obs(o1, f_ty.clone()),
        Term::blob(Bytes::from_static(b"x")),
    );
    let e2 = Term::app(
        Term::obs(o2.clone(), f_ty.clone()),
        Term::blob(Bytes::from_static(b"y")),
    );
    // Different args → refused.
    let result = Thm::obs_eq::<PickyObs>(e1.clone(), e2, None);
    assert!(matches!(result, Err(covalence_core::Error::ObsEqRefused)));

    // Same args → succeeds.
    let e3 = Term::app(Term::obs(o2, f_ty), Term::blob(Bytes::from_static(b"x")));
    assert!(Thm::obs_eq::<PickyObs>(e1, e3, None).is_ok());
}

#[test]
fn obs_eq_demonstrates_untrusted_id_plumbing() {
    // The pattern from the design discussion:
    //   write (a ≡ b) as (untrustedId a ≡ untrustedId b)
    //   then add `untrustedId ≡ id` as an axiom to discharge.
    //
    // Here we just demonstrate the kernel rule: under any model where
    // all UntrustedId observations collapse to the same value at the
    // same Pure type, the application equality is sound.
    #[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    struct UntrustedIdObs;
    impl ObsEq for UntrustedIdObs {
        fn obs_eq(&self, _: &Self, _: &[Term], _: &[Term], _hint: Option<&dyn covalence_core::Hint>) -> bool {
            true
        }
    }

    // (untrusted_id : 'a → 'a)
    let id_ty = Type::fun(Type::tfree("a"), Type::tfree("a"));
    let id = Term::obs(UntrustedIdObs, id_ty);

    // Construct (untrustedId a) and (untrustedId b) where a, b are
    // distinct Free vars at type 'a.
    let a = Term::free("a", Type::tfree("a"));
    let b = Term::free("b", Type::tfree("a"));
    let e1 = Term::app(id.clone(), a);
    let e2 = Term::app(id, b);

    let thm = Thm::obs_eq::<UntrustedIdObs>(e1.clone(), e2.clone(), None).unwrap();
    assert!(thm.hyps().is_empty(), "obs_eq produces an empty-hyp Thm");
    assert_eq!(thm.concl(), &Term::eq(e1, e2));
}

// ============================================================================
// Thm::obs_true — kernel rule for direct observation truth
// ============================================================================

#[test]
fn obs_true_for_a_prop_typed_observation_succeeds_when_policy_allows() {
    use covalence_core::{ObsTrue, Type};

    #[derive(Debug)]
    struct TrueProp;
    impl ObsTrue for TrueProp {
        fn obs_true(&self, _args: &[Term], _hint: Option<&dyn covalence_core::Hint>) -> bool {
            true
        }
    }

    // expr: just `Term::obs(TrueProp, prop)`. Policy returns true → ⊢ expr.
    let expr = Term::obs(TrueProp, Type::prop());
    let thm = Thm::obs_true::<TrueProp>(expr.clone(), None).unwrap();
    assert!(thm.hyps().is_empty());
    assert_eq!(thm.concl(), &expr);
}

#[test]
fn obs_true_rejects_non_prop_observations() {
    use covalence_core::ObsTrue;

    #[derive(Debug)]
    struct BytesOracle;
    impl ObsTrue for BytesOracle {
        fn obs_true(&self, _: &[Term], _: Option<&dyn covalence_core::Hint>) -> bool {
            true
        }
    }

    // expr at type bytes — not prop, must be rejected.
    let expr = Term::obs(BytesOracle, Type::bytes());
    let result = Thm::obs_true::<BytesOracle>(expr, None);
    assert!(matches!(result, Err(covalence_core::Error::NotProp(_))));
}

#[test]
fn obs_true_passes_hint_to_policy() {
    use covalence_core::{Hint, ObsTrue, Type};
    use std::sync::Arc;
    use std::sync::Mutex;

    static SEEN_HINT: Mutex<Option<u64>> = Mutex::new(None);

    #[derive(Debug)]
    struct WithWitness;
    impl ObsTrue for WithWitness {
        fn obs_true(&self, _: &[Term], hint: Option<&dyn Hint>) -> bool {
            if let Some(h) = hint
                && let Some(w) = h.as_any().downcast_ref::<u64>()
            {
                *SEEN_HINT.lock().unwrap() = Some(*w);
                return true;
            }
            false
        }
    }

    let expr = Term::obs(WithWitness, Type::prop());
    let witness: Arc<dyn Hint> = Arc::new(42u64);
    assert!(Thm::obs_true::<WithWitness>(expr.clone(), Some(witness)).is_ok());
    assert_eq!(*SEEN_HINT.lock().unwrap(), Some(42));
}

#[test]
fn obs_true_rejects_non_obs_head() {
    use covalence_core::ObsTrue;

    #[derive(Debug)]
    struct Anything;
    impl ObsTrue for Anything {
        fn obs_true(&self, _: &[Term], _: Option<&dyn covalence_core::Hint>) -> bool {
            true
        }
    }

    // expr is just a Free var — no obs at head.
    let expr = Term::free("p", covalence_core::Type::prop());
    let result = Thm::obs_true::<Anything>(expr, None);
    assert!(matches!(result, Err(covalence_core::Error::NotObsHead(_))));
}
