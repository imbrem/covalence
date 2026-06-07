//! Tests for `Thm::define` and `Def`.
//!
//! Each `define` call allocates a fresh `Arc<Term>` for the body, so
//! distinct calls — even with the same name and the same body —
//! produce distinct `Def`s. The kernel never reuses a `Def` identity,
//! so users cannot `trans + sym` two equations for "the same name"
//! into `⊢ body1 ≡ body2`.

use bytes::Bytes;
use covalence_pure::{Term, TermKind, Thm, Type};

#[test]
fn define_emits_unfolding_equation() {
    // id := λx:bytes. x. Concl is `⊢ Def(id) ≡ λx:bytes. x`.
    let body = Term::abs("x", Type::bytes(), Term::bound(0));
    let thm = Thm::define("id", body.clone()).unwrap();
    assert!(thm.hyps().is_empty(), "define has no hypotheses");
    match thm.concl().kind() {
        TermKind::Eq(lhs, rhs) => {
            assert!(matches!(lhs.kind(), TermKind::Def(_)));
            assert_eq!(rhs, &body);
        }
        other => panic!("expected Eq, got {:?}", other),
    }
}

#[test]
fn define_typed_correctly() {
    // id : bytes → bytes
    let body = Term::abs("x", Type::bytes(), Term::bound(0));
    let thm = Thm::define("id", body).unwrap();
    let expected = Type::fun(Type::bytes(), Type::bytes());
    match thm.concl().kind() {
        TermKind::Eq(lhs, _) => assert_eq!(lhs.type_of().unwrap(), expected),
        _ => panic!(),
    }
}

#[test]
fn distinct_define_calls_yield_distinct_defs() {
    // Two separate `define("c", body)` calls produce two DISTINCT
    // `Def`s, even with the same body shape. So the resulting Thms'
    // LHSs (which wrap the Defs) are unequal.
    let body = Term::abs("x", Type::bytes(), Term::bound(0));
    let thm1 = Thm::define("id", body.clone()).unwrap();
    let thm2 = Thm::define("id", body).unwrap();
    let lhs1 = match thm1.concl().kind() {
        TermKind::Eq(l, _) => l,
        _ => panic!(),
    };
    let lhs2 = match thm2.concl().kind() {
        TermKind::Eq(l, _) => l,
        _ => panic!(),
    };
    assert_ne!(
        lhs1, lhs2,
        "distinct define calls yield distinct Def identities"
    );
}

#[test]
fn cannot_trans_distinct_defs_to_equate_bodies() {
    // The whole soundness story: if we naively allowed two defines
    // with the same name to be treated as equal, then
    //   define("c", body1) → ⊢ c ≡ body1
    //   define("c", body2) → ⊢ c ≡ body2
    //   trans (sym (1)) (2) → ⊢ body1 ≡ body2  -- BAD
    // Because each define yields a DISTINCT Def, the two LHSs are
    // not equal, so trans's middle-term check refuses.
    let body1 = Term::blob(Bytes::from_static(b"a"));
    let body2 = Term::blob(Bytes::from_static(b"b"));
    let thm1 = Thm::define("c", body1.clone()).unwrap();
    let thm2 = Thm::define("c", body2.clone()).unwrap();

    // sym(thm1) gives ⊢ body1 ≡ Def1
    let thm1_sym = thm1.sym().unwrap();
    // trans(thm1_sym, thm2) would try to match Def1 with Def2 as the
    // middle term. They're distinct, so trans must refuse.
    let result = thm1_sym.trans(thm2);
    assert!(
        result.is_err(),
        "trans must refuse: the two Defs are distinct symbols"
    );
}

#[test]
fn define_can_be_used_via_beta() {
    // ⊢ id ≡ λx:bytes. x, then ⊢ id "hi" ≡ (λx:bytes. x) "hi" by
    // cong_app + refl, then β to get ⊢ id "hi" ≡ "hi". But "id" here
    // is the Def, opaque to β. So β only applies after we've used the
    // unfolding equation. Let's just verify the unfolding equation
    // can be used in a trans chain.
    let body = Term::abs("x", Type::bytes(), Term::bound(0));
    let unfold = Thm::define("id", body.clone()).unwrap();

    // Construct (Def id)("hi") and (λx:bytes. x)("hi"), and check
    // that cong_app on `unfold` + refl("hi") gives us their equality.
    let id_term = match unfold.concl().kind() {
        TermKind::Eq(lhs, _) => lhs.clone(),
        _ => panic!(),
    };
    let hi = Term::blob(Bytes::from_static(b"hi"));
    let refl_hi = Thm::refl(hi.clone()).unwrap();
    let cong = unfold.cong_app(refl_hi).unwrap();
    // cong : Def("id")("hi") ≡ (λx:bytes. x)("hi")
    match cong.concl().kind() {
        TermKind::Eq(lhs, rhs) => {
            assert_eq!(lhs, &Term::app(id_term, hi.clone()));
            // rhs is (λx:bytes. x)("hi"); β would reduce to "hi"
            let beta = Thm::beta_conv(rhs.clone()).unwrap();
            match beta.concl().kind() {
                TermKind::Eq(_, beta_rhs) => assert_eq!(beta_rhs, &hi),
                _ => panic!(),
            }
        }
        _ => panic!(),
    }
}

#[test]
fn def_propagates_through_inst_tfree() {
    // Polymorphic body: id := λx:'a. x. After inst_tfree('a, bytes),
    // the body becomes λx:bytes. x — a NEW Def. The original Thm and
    // the substituted Thm refer to *different* defined constants
    // (one per Pure type).
    let body = Term::abs("x", Type::tfree("a"), Term::bound(0));
    let thm = Thm::define("id", body).unwrap();
    let inst = thm.inst_tfree("a", Type::bytes()).unwrap();
    // Both Thms have an empty hyps and an Eq concl.
    assert!(inst.hyps().is_empty());
    match inst.concl().kind() {
        TermKind::Eq(lhs, rhs) => {
            assert!(matches!(lhs.kind(), TermKind::Def(_)));
            assert_eq!(rhs, &Term::abs("x", Type::bytes(), Term::bound(0)));
        }
        _ => panic!(),
    }
}
