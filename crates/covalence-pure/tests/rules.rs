//! Smoke-test the LF and equality rules end-to-end.

use covalence_pure::{Term, Thm, Type};

fn bytes_ty() -> Type {
    Type::bytes()
}

fn x_free() -> Term {
    Term::free("x", bytes_ty())
}

#[test]
fn refl_yields_eq() {
    let x = x_free();
    let thm = Thm::refl(x.clone()).unwrap();
    assert!(thm.hyps().is_empty());
    match thm.concl().kind() {
        covalence_pure::TermKind::Eq(a, b) => {
            assert_eq!(a, &x);
            assert_eq!(b, &x);
        }
        other => panic!("expected Eq, got {:?}", other),
    }
}

#[test]
fn assume_and_imp_intro_round_trip() {
    // φ : prop, take φ as a hypothesis, then introduce ⟹.
    let phi = Term::eq(x_free(), x_free());
    let assumed = Thm::assume(phi.clone()).unwrap();
    assert_eq!(assumed.hyps().len(), 1);
    assert!(assumed.hyps().contains(&phi));
    assert_eq!(assumed.concl(), &phi);

    let intro = assumed.imp_intro(&phi).unwrap();
    assert!(intro.hyps().is_empty());
    match intro.concl().kind() {
        covalence_pure::TermKind::Imp(a, b) => {
            assert_eq!(a, &phi);
            assert_eq!(b, &phi);
        }
        other => panic!("expected Imp, got {:?}", other),
    }
}

#[test]
fn imp_elim_combines_hyps() {
    let phi = Term::eq(x_free(), x_free());
    let psi = Term::eq(Term::free("y", bytes_ty()), Term::free("y", bytes_ty()));
    // (φ ⟹ ψ) under hypothesis (φ ⟹ ψ)
    let impl_thm = Thm::assume(Term::imp(phi.clone(), psi.clone())).unwrap();
    // φ under hypothesis φ
    let hyp_thm = Thm::assume(phi.clone()).unwrap();

    let combined = impl_thm.imp_elim(hyp_thm).unwrap();
    assert_eq!(combined.concl(), &psi);
    assert_eq!(combined.hyps().len(), 2);
}

#[test]
fn beta_conversion() {
    // (λx:bytes. x) (blob "hi")  ≡  blob "hi"
    let id = Term::abs("x", bytes_ty(), Term::bound(0));
    let arg = Term::blob(bytes::Bytes::from_static(b"hi"));
    let app = Term::app(id.clone(), arg.clone());

    let beta = Thm::beta_conv(app.clone()).unwrap();
    match beta.concl().kind() {
        covalence_pure::TermKind::Eq(lhs, rhs) => {
            assert_eq!(lhs, &app);
            assert_eq!(rhs, &arg);
        }
        other => panic!("expected Eq, got {:?}", other),
    }
}

#[test]
fn eta_conversion() {
    // λx:bytes. (f x) ≡ f when f is a Free of type (bytes ⇒ bytes)
    let f = Term::free("f", Type::fun(bytes_ty(), bytes_ty()));
    let body = Term::app(f.clone(), Term::bound(0));
    let abs = Term::abs("x", bytes_ty(), body);
    let eta = Thm::eta_conv(abs.clone()).unwrap();
    match eta.concl().kind() {
        covalence_pure::TermKind::Eq(lhs, rhs) => {
            assert_eq!(lhs, &abs);
            assert_eq!(rhs, &f);
        }
        other => panic!("expected Eq, got {:?}", other),
    }
}

#[test]
fn all_intro_then_elim_is_substitution() {
    // Generalise refl(x) over x, then instantiate at a specific blob.
    let x = x_free();
    let refl_x = Thm::refl(x).unwrap();
    let all = refl_x.all_intro("x", bytes_ty()).unwrap();
    assert!(all.hyps().is_empty());

    let lit = Term::blob(bytes::Bytes::from_static(b"hello"));
    let inst = all.all_elim(lit.clone()).unwrap();
    assert_eq!(inst.concl(), &Term::eq(lit.clone(), lit));
}

#[test]
fn all_intro_fails_when_var_in_hyps() {
    // Assume x ≡ x; can't generalise over x — it's in the hypothesis.
    let phi_x = Term::eq(x_free(), x_free());
    let thm = Thm::assume(phi_x).unwrap();
    assert!(thm.all_intro("x", bytes_ty()).is_err());
}

#[test]
fn type_of_catches_inconsistent_free_var() {
    // The same Free name with two different types should be rejected.
    let phi = Term::imp(
        Term::eq(
            Term::free("x", Type::bytes()),
            Term::free("x", Type::bytes()),
        ),
        Term::eq(
            Term::free("x", Type::tycon("bool", vec![])),
            Term::free("x", Type::tycon("bool", vec![])),
        ),
    );
    assert!(phi.type_of().is_err());
}

#[test]
fn eq_mp_basic() {
    use covalence_pure::{Term, Thm, Type};
    // ⊢ x ≡ x ⊢ x → ⊢ x  (where x : prop)
    let x = Term::free("x", Type::prop());
    let eq_thm = Thm::refl(x.clone()).unwrap(); // ⊢ x ≡ x
    let p_thm = Thm::assume(x.clone()).unwrap(); // {x} ⊢ x
    let q_thm = eq_thm.eq_mp(p_thm).unwrap();
    assert_eq!(q_thm.concl(), &x);
}

#[test]
fn eq_mp_lhs_must_match() {
    use covalence_pure::{Term, Thm, Type};
    let x = Term::free("x", Type::prop());
    let y = Term::free("y", Type::prop());
    let eq_thm = Thm::refl(x.clone()).unwrap(); // ⊢ x ≡ x
    let p_thm = Thm::assume(y).unwrap(); // {y} ⊢ y
    assert!(eq_thm.eq_mp(p_thm).is_err());
}

#[test]
fn eq_mp_requires_eq_concl() {
    use covalence_pure::{Term, Thm, Type};
    // refl on (Free x : prop) gives ⊢ x ≡ x. Then take assume(x ≡ x) — concl is
    // (x ≡ x), which IS an Eq. We need a non-Eq concl. Use ⊢ p ⟹ p.
    let p = Term::free("p", Type::prop());
    let p_thm = Thm::assume(p.clone()).unwrap();
    let imp_thm = p_thm.imp_intro(&p).unwrap(); // ⊢ p ⟹ p
    let p_thm2 = Thm::assume(p).unwrap();
    assert!(imp_thm.eq_mp(p_thm2).is_err());
}
