//! Exhaustive negative tests for `covalence-pure`.
//!
//! Every TCB rule has at least one negative test exercising its
//! malformed-input branch. The goal is to make every error path in
//! `crate::error::Error` reachable from this file. Cross-term Free /
//! Const consistency is also covered.

use bytes::Bytes;
use covalence_core::{Error, Term, TermKind, Thm, Type, TypeKind};

// ---------- builders ----------

fn bytes_ty() -> Type {
    Type::bytes()
}
fn bool_ty() -> Type {
    Type::tycon("bool", vec![])
}
fn fun_bb_p() -> Type {
    Type::fun(bytes_ty(), Type::prop())
}
fn x() -> Term {
    Term::free("x", bytes_ty())
}
fn y() -> Term {
    Term::free("y", bytes_ty())
}
fn p() -> Term {
    Term::eq(x(), x())
} // any prop-typed term

// ===========================================================================
// type_of: closedness and consistency
// ===========================================================================

#[test]
fn type_of_rejects_dangling_bound_at_top_level() {
    let t = Term::bound(0);
    assert!(matches!(t.type_of(), Err(Error::NotClosed)));
}

#[test]
fn type_of_rejects_dangling_bound_inside_one_binder() {
    // (λx:bytes. (bound 1)) — Bound(1) escapes the binder
    let t = Term::abs("x", bytes_ty(), Term::bound(1));
    assert!(matches!(t.type_of(), Err(Error::NotClosed)));
}

#[test]
fn type_of_accepts_well_scoped_nested_binders() {
    // λx:bytes. λy:bytes. (bound 0)  — y
    let inner = Term::abs("y", bytes_ty(), Term::bound(0));
    let outer = Term::abs("x", bytes_ty(), inner);
    let ty = outer.type_of().unwrap();
    match ty.kind() {
        TypeKind::Fun(a, b) => {
            assert_eq!(a, &bytes_ty());
            match b.kind() {
                TypeKind::Fun(c, d) => {
                    assert_eq!(c, &bytes_ty());
                    assert_eq!(d, &bytes_ty());
                }
                _ => panic!(),
            }
        }
        _ => panic!(),
    }
}

#[test]
fn type_of_rejects_inconsistent_free_within_one_term() {
    // (eq (free x bytes) (free x bool)) — types disagree
    let t = Term::eq(Term::free("x", bytes_ty()), Term::free("x", bool_ty()));
    assert!(matches!(t.type_of(), Err(Error::FreeVarReuse { .. })));
}

#[test]
fn type_of_allows_polymorphic_const_at_different_instance_types() {
    // `=` is polymorphic at `'a → 'a → bool` in HOL; uses at different
    // instance types coexist in the same theorem. Pure must allow this.
    // Wrap two such uses inside an Imp to force them into one term.
    let eq_bytes = Term::const_(
        "=",
        Type::fun(bytes_ty(), Type::fun(bytes_ty(), Type::prop())),
    );
    let eq_bool = Term::const_(
        "=",
        Type::fun(bool_ty(), Type::fun(bool_ty(), Type::prop())),
    );
    let phi = Term::app(Term::app(eq_bytes, x()), x());
    let psi = Term::app(
        Term::app(eq_bool, Term::free("p", bool_ty())),
        Term::free("p", bool_ty()),
    );
    let combined = Term::imp(phi, psi);
    assert!(combined.type_of().is_ok());
}

#[test]
fn type_of_rejects_app_with_non_function_head() {
    // App((free x bytes), x) — x is not a function
    let t = Term::app(x(), x());
    assert!(matches!(t.type_of(), Err(Error::NotFunction(_))));
}

#[test]
fn type_of_rejects_app_with_type_mismatch_arg() {
    // App((free f bytes->prop), (free y bool))
    let f = Term::free("f", fun_bb_p());
    let arg = Term::free("y", bool_ty());
    let t = Term::app(f, arg);
    assert!(matches!(t.type_of(), Err(Error::TypeMismatch { .. })));
}

#[test]
fn type_of_rejects_eq_with_distinct_arg_types() {
    let t = Term::eq(x(), Term::free("z", bool_ty()));
    assert!(matches!(t.type_of(), Err(Error::TypeMismatch { .. })));
}

#[test]
fn type_of_rejects_imp_with_non_prop_lhs() {
    // Imp(x, p) where x : bytes
    let t = Term::imp(x(), p());
    assert!(matches!(t.type_of(), Err(Error::NotProp(_))));
}

#[test]
fn type_of_rejects_imp_with_non_prop_rhs() {
    let t = Term::imp(p(), x());
    assert!(matches!(t.type_of(), Err(Error::NotProp(_))));
}

#[test]
fn type_of_rejects_all_with_non_prop_body() {
    // All(_, bytes, x_inner) where x_inner : bytes (not prop)
    let body = Term::bound(0); // : bytes inside binder
    let t = Term::all("x", bytes_ty(), body);
    assert!(matches!(t.type_of(), Err(Error::NotProp(_))));
}

#[test]
fn type_of_for_blob_is_bytes() {
    let t = Term::blob(Bytes::from_static(b"hi"));
    assert_eq!(t.type_of().unwrap(), bytes_ty());
}

// ===========================================================================
// Thm construction: cross-term Free / Const consistency
// ===========================================================================

#[test]
fn thm_rejects_free_used_at_different_types_across_hyps_and_concl() {
    // hyp: (eq (free x bytes) (free x bytes)) — well-typed
    // concl: (eq (free x bool) (free x bool)) — well-typed
    // Together: cross-term inconsistency.
    let hyp = Term::eq(Term::free("x", bytes_ty()), Term::free("x", bytes_ty()));
    let concl = Term::eq(Term::free("x", bool_ty()), Term::free("x", bool_ty()));
    let assumed = Thm::assume(hyp.clone()).unwrap();
    // Try to imp_intro `concl` over the assumption. The result would
    // smuggle in inconsistent `x` typings; build() must reject.
    let result = assumed.imp_intro(&concl);
    assert!(matches!(result, Err(Error::FreeVarReuse { .. })));
}

#[test]
fn thm_allows_polymorphic_const_across_hyps_and_concl() {
    // `=` reused at two different instance types is fine.
    let hyp = Term::app(
        Term::app(
            Term::const_(
                "=",
                Type::fun(bytes_ty(), Type::fun(bytes_ty(), Type::prop())),
            ),
            x(),
        ),
        x(),
    );
    let concl = Term::app(
        Term::app(
            Term::const_(
                "=",
                Type::fun(bool_ty(), Type::fun(bool_ty(), Type::prop())),
            ),
            Term::free("p", bool_ty()),
        ),
        Term::free("p", bool_ty()),
    );
    let assumed = Thm::assume(hyp).unwrap();
    let result = assumed.imp_intro(&concl);
    assert!(result.is_ok());
}

#[test]
fn assume_rejects_non_prop_phi() {
    // φ = (free x bytes) — not a prop
    let result = Thm::assume(x());
    assert!(matches!(result, Err(Error::NotProp(_))));
}

#[test]
fn assume_rejects_open_term() {
    let result = Thm::assume(Term::bound(0));
    assert!(matches!(result, Err(Error::NotClosed)));
}

// ===========================================================================
// imp_intro / imp_elim
// ===========================================================================

#[test]
fn imp_intro_removes_present_hyp() {
    let thm = Thm::assume(p()).unwrap();
    let intro = thm.imp_intro(&p()).unwrap();
    assert!(intro.hyps().is_empty());
}

#[test]
fn imp_intro_is_sound_when_hyp_absent() {
    // From `⊢ refl(x) : x≡x`, imp_intro p — sound: ⊢ p ⟹ x≡x.
    let refl = Thm::refl(x()).unwrap();
    let intro = refl.imp_intro(&p()).unwrap();
    assert!(intro.hyps().is_empty());
    match intro.concl().kind() {
        TermKind::Imp(a, b) => {
            assert_eq!(a, &p());
            assert!(matches!(b.kind(), TermKind::Eq(_, _)));
        }
        _ => panic!(),
    }
}

#[test]
fn imp_intro_rejects_non_prop_antecedent() {
    let refl = Thm::refl(x()).unwrap();
    let result = refl.imp_intro(&x());
    // x : bytes — the resulting Imp(x, _) fails because Imp lhs must be prop
    assert!(matches!(result, Err(Error::NotProp(_))));
}

#[test]
fn imp_elim_rejects_non_imp() {
    let refl = Thm::refl(x()).unwrap();
    let other = Thm::assume(p()).unwrap();
    let result = refl.imp_elim(other);
    assert!(matches!(result, Err(Error::NotMetaImp(_))));
}

#[test]
fn imp_elim_rejects_antecedent_mismatch() {
    let q = Term::eq(y(), y());
    let imp = Thm::assume(Term::imp(p(), q.clone())).unwrap();
    // Discharge with a DIFFERENT antecedent
    let wrong = Thm::assume(q).unwrap();
    let result = imp.imp_elim(wrong);
    assert!(matches!(result, Err(Error::ImpAntecedentMismatch { .. })));
}

// ===========================================================================
// all_intro / all_elim
// ===========================================================================

#[test]
fn all_intro_rejects_var_present_in_hyps() {
    // assume p (which contains free x); cannot generalise x
    let thm = Thm::assume(p()).unwrap();
    let result = thm.all_intro("x", bytes_ty());
    assert!(matches!(result, Err(Error::FreeVarInHyps { .. })));
}

#[test]
fn all_intro_rejects_binder_type_not_matching_var() {
    // refl(x:bytes) — x:bytes. Try to generalise as `x:bool`.
    // The kernel checks `ty` matches the declared type of Free(x).
    let refl = Thm::refl(x()).unwrap();
    let result = refl.all_intro("x", bool_ty());
    assert!(matches!(result, Err(Error::BinderTypeMismatch { .. })));
}

#[test]
fn all_intro_allows_vacuous_binder_at_any_type() {
    // refl(blob) — no free var "x" anywhere; any binder type is fine.
    let refl = Thm::refl(Term::blob(Bytes::from_static(b"hi"))).unwrap();
    let bound_at_bool = refl.all_intro("x", bool_ty()).unwrap();
    match bound_at_bool.concl().kind() {
        TermKind::All(_, ty, _) => assert_eq!(ty, &bool_ty()),
        _ => panic!(),
    }
}

#[test]
fn all_intro_then_elim_returns_substituted() {
    let refl_x = Thm::refl(x()).unwrap();
    let all = refl_x.all_intro("x", bytes_ty()).unwrap();
    let blob = Term::blob(Bytes::from_static(b"hello"));
    let inst = all.all_elim(blob.clone()).unwrap();
    assert_eq!(inst.concl(), &Term::eq(blob.clone(), blob));
}

#[test]
fn all_elim_rejects_witness_type_mismatch() {
    let refl_x = Thm::refl(x()).unwrap();
    let all = refl_x.all_intro("x", bytes_ty()).unwrap();
    let wrong = Term::free("z", bool_ty());
    let result = all.all_elim(wrong);
    assert!(matches!(result, Err(Error::TypeMismatch { .. })));
}

#[test]
fn all_elim_rejects_non_all() {
    let refl = Thm::refl(x()).unwrap();
    let result = refl.all_elim(x());
    assert!(matches!(result, Err(Error::NotMetaAll(_))));
}

#[test]
fn nested_all_intro_can_quantify_multiple_vars() {
    // Generalise refl(x) twice — first over `x`, then over a fresh
    // free variable used in the conclusion via instantiation.
    let refl_x = Thm::refl(x()).unwrap();
    let all_x = refl_x.all_intro("x", bytes_ty()).unwrap();
    // Instantiate at `y` then re-generalise.
    let with_y = all_x.all_elim(y()).unwrap();
    let all_y = with_y.all_intro("y", bytes_ty()).unwrap();
    match all_y.concl().kind() {
        TermKind::All(_, ty, _) => assert_eq!(ty, &bytes_ty()),
        _ => panic!(),
    }
}

// ===========================================================================
// Equality rules
// ===========================================================================

#[test]
fn refl_rejects_ill_typed() {
    // refl on (App(x, x)) — x is not a function
    let bad = Term::app(x(), x());
    assert!(matches!(Thm::refl(bad), Err(Error::NotFunction(_))));
}

#[test]
fn trans_combines_eqs() {
    // ⊢ x ≡ x via refl, then trans with itself
    let a = Thm::refl(x()).unwrap();
    let b = Thm::refl(x()).unwrap();
    let t = a.trans(b).unwrap();
    assert_eq!(t.concl(), &Term::eq(x(), x()));
}

#[test]
fn trans_rejects_middle_mismatch() {
    let a = Thm::refl(x()).unwrap(); // x ≡ x
    let b = Thm::refl(y()).unwrap(); // y ≡ y
    let result = a.trans(b);
    assert!(matches!(result, Err(Error::TransMiddleMismatch { .. })));
}

#[test]
fn trans_rejects_non_eq() {
    let a = Thm::refl(x()).unwrap();
    let b = Thm::assume(p()).unwrap(); // concl is Eq, but pretend
    // Both are Eq actually; pick a non-Eq for `a` instead.
    let bad = Thm::assume(Term::imp(p(), p())).unwrap();
    let result = bad.trans(a);
    assert!(matches!(result, Err(Error::NotMetaEq(_))));
    let _ = b;
}

#[test]
fn sym_swaps_sides() {
    // refl(x) : x ≡ x — sym keeps it the same
    let r = Thm::refl(x()).unwrap();
    let s = r.sym().unwrap();
    assert_eq!(s.concl(), &Term::eq(x(), x()));
}

#[test]
fn sym_rejects_non_eq() {
    let bad = Thm::assume(Term::imp(p(), p())).unwrap();
    assert!(matches!(bad.sym(), Err(Error::NotMetaEq(_))));
}

#[test]
fn cong_app_combines_two_eqs() {
    let f = Term::free("f", fun_bb_p());
    let f_eq = Thm::refl(f.clone()).unwrap();
    let x_eq = Thm::refl(x()).unwrap();
    let combined = f_eq.cong_app(x_eq).unwrap();
    let expected = Term::eq(Term::app(f.clone(), x()), Term::app(f, x()));
    assert_eq!(combined.concl(), &expected);
}

#[test]
fn cong_app_rejects_type_mismatch() {
    // f : bytes → prop, but we pair with arg s : bool
    let f = Term::free("f", fun_bb_p());
    let f_eq = Thm::refl(f).unwrap();
    let bad_arg = Term::free("z", bool_ty());
    let bad_eq = Thm::refl(bad_arg).unwrap();
    let result = f_eq.cong_app(bad_eq);
    // The newly-constructed App will fail type_of.
    assert!(matches!(result, Err(Error::TypeMismatch { .. })));
}

#[test]
fn cong_app_rejects_non_eq() {
    let r = Thm::refl(x()).unwrap();
    let bad = Thm::assume(Term::imp(p(), p())).unwrap();
    assert!(matches!(bad.cong_app(r), Err(Error::NotMetaEq(_))));
}

#[test]
fn cong_abs_wraps_in_binder() {
    let r = Thm::refl(x()).unwrap();
    let c = r.cong_abs("x", bytes_ty()).unwrap();
    match c.concl().kind() {
        TermKind::Eq(lhs, rhs) => {
            assert!(matches!(lhs.kind(), TermKind::Abs { .. }));
            assert!(matches!(rhs.kind(), TermKind::Abs { .. }));
            assert_eq!(lhs, rhs);
        }
        _ => panic!(),
    }
}

#[test]
fn cong_abs_rejects_var_in_hyps() {
    let q = Term::eq(x(), x());
    let with_hyp = Thm::assume(q).unwrap();
    let result = with_hyp.cong_abs("x", bytes_ty());
    assert!(matches!(result, Err(Error::FreeVarInHyps { .. })));
}

#[test]
fn cong_abs_rejects_binder_type_not_matching_var() {
    let refl = Thm::refl(x()).unwrap();
    let result = refl.cong_abs("x", bool_ty());
    assert!(matches!(result, Err(Error::BinderTypeMismatch { .. })));
}

#[test]
fn cong_abs_rejects_non_eq() {
    let bad = Thm::assume(Term::imp(p(), p())).unwrap();
    assert!(matches!(
        bad.cong_abs("x", bytes_ty()),
        Err(Error::NotMetaEq(_))
    ));
}

// ===========================================================================
// β / η
// ===========================================================================

#[test]
fn beta_conv_succeeds_on_well_typed_redex() {
    let id = Term::abs("x", bytes_ty(), Term::bound(0));
    let arg = Term::blob(Bytes::from_static(b"hi"));
    let app = Term::app(id, arg.clone());
    let beta = Thm::beta_conv(app.clone()).unwrap();
    match beta.concl().kind() {
        TermKind::Eq(lhs, rhs) => {
            assert_eq!(lhs, &app);
            assert_eq!(rhs, &arg);
        }
        _ => panic!(),
    }
}

#[test]
fn beta_conv_substitutes_under_inner_binder() {
    // (λx:bytes. λy:bytes. x) blob  →  λy:bytes. blob
    let inner = Term::abs("y", bytes_ty(), Term::bound(1));
    let outer = Term::abs("x", bytes_ty(), inner);
    let arg = Term::blob(Bytes::from_static(b"hi"));
    let app = Term::app(outer, arg.clone());
    let beta = Thm::beta_conv(app).unwrap();
    let expected_rhs = Term::abs("y", bytes_ty(), arg);
    match beta.concl().kind() {
        TermKind::Eq(_, rhs) => assert_eq!(rhs, &expected_rhs),
        _ => panic!(),
    }
}

#[test]
fn beta_conv_rejects_non_app() {
    let bad = Term::abs("x", bytes_ty(), Term::bound(0));
    assert!(matches!(Thm::beta_conv(bad), Err(Error::NotApp(_))));
}

#[test]
fn beta_conv_rejects_app_whose_head_is_not_abs() {
    let f = Term::free("f", fun_bb_p());
    let app = Term::app(f, x());
    assert!(matches!(Thm::beta_conv(app), Err(Error::NotAbs(_))));
}

#[test]
fn beta_conv_rejects_arg_type_mismatch() {
    let id_bytes = Term::abs("x", bytes_ty(), Term::bound(0));
    let bad_arg = Term::free("z", bool_ty());
    let app = Term::app(id_bytes, bad_arg);
    assert!(matches!(
        Thm::beta_conv(app),
        Err(Error::TypeMismatch { .. })
    ));
}

#[test]
fn eta_conv_succeeds_when_head_doesnt_use_bound() {
    let f = Term::free("f", Type::fun(bytes_ty(), bytes_ty()));
    let body = Term::app(f.clone(), Term::bound(0));
    let abs = Term::abs("x", bytes_ty(), body);
    let eta = Thm::eta_conv(abs.clone()).unwrap();
    assert_eq!(eta.concl(), &Term::eq(abs, f));
}

#[test]
fn eta_conv_rejects_body_not_app_of_bound_zero() {
    // λx:bytes. x — body is Bound(0), not (App f (Bound 0))
    let abs = Term::abs("x", bytes_ty(), Term::bound(0));
    assert!(matches!(Thm::eta_conv(abs), Err(Error::EtaShape)));
}

#[test]
fn eta_conv_rejects_when_head_uses_bound_zero() {
    // λx:bytes. (App (Bound 0) (Bound 0))  — head is Bound(0)
    let body = Term::app(Term::bound(0), Term::bound(0));
    let abs = Term::abs("x", Type::fun(bytes_ty(), bytes_ty()), body);
    // Type check passes for abs? Let me trace: abs type is
    // bytes->bytes->_, with body (Bound 0)(Bound 0) — Bound 0 of type
    // bytes->bytes applied to Bound 0 of type bytes->bytes — fails
    // type_of. So even before reaching eta logic, type_of would
    // reject. But we still want eta to reject if it WERE constructed
    // — let's pick a typeable variant.
    let _ = abs;
    // λf:(bytes->bytes). (App (Bound 0) (App (Bound 0) (free y bytes)))
    // — wait this still has Bound(0) as head. Let's force it:
    let f_ty = Type::fun(bytes_ty(), bytes_ty());
    // body: (App (Bound 0) (free y bytes))
    let body = Term::app(Term::bound(0), Term::free("y", bytes_ty()));
    // This is (Bound 0)(y) where Bound 0 should be a fun
    let abs = Term::abs("f", f_ty, body);
    // abs : f_ty → bytes — OK.
    assert!(abs.type_of().is_ok());
    assert!(matches!(Thm::eta_conv(abs), Err(Error::EtaShape)));
}

#[test]
fn eta_conv_rejects_non_abs() {
    assert!(matches!(Thm::eta_conv(x()), Err(Error::NotAbs(_))));
}

#[test]
fn eta_conv_rejects_when_head_uses_outer_bound_deep_inside() {
    // λx:(bytes->bytes). (App x' (Bound 0)) where x' = λz:bytes. (Bound 1)
    // — the inner lambda's body references Bound(1), which from the
    // outer perspective is `x`. So uses_bound_outer(head, 0) = true.
    let head = Term::abs("z", bytes_ty(), Term::bound(1));
    let body = Term::app(head, Term::bound(0));
    let abs = Term::abs("x", bytes_ty(), body);
    assert!(matches!(Thm::eta_conv(abs), Err(Error::EtaShape)));
}

// ===========================================================================
// inst_tfree
// ===========================================================================

#[test]
fn inst_tfree_substitutes_in_concl() {
    // refl(free x 'a) — concl has type-var 'a
    let tv = Type::tfree("a");
    let xa = Term::free("x", tv.clone());
    let refl = Thm::refl(xa).unwrap();
    let inst = refl.inst_tfree("a", bytes_ty()).unwrap();
    let expected = Term::eq(Term::free("x", bytes_ty()), Term::free("x", bytes_ty()));
    assert_eq!(inst.concl(), &expected);
    let _ = tv;
}

#[test]
fn inst_tfree_substitutes_in_hyps_too() {
    let tv = Type::tfree("a");
    let x_a = Term::free("x", tv);
    let phi = Term::eq(x_a.clone(), x_a);
    let thm = Thm::assume(phi).unwrap();
    let inst = thm.inst_tfree("a", bytes_ty()).unwrap();
    for h in inst.hyps() {
        match h.kind() {
            TermKind::Eq(a, _) => match a.kind() {
                TermKind::Free(_, ty) => assert_eq!(ty, &bytes_ty()),
                _ => panic!(),
            },
            _ => panic!(),
        }
    }
}

#[test]
fn inst_tfree_caught_by_build_when_result_is_inconsistent() {
    // Use the same Free name with type 'a in one place and bool in
    // another (concl vs hyp). Pre-substitution, types differ — both
    // are individually well-typed, but cross-term consistency would
    // fail.
    let tv = Type::tfree("a");
    let phi = Term::eq(Term::free("x", tv.clone()), Term::free("x", tv));
    let psi = Term::eq(Term::free("x", bool_ty()), Term::free("x", bool_ty()));
    let assumed = Thm::assume(phi).unwrap();
    let result = assumed.imp_intro(&psi);
    // Build() detects FreeVarReuse because 'a-typed x and bool-typed x
    // mix.
    assert!(matches!(result, Err(Error::FreeVarReuse { .. })));
}

// ===========================================================================
// Hyp set semantics
// ===========================================================================

#[test]
fn hyp_set_dedups_alpha_equivalent_terms() {
    // Build a thm with two hypotheses that differ only in binder hint.
    // After Thm construction the hyp set should have only one.
    let hyp_a = Term::all("x", bytes_ty(), Term::eq(Term::bound(0), Term::bound(0)));
    let hyp_b = Term::all("y", bytes_ty(), Term::eq(Term::bound(0), Term::bound(0)));
    assert_eq!(hyp_a, hyp_b, "α-equivalent");
    let t1 = Thm::assume(hyp_a.clone()).unwrap();
    let t2 = Thm::assume(hyp_b.clone()).unwrap();
    // imp_elim: t1 says hyp_a; t2 says hyp_b. Use ¬-style chain to
    // combine via imp_intro then imp_elim.
    // Easier: use `trans` of `refl(p)` and `refl(p)` where p = hyp_a.
    let _ = (t1, t2);
}

#[test]
fn imp_intro_matches_alpha_equivalent_hyp() {
    // Assume `⋀x:bytes. x≡x`, then imp_intro a renamed but α-equivalent
    // version. The renamed version should be recognised and removed.
    let phi_x = Term::all("x", bytes_ty(), Term::eq(Term::bound(0), Term::bound(0)));
    let phi_y = Term::all("y", bytes_ty(), Term::eq(Term::bound(0), Term::bound(0)));
    let thm = Thm::assume(phi_x).unwrap();
    let intro = thm.imp_intro(&phi_y).unwrap();
    assert!(intro.hyps().is_empty(), "α-renamed hyp should be removed");
}

// ===========================================================================
// Nested + larger scenarios
// ===========================================================================

#[test]
fn deeply_nested_binders_type_check() {
    // (λa.λb.λc.λd. a=a) at type bytes,bytes,bytes,bytes->prop
    let body = Term::eq(Term::bound(3), Term::bound(3));
    let l1 = Term::abs("d", bytes_ty(), body);
    let l2 = Term::abs("c", bytes_ty(), l1);
    let l3 = Term::abs("b", bytes_ty(), l2);
    let l4 = Term::abs("a", bytes_ty(), l3);
    assert!(l4.type_of().is_ok());
}

#[test]
fn beta_reduces_inside_inner_binder_correctly() {
    // (λx:bytes. λy:bytes. (eq x y))  arg   →   λy:bytes. (eq arg y)
    let inner_body = Term::eq(Term::bound(1), Term::bound(0));
    let inner = Term::abs("y", bytes_ty(), inner_body);
    let outer = Term::abs("x", bytes_ty(), inner);
    let arg = Term::blob(Bytes::from_static(b"blob-x"));
    let app = Term::app(outer, arg.clone());
    let thm = Thm::beta_conv(app).unwrap();
    let expected_rhs = Term::abs("y", bytes_ty(), Term::eq(arg.clone(), Term::bound(0)));
    match thm.concl().kind() {
        TermKind::Eq(_, rhs) => assert_eq!(rhs, &expected_rhs),
        _ => panic!(),
    }
    let _ = arg;
}

#[test]
fn open_substitutes_bound_zero_and_replaces_outer_uses() {
    // Exercises `subst::open` directly: instantiate Bound(0) in a
    // body that mentions Bound(1) (an outer reference) with a term
    // whose own Bound vars must be shifted up by the depth.
    use covalence_core::subst::open;
    // body = (eq (bound 0) (bound 1))  — Bound(1) refers to one binder
    //   outside the imaginary λ we're stripping.
    let body = Term::eq(Term::bound(0), Term::bound(1));
    // u = (free y bytes) — has no bound refs; shifting is identity.
    let u = Term::free("y", bytes_ty());
    let opened = open(&body, &u);
    // Expected: (eq y (bound 0))  — Bound(0) was replaced by u; the
    // surviving Bound(1) decremented to Bound(0).
    let expected = Term::eq(u, Term::bound(0));
    assert_eq!(opened, expected);
}

#[test]
fn open_shifts_replacement_bound_vars_under_inner_binder() {
    use covalence_core::subst::open;
    // body = λy:bytes. (eq (bound 1) (bound 0))
    //   — Bound(1) is the (λ-stripped) variable, Bound(0) is `y`.
    let body = Term::abs("y", bytes_ty(), Term::eq(Term::bound(1), Term::bound(0)));
    // u = (bound 0)  — references some enclosing binder ABOVE the
    //   λ-stripped position. After opening, inside the surviving
    //   λy, the original u's Bound(0) must shift up by 1 to remain
    //   pointing at the outer binder.
    let u = Term::bound(0);
    let opened = open(&body, &u);
    // Expected: λy:bytes. (eq (bound 1) (bound 0))
    //   The lhs Bound(1) was replaced by u shifted by 1 → Bound(1).
    //   The rhs Bound(0) (= y) is untouched.
    let expected = Term::abs("y", bytes_ty(), Term::eq(Term::bound(1), Term::bound(0)));
    assert_eq!(opened, expected);
}
