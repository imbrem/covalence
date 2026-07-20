//! End-to-end battery for the **ACL2-flavoured dialect**
//! ([`covalence_lisp::acl2`]) — Little-Schemer-flavoured programs, `defun`
//! admissibility, and the honest `defthm` story.
//!
//! # The contract these tests pin
//!
//! - **Every value assertion checks the backing kernel theorem**: the printed
//!   value is the RHS of `out.thm`'s equational conclusion, and the theorem's
//!   hypotheses are exactly the `defun` equations used (empty for closed
//!   primitive/arithmetic programs, non-empty when user recursion unfolds).
//! - **`defthm` never fakes**: a ground decidable goal mints a real theorem
//!   (retrievable via [`Acl2Session::theorem`]); a universally quantified
//!   goal is *rejected* with a message naming induction as the missing piece;
//!   a false ground goal is rejected as refuted.
//! - **`defun` admissibility is checked**: non-structural recursion is
//!   rejected with a clear message (and no definition is installed).
#![cfg(feature = "hol")]

use covalence_init::init::acl2::count::acl2_count_natp_fact;
use covalence_kernel_lisp::{CoreExpr, Datum};
use covalence_lisp::acl2::{
    Acl2Outcome, Acl2Session, Acl2ValueKind, replay_acl2_append_execution,
    replay_acl2_append_existence, replay_acl2_append_graph_adequacy,
};
use covalence_lisp::carrier::Acl2Carrier;
use covalence_lisp::frontend::CoreAtom;
use covalence_lisp::reader::read_one;
use covalence_sexp::AbstractSExpr;

fn session() -> Acl2Session {
    Acl2Session::new().expect("session")
}

#[test]
fn stale_generation_induction_fact_is_rejected_at_registration() {
    let mut s = session();
    let fact = acl2_count_natp_fact(s.induction_env()).expect("current-generation count fact");
    s.add_induction_lemma(fact.clone())
        .expect("a fact checked in the current generation is accepted");

    s.eval_cell("(defun generation-step (x) x)")
        .expect("admit a deep definition and advance the ACL2 generation");
    let err = s
        .add_induction_lemma(fact)
        .expect_err("the old generation's checked fact must fail closed");
    assert!(
        err.to_string().contains("current ACL2 generation"),
        "registration should diagnose the generation mismatch: {err}"
    );
}

/// Reduce `src` and assert the honesty invariant: the value is the RHS of the
/// theorem's equational conclusion. Returns the outcome for further checks.
fn eval_checked(s: &Acl2Session, src: &str) -> Acl2Outcome {
    let form = read_one(src).expect("parse");
    let out = s.reduce(&form).expect("reduce");
    let (_, rhs) = out
        .thm
        .concl()
        .as_eq()
        .expect("conclusion must be an equation `input = value`");
    assert_eq!(rhs, &out.value, "the value must be the theorem's RHS");
    out
}

/// [`eval_checked`] + assert the rendered value and that the theorem is
/// hypothesis-free (closed, definition-free programs).
fn eval_closed(s: &Acl2Session, src: &str, want: &str) {
    let out = eval_checked(s, src);
    assert!(
        out.thm.hyps().is_empty(),
        "`{src}` must be hyps-free, got {:?}",
        out.thm.hyps()
    );
    assert_eq!(s.render(&out), want, "value mismatch for `{src}`");
}

// ---- Little-Schemer app: defun + recursion --------------------------------

const APP: &str = "(defun app (x y) (if (consp x) (cons (car x) (app (cdr x) y)) y))";

#[test]
fn relational_append_agrees_with_conservatively_admitted_acl2_append() {
    let s = session();
    let carrier = Acl2Carrier::new().unwrap();
    let left = carrier.quote(&read_one("(a b)").unwrap()).unwrap();
    let right = carrier.quote(&read_one("(c d)").unwrap()).unwrap();
    let expected = carrier.quote(&read_one("(a b c d)").unwrap()).unwrap();

    let evidence = replay_acl2_append_execution(s.induction_env(), left, right, 16).unwrap();
    assert_eq!(evidence.execution.value, expected);
    assert!(evidence.execution.reduction.hyps().is_empty());
    assert!(evidence.model_agreement.hyps().is_empty());
    assert_eq!(
        evidence.model_agreement.concl().as_eq().unwrap().1,
        &evidence.execution.value
    );
}

#[test]
fn relational_append_exists_for_every_acl2_object() {
    let s = session();
    let existence = replay_acl2_append_existence(s.induction_env()).unwrap();
    assert!(existence.theorem.hyps().is_empty());
}

#[test]
fn reified_append_evaluation_exists_and_is_unique() {
    let s = session();
    let adequacy = replay_acl2_append_graph_adequacy(s.induction_env()).unwrap();
    assert!(adequacy.existence.theorem.hyps().is_empty());
    assert!(adequacy.uniqueness.theorem.hyps().is_empty());
}

#[test]
fn defun_app_and_apply() {
    let mut s = session();
    // A defun event returns the function name (the ACL2 convention).
    assert_eq!(s.eval_cell(APP).unwrap(), "app");
    // Apply it: value is right, AND the theorem carries the defun equation
    // as a hypothesis (defun-as-hypothesis recursion, never an axiom).
    let out = eval_checked(&s, "(app (quote (a b)) (quote (c)))");
    assert_eq!(s.render(&out), "(a b c)");
    assert!(
        !out.thm.hyps().is_empty(),
        "a recursive call must ride on the defun hypothesis"
    );
    assert_eq!(out.kind, Acl2ValueKind::Data);
}

#[test]
fn admitted_definition_reuses_the_shared_partial_core() {
    let mut s = session();
    s.eval_cell(APP).unwrap();
    let definition = s
        .definition("app")
        .expect("admitted definition retains its shared core");
    assert_eq!(definition.core.name, "app");
    assert_eq!(definition.core.parameters, ["x", "y"]);
    assert!(definition.core.rest.is_none());
    assert!(matches!(&definition.core.body, CoreExpr::If { .. }));

    let evaluation = s
        .operational_evidence(&read_one("(app (quote (a b)) (quote (c)))").unwrap())
        .unwrap();
    assert_eq!(
        evaluation.value.as_datum(),
        Some(Datum::list([
            Datum::Atom(CoreAtom::symbol("a")),
            Datum::Atom(CoreAtom::symbol("b")),
            Datum::Atom(CoreAtom::symbol("c")),
        ])),
        "ACL2 admission and generic partial execution must share the lowered program"
    );
    assert!(
        evaluation.trace.steps() > 0,
        "the shared core result must retain a nontrivial checked execution"
    );
    s.eval_cell(
        "(defun app-core (x y)
           (if (endp x) y (cons (car x) (app-core (cdr x) y))))",
    )
    .unwrap();
    let app = s
        .definition("app-core")
        .expect("recursive ACL2 definition retains its normalized shared core");
    assert!(matches!(&app.core.body, CoreExpr::If { .. }));
    let evaluation = s
        .operational_evidence(&read_one("(app-core (quote (a b)) (quote (c)))").unwrap())
        .unwrap();
    assert_eq!(
        evaluation.value.as_datum(),
        Some(Datum::list([
            Datum::Atom(CoreAtom::symbol("a")),
            Datum::Atom(CoreAtom::symbol("b")),
            Datum::Atom(CoreAtom::symbol("c")),
        ])),
        "ACL2 ENDP normalization must survive into generic partial execution"
    );
    assert!(
        evaluation.trace.steps() > 0,
        "the normalized recursive core must retain checked execution evidence"
    );

    let form = read_one("(app (quote (a b)) (quote (c)))").unwrap();
    let direct = s.reduce(&form).unwrap();
    let hol = s.operational_hol_evidence(&form).unwrap();
    assert_eq!(hol.value, direct.value);
    assert_eq!(
        hol.equality.hyps().len(),
        1,
        "concrete transport must retain the recursive definition equation"
    );

    s.reset();
    assert!(
        s.operational_evidence(&read_one("(app (quote (a b)) (quote (c)))").unwrap())
            .is_err(),
        "reset must clear the shared operational definition generation too"
    );
}

#[test]
fn defun_persists_across_cells() {
    let mut s = session();
    s.eval_cell(APP).unwrap();
    assert_eq!(s.eval_cell("(app (quote ()) (quote (q)))").unwrap(), "(q)");
    assert_eq!(
        s.eval_cell("(app (quote (a b)) (app (quote (c)) (quote (d))))")
            .unwrap(),
        "(a b c d)"
    );
}

#[test]
fn defun_accepts_acl2_doc_string_and_declarations() {
    let mut s = session();
    assert_eq!(
        s.eval_cell(
            r#"(defun app-declared (x y)
                   "Append X to Y."
                   (declare (xargs :measure (acl2-count x)
                                    :guard (true-listp x)))
                   (if (consp x)
                       (cons (car x) (app-declared (cdr x) y))
                     y))"#
        )
        .unwrap(),
        "app-declared"
    );
    let out = eval_checked(&s, "(app-declared (quote (a b)) (quote (c)))");
    assert_eq!(s.render(&out), "(a b c)");
    assert!(!out.thm.hyps().is_empty());
}

#[test]
fn defun_rejects_missing_or_multiple_bodies_after_declarations() {
    let mut s = session();
    for src in [
        "(defun no-body (x) (declare (xargs :guard t)))",
        "(defun two-bodies (x) (declare (xargs :guard t)) x x)",
    ] {
        let err = s.eval_cell(src).unwrap_err();
        assert!(err.to_string().contains("body"), "got: {err}");
    }
    assert!(!s.defs().contains("no-body"));
    assert!(!s.defs().contains("two-bodies"));
}

#[test]
fn disabled_rule_event_aliases_use_the_same_honest_paths() {
    let mut s = session();
    assert_eq!(s.eval_cell("(defund identity (x) x)").unwrap(), "identity");
    assert!(s.defs().contains("identity"));

    assert_eq!(
        s.eval_cell("(defthmd four-disabled (equal (+ 2 2) 4))")
            .unwrap(),
        "four-disabled"
    );
    assert!(s.theorem("four-disabled").is_some());
}

#[test]
fn composed_car_cdr_accessors_expand_and_count_as_structural_descent() {
    let mut s = session();
    eval_closed(&s, "(cadr (quote (a b c)))", "b");
    eval_closed(&s, "(cddr (quote (a b c)))", "(c)");

    assert_eq!(
        s.eval_cell(
            "(defun every-other (x) \
               (if (consp x) (cons (car x) (every-other (cddr x))) x))"
        )
        .unwrap(),
        "every-other"
    );
    assert_eq!(
        s.eval_cell("(every-other (quote (a b c d)))").unwrap(),
        "(a c)"
    );
}

// ---- ACL2 primitive spellings ---------------------------------------------

#[test]
fn acl2_primitives() {
    let s = session();
    eval_closed(&s, "(car (quote (a b)))", "a");
    eval_closed(&s, "(cdr (quote (a b c)))", "(b c)");
    eval_closed(&s, "(cons (quote a) (quote (b)))", "(a b)");
    eval_closed(&s, "(consp (quote (a)))", "t");
    eval_closed(&s, "(consp (quote a))", "nil");
    eval_closed(&s, "(atom (quote a))", "t");
    eval_closed(&s, "(atom (quote (a)))", "nil");
    eval_closed(&s, "(endp (quote ()))", "t");
    eval_closed(&s, "(endp (quote (a)))", "nil");
    eval_closed(&s, "(if (consp (quote (a))) (quote yes) (quote no))", "yes");
    eval_closed(&s, "(equal (quote a) (quote a))", "t");
    eval_closed(&s, "(equal (quote a) (quote b))", "nil");
}

#[test]
fn equal_on_equal_lists_is_proved_structurally() {
    // `equal` on composite values succeeds exactly when the reduced values
    // coincide — backed by a genuine trans/sym + eqt_intro theorem.
    let s = session();
    eval_closed(&s, "(equal (cons (quote a) (quote ())) (quote (a)))", "t");
    // Disequality of composites is NOT decidable in this slice: clean error.
    let form = read_one("(equal (quote (a)) (quote (b)))").unwrap();
    assert!(s.reduce(&form).is_err());
}

#[test]
fn cond_is_rejected() {
    // The ACL2 slice is ternary-`if` only.
    let mut s = session();
    let err = s
        .eval_cell("(cond ((consp (quote (a))) (quote y)) (t (quote n)))")
        .unwrap_err();
    assert!(err.to_string().contains("if"), "got: {err}");
}

// ---- ground integer arithmetic --------------------------------------------

#[test]
fn ground_arithmetic() {
    let s = session();
    eval_closed(&s, "(+ 2 2)", "4");
    eval_closed(&s, "(- 5 3)", "2");
    eval_closed(&s, "(* 3 4)", "12");
    eval_closed(&s, "(+ 1 (* 2 3))", "7");
    eval_closed(&s, "(- 2 5)", "-3");
}

#[test]
fn ground_arithmetic_propositions() {
    let s = session();
    eval_closed(&s, "(<= 2 5)", "t");
    eval_closed(&s, "(<= 5 2)", "nil");
    eval_closed(&s, "(= 4 4)", "t");
    eval_closed(&s, "(= 4 5)", "nil");
    eval_closed(&s, "(equal (+ 2 2) 4)", "t");
    eval_closed(&s, "(zp 0)", "t");
    eval_closed(&s, "(zp 3)", "nil");
    eval_closed(&s, "(natp 3)", "t");
    eval_closed(&s, "(natp (- 2 5))", "nil");
}

#[test]
fn integers_outside_arithmetic_are_cleanly_rejected() {
    // Integers in list structure await the value semantics' integer backend;
    // the error must be clean, not a stuck term or a fake value.
    let s = session();
    let form = read_one("(cons 1 (quote ()))").unwrap();
    let err = s.reduce(&form).unwrap_err();
    assert!(err.to_string().contains("integer"), "got: {err}");
}

// ---- defthm: ground success -----------------------------------------------

/// **The transported `defthm four` gate** (the demo wiring of init's S3
/// gate): a ground arithmetic `(equal LHS RHS)` goes THROUGH the reified
/// ladder — the stored theorem is the transported base-HOL model equation
/// `⊢ aplus (aint 2) (aint 2) = aint 4` (asserted exactly, hyps-free), and
/// the recorded provenance carries the hypothesis-free certificate
/// `⊢ Derivable_ACL2 ⌜(EQUAL (BINARY-+ '2 '2) '4)⌝` (asserted exactly).
#[test]
fn defthm_ground_arithmetic_transports_via_certificate() {
    use covalence_init::init::acl2::derivable::{derivable, ground_env};
    use covalence_init::init::ext::TermExt;
    use covalence_lisp::acl2::Acl2Proof;

    let mut s = session();
    assert_eq!(
        s.eval_cell("(defthm four (equal (+ 2 2) 4))").unwrap(),
        "four"
    );
    let entry = s.theorem_entry("four").expect("stored theorem");
    assert!(
        entry.thm.hyps().is_empty(),
        "the transported model equation must be hyps-free"
    );

    // The exact final statement: ⊢ aplus (aint 2) (aint 2) = aint 4.
    let e = ground_env().expect("ground env");
    let tm = &*e.tm;
    let aint = |i: i128| tm.th.aint_at(&covalence_hol_eval::mk_int(i)).unwrap();
    let expected = tm
        .pr
        .plus
        .clone()
        .apply(aint(2))
        .unwrap()
        .apply(aint(2))
        .unwrap()
        .equals(aint(4))
        .unwrap();
    assert_eq!(entry.thm.concl(), &expected, "the model equation, exactly");

    // The path built a reified certificate, with the exact
    // `Derivable_ACL2` statement, itself hypothesis-free.
    let Acl2Proof::Certificate { derivation } = &entry.proof else {
        panic!("defthm four must take the certificate path");
    };
    assert!(derivation.hyps().is_empty(), "certificate must be closed");
    let q2 = tm.quote(&aint(2)).unwrap();
    let q4 = tm.quote(&aint(4)).unwrap();
    let phi = tm.mk_equal(&tm.mk_plus(&q2, &q2).unwrap(), &q4).unwrap();
    assert_eq!(derivation.concl(), &derivable(&e, &phi).unwrap());
}

/// A structural (list) goal in the fragment also transports: the stored
/// theorem is the base-HOL model equation
/// `⊢ car (acons (asym "a") (acons (asym "b") anil)) = asym "a"`.
#[test]
fn defthm_structural_goal_transports_via_certificate() {
    use covalence_init::init::acl2::derivable::ground_env;
    use covalence_init::init::ext::TermExt;
    use covalence_lisp::acl2::Acl2Proof;

    let mut s = session();
    assert_eq!(
        s.eval_cell("(defthm car-ab (equal (car (quote (a b))) (quote a)))")
            .unwrap(),
        "car-ab"
    );
    let entry = s.theorem_entry("car-ab").expect("stored theorem");
    assert!(matches!(entry.proof, Acl2Proof::Certificate { .. }));
    assert!(entry.thm.hyps().is_empty());

    let e = ground_env().expect("ground env");
    let tm = &*e.tm;
    let sym = |n: &str| tm.sym(n.as_bytes()).unwrap();
    let acons = |h: covalence_init::Term, t: covalence_init::Term| {
        tm.th.cons.clone().apply(h).unwrap().apply(t).unwrap()
    };
    let lst = acons(sym("a"), acons(sym("b"), tm.th.nil.clone()));
    let expected = tm
        .th
        .car
        .clone()
        .apply(lst)
        .unwrap()
        .equals(sym("a"))
        .unwrap();
    assert_eq!(entry.thm.concl(), &expected, "the model equation, exactly");
}

/// Out-of-fragment ground goals keep the pre-ladder behaviour: proved by
/// certified kernel reduction, recorded as [`Acl2Proof::Reduction`].
#[test]
fn defthm_out_of_fragment_falls_back_to_reduction() {
    use covalence_lisp::acl2::Acl2Proof;

    let mut s = session();
    s.eval_cell(APP).unwrap();
    // A user defun is not a PrimRow: reduction fallback, riding the defun
    // hypothesis (never a certificate).
    s.eval_cell("(defthm app-ab-c (equal (app (quote (a b)) (quote (c))) (quote (a b c))))")
        .unwrap();
    let entry = s.theorem_entry("app-ab-c").expect("stored theorem");
    assert!(matches!(entry.proof, Acl2Proof::Reduction));
    assert!(!entry.thm.hyps().is_empty(), "rides the defun hypothesis");

    // `*` has no public ground model-folding law yet (only `plus_lit` is
    // exported): outside the certificate fragment, but still honestly
    // proved by reduction, hyps-free.
    s.eval_cell("(defthm twelve (equal (* 3 4) 12))").unwrap();
    let entry = s.theorem_entry("twelve").expect("stored theorem");
    assert!(matches!(entry.proof, Acl2Proof::Reduction));
    assert!(entry.thm.hyps().is_empty());
}

#[test]
fn defthm_ground_list_goal_rides_defun_hypotheses() {
    let mut s = session();
    s.eval_cell(APP).unwrap();
    assert_eq!(
        s.eval_cell("(defthm app-ab-c (equal (app (quote (a b)) (quote (c))) (quote (a b c))))")
            .unwrap(),
        "app-ab-c"
    );
    let thm = s.theorem("app-ab-c").expect("stored theorem");
    // The proof unfolds `app`, so the defun equation rides as a hypothesis —
    // honestly recorded, never discharged by fiat.
    assert!(
        !thm.hyps().is_empty(),
        "a defun-using defthm must carry the defun hypothesis"
    );
    assert!(thm.concl().as_eq().is_some(), "concl is the equation goal");
}

// ---- defthm: honest rejections --------------------------------------------

#[test]
fn defthm_non_ground_is_rejected_pointing_at_induction() {
    let mut s = session();
    s.eval_cell(APP).unwrap();
    let err = s
        .eval_cell("(defthm app-nil (equal (app x (quote ())) x))")
        .unwrap_err();
    let msg = err.to_string();
    assert!(
        msg.contains("induction"),
        "must name the missing piece: {msg}"
    );
    assert!(msg.contains('x'), "must name the free variable: {msg}");
    assert!(s.theorem("app-nil").is_none(), "nothing may be stored");
}

#[test]
fn defthm_false_ground_goal_is_refuted_not_faked() {
    let mut s = session();
    let err = s.eval_cell("(defthm bogus (equal (+ 2 2) 5))").unwrap_err();
    assert!(err.to_string().contains("FALSE"), "got: {err}");
    assert!(s.theorem("bogus").is_none(), "nothing may be stored");
}

#[test]
fn defthm_non_boolean_goal_is_rejected() {
    let mut s = session();
    let err = s
        .eval_cell("(defthm datum (cons (quote a) (quote ())))")
        .unwrap_err();
    assert!(err.to_string().contains("boolean"), "got: {err}");
    assert!(s.theorem("datum").is_none());
}

// ---- defun: admissibility -------------------------------------------------

#[test]
fn non_structural_defun_is_rejected() {
    let mut s = session();
    // Identity-argument recursion: nothing decreases.
    let err = s.eval_cell("(defun bad (x) (bad x))").unwrap_err();
    let msg = err.to_string();
    assert!(msg.contains("structurally recursive"), "got: {msg}");
    // Growing-argument recursion: also rejected.
    let err = s
        .eval_cell("(defun grow (x) (grow (cons x x)))")
        .unwrap_err();
    assert!(err.to_string().contains("structurally recursive"));
    // Neither definition was installed.
    assert!(s.defs().is_empty());
}

#[test]
fn structural_predicate_defun_is_admitted() {
    let mut s = session();
    assert_eq!(
        s.eval_cell(
            "(defun all-atoms (l) (if (endp l) t (if (atom (car l)) (all-atoms (cdr l)) nil)))"
        )
        .unwrap(),
        "all-atoms"
    );
    let out = eval_checked(&s, "(all-atoms (quote (a b c)))");
    assert_eq!(s.render(&out), "t");
    assert!(!out.thm.hyps().is_empty());
    let out = eval_checked(&s, "(all-atoms (quote (a (b) c)))");
    assert_eq!(s.render(&out), "nil");
}

#[test]
fn defun_retains_plain_structural_admission_witnesses() {
    let mut s = Acl2Session::new().unwrap();

    s.eval_cell("(defun identity (x) x)").unwrap();
    let identity = s.admission("identity").unwrap();
    assert_eq!(identity.recursive_calls, 0);
    assert_eq!(identity.decreasing_parameter, None);
    let identity_hol = s.hol_definition("identity").unwrap();
    assert!(identity_hol.defining_equation.hyps().is_empty());

    s.eval_cell(APP).unwrap();
    let app = s.admission("app").unwrap();
    assert_eq!(app.recursive_calls, 1);
    assert_eq!(app.decreasing_parameter, Some(0));
    let app_hol = s.hol_definition("app").unwrap();
    assert!(
        app_hol.defining_equation.hyps().is_empty(),
        "deep admission must produce a conservative theorem, not an assumed equation"
    );

    assert!(s.eval_cell("(defun bad (x) (bad x))").is_err());
    assert!(s.admission("bad").is_none());
    assert!(s.hol_definition("bad").is_none());
}

#[test]
#[ignore = "full open-theorem replay currently takes about 100 seconds"]
// TODO(cov:lisp.acl2.induction-test-performance, major): Bring the append admission/execution/induction integration gate below ten seconds and enable it in the default ACL2 test suite.
fn recursive_definition_runs_and_transports_an_open_theorem() {
    use covalence_lisp::acl2::Acl2Proof;

    let mut s = session();
    s.eval_cell(APP).unwrap();

    let admission = s.admission("app").expect("surface admission witness");
    assert_eq!(admission.decreasing_parameter, Some(0));
    assert!(
        s.hol_definition("app")
            .expect("deep conservative definition")
            .defining_equation
            .hyps()
            .is_empty()
    );

    let out = eval_checked(&s, "(app (quote (a b)) (quote (c)))");
    assert_eq!(s.render(&out), "(a b c)");

    s.eval_cell("(defthm app-assoc (equal (app (app x y) z) (app x (app y z))))")
        .unwrap();
    let theorem = s
        .theorem_entry("app-assoc")
        .expect("transported open theorem");
    assert!(theorem.thm.hyps().is_empty());
    assert!(matches!(theorem.proof, Acl2Proof::Induction { .. }));
}

#[test]
fn undefined_callee_is_rejected() {
    let mut s = session();
    // ACL2 requires definition before use — no forward references.
    let err = s.eval_cell("(defun f (x) (g x))").unwrap_err();
    assert!(err.to_string().contains("undefined"), "got: {err}");
}

#[test]
fn integer_valued_recursion_over_lists_works() {
    // `len` is structurally recursive AND integer-valued: the recursive
    // head's return type is inferred as `int` (the value semantics carries
    // the integer backend), and the value rides the defun hypothesis.
    let mut s = session();
    assert_eq!(
        s.eval_cell("(defun len2 (x) (if (endp x) 0 (+ 1 (len2 (cdr x)))))")
            .unwrap(),
        "len2"
    );
    let out = eval_checked(&s, "(len2 (quote (a b c)))");
    assert_eq!(s.render(&out), "3");
    assert_eq!(out.kind, Acl2ValueKind::Int);
    assert!(!out.thm.hyps().is_empty(), "rides the defun hypothesis");
}

// ---- expression-level honesty ---------------------------------------------

#[test]
fn unbound_variable_is_a_clean_error() {
    let s = session();
    let form = read_one("(car x)").unwrap();
    let err = s.reduce(&form).unwrap_err();
    assert!(err.to_string().contains("unbound"), "got: {err}");
}
