//! End-to-end `#lang` dialect battery for the [`Session`] REPL: the DEFAULT
//! `lisp` dialect (relational, integers on), `scheme` (equational value
//! semantics with recursion), and `sector` (relational, no integers). Every
//! relational value is read off a hypothesis-free `⊢ Reduces input value`
//! theorem; every `scheme` value off a `⊢ input = value` equation.
#![cfg(feature = "hol")]

use covalence_lisp::reader::read_one;
use covalence_lisp::session::{Lang, Session};

/// Reduce one cell (bypassing directives) and return the printed value, after
/// asserting the reduction is a hypothesis-free theorem whose RHS renders to
/// that value.
fn eval(s: &Session, src: &str) -> String {
    let form = read_one(src).expect("parse");
    let out = s.reduce(&form).expect("reduce");
    assert!(
        out.thm.hyps().is_empty(),
        "closed program `{src}` must be hyps-free, got {:?}",
        out.thm.hyps()
    );
    s.render(&out)
}

// ---- default dialect: `lisp` (relational, integers on) ------------------

#[test]
fn default_lang_is_lisp() {
    let s = Session::new().unwrap();
    assert_eq!(s.lang(), Lang::Lisp);
}

#[test]
fn lisp_integer_arithmetic() {
    let s = Session::new().unwrap();
    assert_eq!(eval(&s, "(+ 2 2)"), "4");
    assert_eq!(eval(&s, "(- 5 3)"), "2");
    assert_eq!(eval(&s, "(* 3 4)"), "12");
}

#[test]
fn lisp_reduces_theorem_shape() {
    // The default dialect's theorem is `⊢ Reduces input value`, NOT an equation.
    let s = Session::new().unwrap();
    let form = read_one("(+ 2 2)").unwrap();
    let out = s.reduce(&form).unwrap();
    assert!(
        out.thm.concl().as_eq().is_none(),
        "relational: not an equation"
    );
    assert!(out.thm.hyps().is_empty());
}

#[test]
fn lisp_nested_arithmetic() {
    // Congruence into int operands: nested expressions reduce all the way to
    // a value (each off a hyps-free `⊢ Reduces input value`, per `eval`).
    let s = Session::new().unwrap();
    assert_eq!(eval(&s, "(+ 1 (+ 2 3))"), "6");
    assert_eq!(eval(&s, "(<= (+ 1 1) 5)"), "t");
    assert_eq!(eval(&s, "(* (+ 1 2) (- 5 1))"), "12");
    // Deeper nesting on both sides: (2*(1+2)) + ((3*3)-(2+2)) = 6 + 5 = 11.
    assert_eq!(eval(&s, "(+ (* 2 (+ 1 2)) (- (* 3 3) (+ 2 2)))"), "11");
}

#[test]
fn nested_reduces_theorem_is_genuine() {
    // The nested reduction's theorem IS `⊢ Reduces input value` for the
    // compiled input — checked against an independently built relation.
    use covalence_lisp::relation::{Dialect, IntFlavour, LispRel};
    let s = Session::new().unwrap();
    let form = read_one("(+ 1 (+ 2 3))").unwrap();
    let out = s.reduce(&form).unwrap();
    assert!(out.thm.hyps().is_empty());

    let rel = LispRel::with_dialect(Dialect::SectorInt(IntFlavour::Int)).unwrap();
    let input = rel.compile_surface(&form).unwrap();
    assert_eq!(
        out.thm.concl(),
        &rel.reduces_prop(&input, &out.value).unwrap()
    );
    assert_eq!(rel.render_value(&out.value), "6");
}

#[test]
fn lisp_comparisons() {
    let s = Session::new().unwrap();
    assert_eq!(eval(&s, "(<= 2 5)"), "t");
    assert_eq!(eval(&s, "(<= 5 2)"), "nil");
    assert_eq!(eval(&s, "(= 4 4)"), "t");
    assert_eq!(eval(&s, "(= 4 5)"), "nil");
}

#[test]
fn lisp_primitives_still_work() {
    let s = Session::new().unwrap();
    assert_eq!(eval(&s, "(car (quote (a b)))"), "a");
    assert_eq!(eval(&s, "(cdr (quote (a b c)))"), "(b c)");
    assert_eq!(eval(&s, "(cons (quote a) (quote (b)))"), "(a b)");
    assert_eq!(eval(&s, "(atom? (quote a))"), "t");
    assert_eq!(eval(&s, "(null? (quote ()))"), "t");
}

// ---- honesty: stuck programs are clean errors, never printed values ------

#[test]
fn lisp_stuck_is_a_clean_error() {
    let s = Session::new().unwrap();
    // `(+ 1 x)` — the symbol operand is a value but not an int literal, so the
    // redex never fires: stuck, and must be an Err (never printed as SUCCESS).
    let form = read_one("(+ 1 (quote x))").unwrap();
    let msg = s.reduce(&form).map(|_| ()).unwrap_err().to_string();
    assert!(msg.contains("stuck"), "got: {msg}");
    assert!(msg.contains("does not reduce to a value"), "got: {msg}");
    assert!(
        !msg.contains("lisp.rel."),
        "no raw kernel syntax in a user-facing error: {msg}"
    );

    // `(car (quote a))` — car of an atom has no rule: also a clean Err.
    let form = read_one("(car (quote a))").unwrap();
    let msg = s.reduce(&form).map(|_| ()).unwrap_err().to_string();
    assert!(msg.contains("does not reduce to a value"), "got: {msg}");
}

#[test]
fn lisp_defun_is_a_friendly_error() {
    let mut s = Session::new().unwrap();
    // The default (relational) dialect has no β/δ clauses: `defun` must point
    // the user at `#lang scheme`, not dump internal jargon.
    let msg = s.eval_cell("(defun f (x) x)").unwrap_err().to_string();
    assert!(msg.contains("#lang scheme"), "got: {msg}");
    assert!(!msg.contains("unknown or misapplied"), "got: {msg}");
    // `lambda` and `define` too.
    let msg = s.eval_cell("(lambda (x) x)").unwrap_err().to_string();
    assert!(msg.contains("#lang scheme"), "got: {msg}");
    let msg = s
        .eval_cell("(define f (lambda (x) x))")
        .unwrap_err()
        .to_string();
    assert!(msg.contains("#lang scheme"), "got: {msg}");
}

#[test]
fn lisp_unknown_operator_is_a_clear_error() {
    let mut s = Session::new().unwrap();
    let msg = s.eval_cell("(frobnicate 1 2)").unwrap_err().to_string();
    assert!(msg.contains("frobnicate"), "got: {msg}");
    assert!(msg.contains("unknown"), "got: {msg}");
    // It names the supported primitives so the user can recover.
    assert!(msg.contains("car"), "got: {msg}");
}

// ---- `#lang scheme` (equational value semantics + recursion) ------------

const LAT: &str = "(defun lat? (l) \
    (cond ((null? l) t) \
          ((atom? (car l)) (lat? (cdr l))) \
          (t nil)))";

#[test]
fn scheme_recursion_works() {
    let mut s = Session::new().unwrap();
    assert_eq!(
        s.eval_cell("#lang scheme").unwrap(),
        "#lang scheme (session reset)"
    );
    s.eval_cell(LAT).unwrap();
    assert_eq!(s.eval_cell("(lat? (quote (a b c)))").unwrap(), "t");
}

#[test]
fn scheme_integer_arithmetic() {
    // `scheme` = recursion AND integers: the equational value semantics
    // reduces `(+ 2 2)` to the kernel `int` literal `4`, off a hyps-free
    // `⊢ (+ 2 2) = 4` (arithmetic kernel-proved via `TermExt::reduce`).
    let mut s = Session::new().unwrap();
    s.eval_cell("#lang scheme").unwrap();
    assert_eq!(eval(&s, "(+ 2 2)"), "4");
    assert_eq!(eval(&s, "(- 5 3)"), "2");
    assert_eq!(eval(&s, "(* 3 4)"), "12");
    assert_eq!(eval(&s, "(= 2 2)"), "t");
    assert_eq!(eval(&s, "(= 2 3)"), "nil");
    assert_eq!(eval(&s, "(<= 2 5)"), "t");
    assert_eq!(eval(&s, "(<= 5 2)"), "nil");
    // Nested operands reduce congruentially.
    assert_eq!(eval(&s, "(+ 1 (* 2 3))"), "7");
    // The scheme theorem IS an equation (unlike the relational dialects).
    let form = read_one("(+ 2 2)").unwrap();
    let out = s.reduce(&form).unwrap();
    assert!(out.thm.concl().as_eq().is_some(), "scheme: an equation");
    assert!(out.thm.hyps().is_empty());
}

// ---- `#lang sector` (relational, no integers) ---------------------------

#[test]
fn sector_integers_stuck_primitives_work() {
    let mut s = Session::new().unwrap();
    s.eval_cell("#lang sector").unwrap();
    // `(+ 2 2)` is stuck (no integer clauses): the honesty guard makes this a
    // clean Err — the stuck term is NEVER printed as a value (and never `4`).
    let msg = s.eval_cell("(+ 2 2)").unwrap_err().to_string();
    assert!(msg.contains("does not reduce to a value"), "got: {msg}");
    assert!(msg.contains("#lang lisp"), "got: {msg}");
    // McCarthy primitives still work.
    assert_eq!(s.eval_cell("(car (quote (a b)))").unwrap(), "a");
}

// ---- `#lang acl2` (value semantics + admissibility + ground defthm) -----

const APP: &str = "(defun app (x y) (if (consp x) (cons (car x) (app (cdr x) y)) y))";

#[test]
fn acl2_defun_run_and_ground_defthm() {
    let mut s = Session::new().unwrap();
    assert_eq!(
        s.eval_cell("#lang acl2").unwrap(),
        "#lang acl2 (session reset)"
    );
    assert_eq!(s.lang(), Lang::Acl2);
    // Admit a structurally recursive defun, run it, prove a ground defthm.
    assert_eq!(s.eval_cell(APP).unwrap(), "app");
    assert_eq!(
        s.eval_cell("(app (quote (a b)) (quote (c)))").unwrap(),
        "(a b c)"
    );
    assert_eq!(
        s.eval_cell("(defthm four (equal (+ 2 2) 4))").unwrap(),
        "four"
    );
    // The defthm is a genuine, auditable kernel theorem.
    let thm = s.acl2().theorem("four").expect("stored theorem");
    assert!(thm.hyps().is_empty(), "ground arithmetic is hyps-free");
    // A free-variable goal is honestly rejected (induction not implemented).
    let msg = s
        .eval_cell("(defthm app-nil (equal (app x (quote ())) x))")
        .unwrap_err()
        .to_string();
    assert!(msg.contains("induction"), "got: {msg}");
}

#[test]
fn acl2_state_resets_on_lang_switch() {
    let mut s = Session::new().unwrap();
    s.eval_cell("#lang acl2").unwrap();
    s.eval_cell(APP).unwrap();
    s.eval_cell("(defthm four (equal (+ 2 2) 4))").unwrap();
    // Switch away and back — defuns AND defthms must be gone.
    s.eval_cell("#lang lisp").unwrap();
    s.eval_cell("#lang acl2").unwrap();
    assert!(
        s.eval_cell("(app (quote (a)) (quote ()))").is_err(),
        "the defun must not survive a #lang reset"
    );
    assert!(
        s.acl2().theorem("four").is_none(),
        "the defthm table must not survive a #lang reset"
    );
}

#[test]
fn acl2_show_prints_the_theorem() {
    let mut s = Session::new().unwrap();
    s.eval_cell("#lang acl2").unwrap();
    // `#show` rides the same reduce path: the printed sequent is the genuine
    // `⊢ input = value` equation — hyps-free here, so it STARTS with `⊢`.
    let out = s.eval_cell("#show (+ 1 2)").unwrap();
    assert!(out.contains('='), "got: {out}");
    assert!(
        out.starts_with('⊢'),
        "closed arithmetic: hyps-free sequent, got: {out}"
    );
}

#[test]
fn acl2_show_defthm_reveals_transported_sequent() {
    // `#show NAME` on a stored certificate-path defthm prints the
    // transported base-HOL model equation (hyps-free, so it starts with
    // `⊢`) and notes it went via the reified certificate.
    let mut s = Session::new().unwrap();
    s.eval_cell("#lang acl2").unwrap();
    s.eval_cell("(defthm four (equal (+ 2 2) 4))").unwrap();
    let out = s.eval_cell("#show four").unwrap();
    assert!(
        out.starts_with('⊢'),
        "transported model equation is hyps-free, got: {out}"
    );
    assert!(out.contains('='), "an equation, got: {out}");
    assert!(
        out.contains("Derivable_ACL2 certificate"),
        "must note the certificate path, got: {out}"
    );

    // A reduction-path defthm is annotated as such.
    s.eval_cell(APP).unwrap();
    s.eval_cell("(defthm app-ab-c (equal (app (quote (a b)) (quote (c))) (quote (a b c))))")
        .unwrap();
    let out = s.eval_cell("#show app-ab-c").unwrap();
    assert!(
        out.contains("certified kernel reduction"),
        "must note the reduction path, got: {out}"
    );
}

#[test]
fn show_prints_hypotheses_of_defun_unfoldings() {
    // The honesty fix for the hover-proof surface: after a `defun`, a call's
    // theorem is `{f = λ…} ⊢ f args = value` — `f` is a FREE variable in the
    // bare conclusion, so printing `⊢ concl` alone would be a false claim.
    // `#show` must print the hypotheses to the LEFT of the turnstile.
    let mut s = Session::new().unwrap();
    s.eval_cell("#lang acl2").unwrap();
    s.eval_cell("(defun app (x y) (if (consp x) (cons (car x) (app (cdr x) y)) y))")
        .unwrap();
    let out = s
        .eval_cell("#show (app (quote (a b)) (quote (c)))")
        .unwrap();
    let turnstile = out.find('⊢').expect("sequent must have a turnstile");
    let hyps = out[..turnstile].trim();
    assert!(
        !hyps.is_empty() && hyps.contains("app"),
        "the `app = λ…` hypothesis must render left of ⊢, got: {out}"
    );

    // Same surface in `scheme` (integer-valued defuns like `len`).
    s.eval_cell("#lang scheme").unwrap();
    s.eval_cell("(defun len (l) (cond ((null? l) 0) (t (+ 1 (len (cdr l))))))")
        .unwrap();
    let out = s.eval_cell("#show (len (quote (a b c)))").unwrap();
    let turnstile = out.find('⊢').expect("sequent must have a turnstile");
    let hyps = out[..turnstile].trim();
    assert!(
        !hyps.is_empty() && hyps.contains("len"),
        "the `len = λ…` hypothesis must render left of ⊢, got: {out}"
    );
}

// ---- `#lang` switching resets session state -----------------------------

#[test]
fn lang_switch_resets_defs() {
    let mut s = Session::new().unwrap();
    s.eval_cell("#lang scheme").unwrap();
    s.eval_cell(LAT).unwrap();
    assert_eq!(s.eval_cell("(lat? (quote (a)))").unwrap(), "t");
    // Switch away and back — the `defun` must be gone.
    s.eval_cell("#lang lisp").unwrap();
    s.eval_cell("#lang scheme").unwrap();
    assert!(
        s.eval_cell("(lat? (quote (a)))").is_err(),
        "the `defun` must not survive a #lang reset"
    );
}

// ---- `#lang` directive UX ------------------------------------------------

#[test]
fn lang_no_arg_reports_current() {
    let mut s = Session::new().unwrap();
    let out = s.eval_cell("#lang").unwrap();
    assert!(out.contains("current #lang: lisp"), "got: {out}");
    assert!(out.contains("scheme"));
    assert!(out.contains("sector"));
}

#[test]
fn lang_unknown_is_a_clean_error() {
    let mut s = Session::new().unwrap();
    assert!(s.eval_cell("#lang bogus").is_err());
    // The session is unchanged after a bad switch.
    assert_eq!(s.lang(), Lang::Lisp);
}

#[test]
fn lang_aliases() {
    let mut s = Session::new().unwrap();
    s.eval_cell("#lang lisp-int").unwrap();
    assert_eq!(s.lang(), Lang::Lisp);
}
