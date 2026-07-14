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
fn scheme_integer_arithmetic_is_stuck() {
    let mut s = Session::new().unwrap();
    s.eval_cell("#lang scheme").unwrap();
    // In `scheme`, `+`/`2` are ordinary symbols with no reduction rule: `(+ 2 2)`
    // is an error (a stuck user-call / unknown operator).
    assert!(
        s.eval_cell("(+ 2 2)").is_err(),
        "integer arithmetic must be stuck in scheme"
    );
}

// ---- `#lang sector` (relational, no integers) ---------------------------

#[test]
fn sector_integers_stuck_primitives_work() {
    let mut s = Session::new().unwrap();
    s.eval_cell("#lang sector").unwrap();
    // `(+ 2 2)` is stuck: it reduces to itself (Reduces refl), rendering as the
    // raw stuck term — NOT `4`.
    assert_ne!(s.eval_cell("(+ 2 2)").unwrap(), "4");
    // McCarthy primitives still work.
    assert_eq!(s.eval_cell("(car (quote (a b)))").unwrap(), "a");
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
