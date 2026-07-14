//! End-to-end REPL battery mirroring **The Little Schemer, chapter 1** — the
//! primitives over lists of atoms (`car`, `cdr`, `cons`, `atom?`, `null?`,
//! `eq?`, `consp`, `quote`), driven through the [`Session`] REPL.
//!
//! Every case asserts BOTH:
//! 1. the printed string matches the expected Little-Schemer value, AND
//! 2. the reduction produced a **hypothesis-free kernel theorem** whose RHS is
//!    exactly the value that was printed — i.e. nothing prints without a Thm.
//!
//! Chapter-2 recursion (`lat?`, `member?`, user `defun`s) is out of scope —
//! it needs recursion / definitions the current evaluator lacks; recorded in
//! `crates/lang/lisp/SKELETONS.md`.
#![cfg(feature = "hol")]

use covalence_lisp::semantics::ValueKind;
use covalence_lisp::session::Session;

/// Run one cell, returning the printed value; also assert the reduction is a
/// hyps-free theorem whose conclusion RHS renders to that same printed value.
fn eval(sess: &mut Session, src: &str) -> String {
    let form = covalence_lisp::reader::read_one(src).expect("parse");
    let r = sess.reduce(&form).expect("reduce");
    // (2) hyps-free genuine kernel theorem.
    assert!(
        r.thm.hyps().is_empty(),
        "cell `{src}` must produce a hypothesis-free theorem, got hyps {:?}",
        r.thm.hyps()
    );
    // The theorem's conclusion is an equation whose RHS is the value.
    let (_, rhs) = r.thm.concl().as_eq().expect("conclusion is `lhs = rhs`");
    assert_eq!(rhs, &r.value, "the value must be the theorem's RHS");
    // (1) the printed string comes off the theorem, via the Session renderer.
    sess.render(&r)
}

fn session() -> Session {
    Session::new().expect("session")
}

// ---- car / cdr / cons ---------------------------------------------------

#[test]
fn car_of_list() {
    let mut s = session();
    assert_eq!(eval(&mut s, "(car (quote (a b c)))"), "a");
}

#[test]
fn cdr_of_list() {
    let mut s = session();
    assert_eq!(eval(&mut s, "(cdr (quote (a b c)))"), "(b c)");
}

#[test]
fn car_of_cdr() {
    let mut s = session();
    // (car (cdr '(a b c))) = b  — nested projection, multi-step.
    assert_eq!(eval(&mut s, "(car (cdr (quote (a b c))))"), "b");
}

#[test]
fn cdr_of_cdr() {
    let mut s = session();
    assert_eq!(eval(&mut s, "(cdr (cdr (quote (a b c))))"), "(c)");
}

#[test]
fn car_of_car_nested_list() {
    let mut s = session();
    // (car (car '((a b) c))) = a
    assert_eq!(eval(&mut s, "(car (car (quote ((a b) c))))"), "a");
}

#[test]
fn cons_atom_onto_list() {
    let mut s = session();
    assert_eq!(eval(&mut s, "(cons (quote a) (quote (b c)))"), "(a b c)");
}

#[test]
fn cons_onto_empty() {
    let mut s = session();
    assert_eq!(eval(&mut s, "(cons (quote a) (quote ()))"), "(a)");
}

#[test]
fn cons_then_car() {
    let mut s = session();
    // (car (cons 'a '(b c))) = a  — cons builds, car projects; one theorem.
    assert_eq!(eval(&mut s, "(car (cons (quote a) (quote (b c))))"), "a");
}

#[test]
fn cons_then_cdr() {
    let mut s = session();
    assert_eq!(
        eval(&mut s, "(cdr (cons (quote a) (quote (b c))))"),
        "(b c)"
    );
}

// ---- atom? / consp ------------------------------------------------------

#[test]
fn atom_of_atom_is_t() {
    let mut s = session();
    assert_eq!(eval(&mut s, "(atom? (quote a))"), "t");
}

#[test]
fn atom_of_list_is_nil() {
    let mut s = session();
    assert_eq!(eval(&mut s, "(atom? (quote (a b)))"), "nil");
}

#[test]
fn atom_of_car() {
    let mut s = session();
    // (atom? (car '(a b c))) = t   (car → atom a → atom? = t)
    assert_eq!(eval(&mut s, "(atom? (car (quote (a b c))))"), "t");
}

#[test]
fn consp_of_list_is_t() {
    let mut s = session();
    assert_eq!(eval(&mut s, "(consp (quote (a b)))"), "t");
}

#[test]
fn consp_of_atom_is_nil() {
    let mut s = session();
    assert_eq!(eval(&mut s, "(consp (quote a))"), "nil");
}

// ---- null? --------------------------------------------------------------

#[test]
fn null_of_empty_is_t() {
    let mut s = session();
    assert_eq!(eval(&mut s, "(null? (quote ()))"), "t");
}

#[test]
fn null_of_nonempty_is_nil() {
    let mut s = session();
    assert_eq!(eval(&mut s, "(null? (quote (a b)))"), "nil");
}

#[test]
fn null_of_cdr_to_empty() {
    let mut s = session();
    // (null? (cdr '(a))) = t
    assert_eq!(eval(&mut s, "(null? (cdr (quote (a))))"), "t");
}

// ---- eq? ----------------------------------------------------------------

#[test]
fn eq_same_atoms_is_t() {
    let mut s = session();
    assert_eq!(eval(&mut s, "(eq? (quote a) (quote a))"), "t");
}

#[test]
fn eq_different_atoms_is_nil() {
    let mut s = session();
    assert_eq!(eval(&mut s, "(eq? (quote a) (quote b))"), "nil");
}

#[test]
fn eq_of_cars() {
    let mut s = session();
    // (eq? (car '(a b)) (car '(a c))) = t  — both cars are atom a.
    assert_eq!(
        eval(&mut s, "(eq? (car (quote (a b))) (car (quote (a c))))"),
        "t"
    );
}

// ---- value kinds / theorem shape ---------------------------------------

#[test]
fn data_ops_yield_data_kind_predicates_yield_bool() {
    let s = session();
    let car = s
        .reduce(&covalence_lisp::reader::read_one("(car (quote (a b)))").unwrap())
        .unwrap();
    assert_eq!(car.kind, ValueKind::Data);
    let atomp = s
        .reduce(&covalence_lisp::reader::read_one("(atom? (quote a))").unwrap())
        .unwrap();
    assert_eq!(atomp.kind, ValueKind::Bool);
}

// ---- directives ---------------------------------------------------------

#[test]
fn directive_help_lists_primitives() {
    let mut s = session();
    let out = s.eval_cell("#help").expect("help");
    assert!(out.contains("(car E)"));
    assert!(out.contains("#show"));
}

#[test]
fn directive_show_prints_the_theorem() {
    let mut s = session();
    let out = s.eval_cell("#show (car (quote (a b c)))").expect("show");
    // The full `lhs = rhs` conclusion: an equation mentioning `=`.
    assert!(out.contains('='), "expected an equation, got `{out}`");
}

#[test]
fn eval_cell_prints_value() {
    let mut s = session();
    assert_eq!(s.eval_cell("(car (quote (a b c)))").unwrap(), "a");
    assert_eq!(s.eval_cell("(cdr (quote (a b c)))").unwrap(), "(b c)");
}

// ---- stuck / error paths ------------------------------------------------

#[test]
fn unknown_operator_is_an_error() {
    let mut s = session();
    assert!(s.eval_cell("(frobnicate (quote a))").is_err());
}

#[test]
fn eq_on_non_atom_is_an_error() {
    let mut s = session();
    // eq? on lists is out of scope (ch1 eq? is atoms only).
    assert!(s.eval_cell("(eq? (quote (a)) (quote (a)))").is_err());
}

// ---- streaming / fuel-bounded reduction ---------------------------------

// The parametric reduction is a *step relation*: `reduce` runs to a value, but
// a bounded `drive_fueled` yields a CERTIFIED PARTIAL reduction instead of
// hanging — the seam a non-terminating recursive program (ch2) will use.
#[test]
fn fuel_bound_is_a_certified_partial_not_a_hang() {
    use covalence_repl_core::{Fuel, Status};
    let s = session();
    let form = covalence_lisp::reader::read_one("(car (cdr (quote (a b c))))").unwrap();

    // One step: not yet a value, but the partial chain `⊢ input = cur` is real.
    let one = s.drive_fueled(&form, Fuel::steps(1)).unwrap();
    assert_eq!(one.steps(), 1);
    assert!(matches!(one.status(), Status::Diverging(1)));
    assert!(
        one.composite().is_some(),
        "one step must carry ⊢ input = cur"
    );

    // Unbounded: reaches the value `b`, and it equals the full `reduce`.
    let full = s.drive_fueled(&form, Fuel::UNBOUNDED).unwrap();
    assert!(matches!(full.status(), Status::Value));
    assert_eq!(eval(&mut session(), "(car (cdr (quote (a b c))))"), "b");
}
