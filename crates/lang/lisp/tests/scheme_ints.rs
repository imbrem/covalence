//! **Integers in the `#lang scheme` value semantics** — the Scheme
//! convergence point: recursion AND integers in one dialect.
//!
//! Every value printed here is read off a genuine kernel theorem
//! `hyps ⊢ input = value`: for closed arithmetic the hypothesis set is empty
//! (the computation is kernel-proved via `TermExt::reduce`, never asserted);
//! for programs using `defun`s the hypotheses are **exactly** the assumed
//! defining equations (`{f = λ…}`), never anything else.
#![cfg(feature = "hol")]

use covalence_lisp::defs::Defs;
use covalence_lisp::reader::read_one;
use covalence_lisp::semantics::LispSemantics;
use covalence_lisp::session::{Outcome, Session};
use covalence_repl_core::{Fuel, Reduction, RunToValue, Strategy};
use covalence_types::Int;

/// A fresh session switched to `#lang scheme`.
fn scheme() -> Session {
    let mut s = Session::new().unwrap();
    assert_eq!(
        s.eval_cell("#lang scheme").unwrap(),
        "#lang scheme (session reset)"
    );
    s
}

/// Reduce `src` and return the [`Outcome`], asserting the scheme theorem
/// shape: an **equation** whose RHS is the printed value term.
fn outcome(s: &Session, src: &str) -> Outcome {
    let form = read_one(src).expect("parse");
    let out = s.reduce(&form).expect("reduce");
    let (_lhs, rhs) = out
        .thm
        .concl()
        .as_eq()
        .expect("scheme theorem is an equation");
    assert_eq!(
        rhs, &out.value,
        "printed value must be the theorem's RHS (`{src}`)"
    );
    out
}

/// [`outcome`] for a **closed** program: additionally hypothesis-free.
fn eval_closed(s: &Session, src: &str) -> String {
    let out = outcome(s, src);
    assert!(
        out.thm.hyps().is_empty(),
        "closed program `{src}` must be hyps-free, got {:?}",
        out.thm.hyps()
    );
    s.render(&out)
}

// ---- closed integer arithmetic -------------------------------------------

#[test]
fn scheme_addition_is_a_kernel_theorem() {
    let s = scheme();
    assert_eq!(eval_closed(&s, "(+ 2 2)"), "4");
    // The RHS really is the kernel `int` literal 4.
    let out = outcome(&s, "(+ 2 2)");
    assert_eq!(
        covalence_hol_eval::as_int(&out.value),
        Some(Int::from(4i128))
    );
}

#[test]
fn scheme_comparisons_produce_t_nil() {
    let s = scheme();
    assert_eq!(eval_closed(&s, "(= 2 2)"), "t");
    assert_eq!(eval_closed(&s, "(= 2 3)"), "nil");
    assert_eq!(eval_closed(&s, "(<= 2 5)"), "t");
    assert_eq!(eval_closed(&s, "(<= 5 2)"), "nil");
}

#[test]
fn scheme_nested_arithmetic_reduces_congruentially() {
    let s = scheme();
    assert_eq!(eval_closed(&s, "(+ 1 (* 2 3))"), "7");
    assert_eq!(eval_closed(&s, "(* (+ 1 2) (- 5 1))"), "12");
    assert_eq!(eval_closed(&s, "(<= (+ 1 1) (* 1 3))"), "t");
}

#[test]
fn scheme_comparisons_drive_conditionals() {
    let s = scheme();
    // An integer comparison is a genuine `bool` — it can steer `if`/`cond`.
    assert_eq!(eval_closed(&s, "(if (<= 1 2) (quote a) (quote b))"), "a");
    assert_eq!(eval_closed(&s, "(if (= 1 2) (quote a) (quote b))"), "b");
}

#[test]
fn scheme_quoted_numerals_stay_data() {
    let s = scheme();
    // Inside `quote`, a numeral is an uninterpreted atom, as before.
    assert_eq!(eval_closed(&s, "(car (quote (1 2)))"), "1");
    assert_eq!(eval_closed(&s, "(atom? (quote 7))"), "t");
}

// ---- integers + recursion (the convergence point) ------------------------

const LEN: &str = "(defun len (l) \
    (cond ((null? l) 0) \
          (t (+ 1 (len (cdr l))))))";

#[test]
fn scheme_len_mixes_recursion_and_integers() {
    let mut s = scheme();
    s.eval_cell(LEN).unwrap();

    let out = outcome(&s, "(len (quote (a b c)))");
    assert_eq!(s.render(&out), "3");
    assert_eq!(
        covalence_hol_eval::as_int(&out.value),
        Some(Int::from(3i128))
    );

    // Theorem shape: `{len = λl. …} ⊢ (len '(a b c)) = 3` — the hypotheses
    // are EXACTLY the definitions used, nothing else.
    let hyps = out.thm.hyps();
    assert_eq!(hyps.len(), 1, "exactly the `len` defining equation");
    let def = s.defs().get("len").expect("len installed");
    assert!(
        hyps.contains(def.assumption.concl()),
        "the hypothesis IS the assumed `len = λ…` equation"
    );

    // Base case too (exercises the int-typed `cond`).
    let out = outcome(&s, "(len (quote ()))");
    assert_eq!(s.render(&out), "0");
    assert_eq!(out.thm.hyps().len(), 1);
}

#[test]
fn scheme_recursive_defuns_still_work_alongside_ints() {
    // The pre-existing predicate recursion is unaffected by the int wiring.
    let mut s = scheme();
    s.eval_cell(
        "(defun lat? (l) \
            (cond ((null? l) t) \
                  ((atom? (car l)) (lat? (cdr l))) \
                  (t nil)))",
    )
    .unwrap();
    let out = outcome(&s, "(lat? (quote (a b c)))");
    assert_eq!(s.render(&out), "t");
    assert_eq!(out.thm.hyps().len(), 1);
}

// ---- error quality --------------------------------------------------------

#[test]
fn stuck_errors_are_single_layer() {
    let mut s = scheme();
    // Unbound variable: named plainly — no kernel dump, no double wrap.
    let err = s.eval_cell("x").unwrap_err().to_string();
    assert_eq!(err, "stuck: unbound variable `x`");

    // A stuck user call says "no reduction for" EXACTLY once (the historical
    // regression rendered `stuck: no reduction for `no reduction for …``).
    let err = s
        .eval_cell("(undefined-fn (quote a))")
        .unwrap_err()
        .to_string();
    assert!(err.starts_with("stuck: "), "got: {err}");
    assert_eq!(
        err.matches("no reduction for").count(),
        1,
        "single-layer stuck message, got: {err}"
    );
}

#[test]
fn int_op_on_non_integer_operand_is_a_clean_error() {
    let mut s = scheme();
    // `(car '(a))` reduces to the atom `a`, which is not an int literal: the
    // `+` redex must be a clean Err (never a printed value).
    let err = s
        .eval_cell("(+ (car (quote (a b))) 1)")
        .unwrap_err()
        .to_string();
    assert!(err.contains("expects integer operands"), "got: {err}");
    assert_eq!(err.matches("no reduction for").count(), 0, "got: {err}");
}

// ---- the nat-restricted backend plugs into the value semantics ------------

#[test]
fn nat_backend_rejects_negative_results() {
    let sem = LispSemantics::with_defs_nat(Defs::new()).unwrap();

    // Positive arithmetic still reduces to a genuine hyps-free theorem.
    let term = sem.compile(&read_one("(+ 2 3)").unwrap()).unwrap();
    let mut red = Reduction::start(term);
    RunToValue.drive(&sem, &mut red, Fuel::UNBOUNDED).unwrap();
    let (value, thm) = red.into_parts();
    let thm = thm.expect("at least one step");
    assert!(thm.hyps().is_empty());
    assert_eq!(covalence_hol_eval::as_int(&value), Some(Int::from(5i128)));

    // `(- 2 5)` would be negative: a clean error, never a value.
    let term = sem.compile(&read_one("(- 2 5)").unwrap()).unwrap();
    let mut red = Reduction::start(term);
    let err = RunToValue
        .drive(&sem, &mut red, Fuel::UNBOUNDED)
        .unwrap_err();
    assert!(err.to_string().contains("negative"), "got: {err}");

    // The signed default (what `#lang scheme` wires) allows it.
    let sem = LispSemantics::with_defs(Defs::new()).unwrap();
    let term = sem.compile(&read_one("(- 2 5)").unwrap()).unwrap();
    let mut red = Reduction::start(term);
    RunToValue.drive(&sem, &mut red, Fuel::UNBOUNDED).unwrap();
    let (value, _) = red.into_parts();
    assert_eq!(covalence_hol_eval::as_int(&value), Some(Int::from(-3i128)));
}
