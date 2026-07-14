//! End-to-end REPL battery for **The Little Schemer, chapter 2** and a slice of
//! the **metacircular interpreter** — user `defun`/`define` recursion driven
//! through the [`Session`] REPL.
//!
//! # The soundness contract these tests pin
//!
//! A `(defun f (params) body)` enters the kernel as an **assumption**
//! `{f = λparams. body} ⊢ f = λparams. body` (never an axiom — see
//! [`covalence_lisp::defs`]). So a program that calls user functions reduces to
//! a theorem `definitions ⊢ program = value` whose **hypotheses are exactly the
//! `defun` equations used**. Each recursive test therefore asserts BOTH:
//!
//! 1. the value is correct, AND
//! 2. the reduction theorem's hypotheses are **non-empty** — the defun
//!    equations ride along (contrast the ch1 battery, which is hyps-free).
//!
//! This is sound even for ill-founded / non-terminating recursion: a
//! conditional sequent `{defs} ⊢ Q` is fine even if `defs` is inconsistent, and
//! divergence is caught by the fuel-bounded driver, not a hang.
#![cfg(feature = "hol")]

use covalence_lisp::reader::read_one;
use covalence_lisp::session::{Lang, Session};

fn session() -> Session {
    // Chapter 2 is `defun`/recursion in the equational value semantics — now the
    // `scheme` dialect (the default `lisp` is the relational integer semantics).
    let mut s = Session::new().expect("session");
    s.set_lang(Lang::Scheme);
    s
}

/// Reduce `src` and assert the value renders to `want` AND the theorem carries
/// at least `min_hyps` hypotheses (the `defun` equations). Returns the hyp
/// count so callers can pin exact numbers.
fn eval_hyps(s: &Session, src: &str, want: &str, min_hyps: usize) -> usize {
    let form = read_one(src).expect("parse");
    let out = s.reduce(&form).expect("reduce");
    // The value is the theorem's RHS (the honesty invariant).
    let (_, rhs) = out.thm.concl().as_eq().expect("conclusion is `lhs = rhs`");
    assert_eq!(rhs, &out.value, "value must be the theorem's RHS");
    let nhyps = out.thm.hyps().iter().count();
    assert!(
        nhyps >= min_hyps,
        "`{src}` must carry >= {min_hyps} defun hyps, got {nhyps}"
    );
    assert_eq!(s.render(&out), want, "value mismatch for `{src}`");
    nhyps
}

// ---- defun basics -------------------------------------------------------

#[test]
fn defun_ack_and_identity() {
    let mut s = session();
    // A `defun` returns an ack (the function name), not a value.
    assert_eq!(s.eval_cell("(defun id (x) x)").unwrap(), "id");
    // Applying it: the value is right and the theorem carries the defun hyp.
    eval_hyps(&s, "(id (quote a))", "a", 1);
}

#[test]
fn defun_wrapping_a_primitive() {
    let mut s = session();
    s.eval_cell("(defun mycar (x) (car x))").unwrap();
    eval_hyps(&s, "(mycar (quote (a b c)))", "a", 1);
}

#[test]
fn lambda_application_is_beta() {
    let s = session();
    // A bare lambda application β-reduces — no defun, so it stays hyps-free.
    eval_hyps(&s, "((lambda (x) (cons x x)) (quote a))", "(a . a)", 0);
}

#[test]
fn cond_selects_a_branch() {
    let s = session();
    eval_hyps(
        &s,
        "(cond ((eq? (quote a) (quote a)) (quote yes)) (t (quote no)))",
        "yes",
        0,
    );
    eval_hyps(
        &s,
        "(cond ((eq? (quote a) (quote b)) (quote yes)) (t (quote no)))",
        "no",
        0,
    );
}

// ---- ch2 recursive functions -------------------------------------------

const LAT: &str = "(defun lat? (l) (cond ((null? l) t) ((atom? (car l)) (lat? (cdr l))) (t nil)))";
const MEMBER: &str = "(defun member? (a lat) (cond ((null? lat) nil) (t (cond ((eq? (car lat) a) t) (t (member? a (cdr lat)))))))";
const REMBER: &str = "(defun rember (a l) (cond ((null? l) (quote ())) ((eq? (car l) a) (cdr l)) (t (cons (car l) (rember a (cdr l))))))";

#[test]
fn lat_predicate() {
    let mut s = session();
    s.eval_cell(LAT).unwrap();
    // `lat?` is a *predicate*: value `t`/`nil`, carrying the defun hyp.
    eval_hyps(&s, "(lat? (quote (a b c)))", "t", 1);
    eval_hyps(&s, "(lat? (quote (a (b) c)))", "nil", 1);
    eval_hyps(&s, "(lat? (quote ()))", "t", 1);
}

#[test]
fn member_predicate() {
    let mut s = session();
    s.eval_cell(MEMBER).unwrap();
    eval_hyps(&s, "(member? (quote b) (quote (a b c)))", "t", 1);
    eval_hyps(&s, "(member? (quote z) (quote (a b c)))", "nil", 1);
}

#[test]
fn rember_builds_a_list() {
    let mut s = session();
    s.eval_cell(REMBER).unwrap();
    // `rember` returns *data* — a list with the first `b` removed.
    eval_hyps(&s, "(rember (quote b) (quote (a b c)))", "(a c)", 1);
    eval_hyps(&s, "(rember (quote x) (quote (a b c)))", "(a b c)", 1);
}

#[test]
fn defun_hyp_is_the_assumed_equation() {
    // Pin the exact soundness shape: the single hypothesis is the `defun`
    // equation `lat? = λl. …`, i.e. an equation headed by `=` whose LHS is the
    // free variable `lat?`.
    let mut s = session();
    s.eval_cell(LAT).unwrap();
    let form = read_one("(lat? (quote (a b c)))").unwrap();
    let out = s.reduce(&form).unwrap();
    let hyps: Vec<_> = out.thm.hyps().iter().collect();
    assert_eq!(hyps.len(), 1, "exactly one defun hyp");
    let (lhs, _) = hyps[0].as_eq().expect("the hyp is an equation `f = λ…`");
    assert_eq!(
        lhs.as_free().map(|v| v.name().to_string()),
        Some("lat?".to_string()),
        "the hyp equates the function's free-variable head"
    );
}

// ---- the metacircular interpreter (ground fragment) --------------------

/// A McCarthy-style `eval` for the ground `quote`/`car`/`cdr`/`cons` fragment —
/// dispatched by `eq?` on the operator symbol (a *bool* condition, so it types
/// in HOL). This is the slice of `metacircular.lisp` that runs today (the
/// `assoc`/env and truthy-data-`cond` machinery is deferred — see
/// `crates/lang/lisp/SKELETONS.md`).
const META_EVAL: &str = "(define eval (lambda (e a) (cond \
    ((eq? (car e) (quote quote)) (car (cdr e))) \
    ((eq? (car e) (quote car)) (car (eval (car (cdr e)) a))) \
    ((eq? (car e) (quote cdr)) (cdr (eval (car (cdr e)) a))) \
    ((eq? (car e) (quote cons)) (cons (eval (car (cdr e)) a) (eval (car (cdr (cdr e))) a))) \
    (t (quote unknown)))))";

#[test]
fn metacircular_eval_ground_fragment() {
    let mut s = session();
    assert_eq!(s.eval_cell(META_EVAL).unwrap(), "eval");
    // Each is a certified `{eval = λ…} ⊢ (eval …) = value`.
    eval_hyps(&s, "(eval (quote (quote (a b))) (quote ()))", "(a b)", 1);
    eval_hyps(&s, "(eval (quote (car (quote (x y)))) (quote ()))", "x", 1);
    eval_hyps(
        &s,
        "(eval (quote (cons (quote p) (quote (q)))) (quote ()))",
        "(p q)",
        1,
    );
    // The plan's headline example: nested `car`/`cons` through the interpreter.
    eval_hyps(
        &s,
        "(eval (quote (car (cons (quote 1) (quote (2))))) (quote ()))",
        "1",
        1,
    );
}

#[test]
fn metacircular_result_is_the_theorem_rhs() {
    // The interpreted result is genuinely the RHS of a kernel theorem whose
    // only hypothesis is the `eval` definition — not a bare computed value.
    let mut s = session();
    s.eval_cell(META_EVAL).unwrap();
    let form = read_one("(eval (quote (car (cons (quote 1) (quote (2))))) (quote ()))").unwrap();
    let out = s.reduce(&form).unwrap();
    assert_eq!(out.thm.hyps().iter().count(), 1);
    let (_, rhs) = out.thm.concl().as_eq().unwrap();
    assert_eq!(rhs, &out.value);
    assert_eq!(s.render(&out), "1");
}
