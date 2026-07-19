//! Kernel-independent integration gate for the classic metacircular evaluator.

use covalence_kernel_lisp::Datum;
use covalence_lisp::frontend::{CoreAtom, HostSession, SurfaceDialect};
use covalence_lisp::reader::{read, read_one};

const METACIRCULAR: &str = r#"
(label assoc (lambda (k a)
  (cond ((eq? (car (car a)) k) (car (cdr (car a))))
        (t (assoc k (cdr a))))))

(label evlis (lambda (m a)
  (cond ((eq? m nil) nil)
        (t (cons (eval (car m) a) (evlis (cdr m) a))))))

(label evcon (lambda (c a)
  (cond ((eval (car (car c)) a) (eval (car (cdr (car c))) a))
        (t (evcon (cdr c) a)))))

(label pair (lambda (ks vs)
  (cond ((eq? ks nil) nil)
        (t (cons (cons (car ks) (cons (car vs) nil))
                 (pair (cdr ks) (cdr vs)))))))

(label eval (lambda (e a)
  (cond
    ((integer? e) e)
    ((atom? e) (assoc e a))
    ((atom? (car e))
     (cond ((eq? (car e) (quote quote)) (car (cdr e)))
           ((eq? (car e) (quote atom))  (atom? (eval (car (cdr e)) a)))
           ((eq? (car e) (quote eq))    (eq? (eval (car (cdr e)) a)
                                                (eval (car (cdr (cdr e))) a)))
           ((eq? (car e) (quote car))   (car  (eval (car (cdr e)) a)))
           ((eq? (car e) (quote cdr))   (cdr  (eval (car (cdr e)) a)))
           ((eq? (car e) (quote cons))  (cons (eval (car (cdr e)) a)
                                               (eval (car (cdr (cdr e))) a)))
           ((eq? (car e) (quote cond))  (evcon (cdr e) a))
           (t (eval (cons (assoc (car e) a) (cdr e)) a))))
    ((eq? (car (car e)) (quote lambda))
     (eval (car (cdr (cdr (car e))))
           (append (pair (car (cdr (car e))) (evlis (cdr e) a)) a))))))
"#;

fn symbol(name: &str) -> Datum<CoreAtom> {
    Datum::Atom(CoreAtom::symbol(name))
}

fn evaluate(session: &HostSession, source: &str) -> Datum<CoreAtom> {
    let value = session.evaluate(&read_one(source).unwrap()).unwrap();
    value
        .as_datum()
        .expect("metacircular evaluator returned a closure-containing value")
}

#[test]
fn classic_metacircular_evaluator_runs_on_the_shared_host_core() {
    let mut session = HostSession::new(SurfaceDialect::Scheme, 20_000);
    let definitions = read(METACIRCULAR).unwrap();
    assert_eq!(session.define_group(&definitions).unwrap().len(), 5);

    assert_eq!(
        evaluate(&session, "(eval (quote (car (cons 1 2))) (quote ()))"),
        Datum::Atom(CoreAtom::Integer(1.into()))
    );
    assert_eq!(
        evaluate(
            &session,
            "(eval (quote ((lambda (x) (cons x x)) 7)) (quote ()))"
        ),
        Datum::cons(
            Datum::Atom(CoreAtom::Integer(7.into())),
            Datum::Atom(CoreAtom::Integer(7.into()))
        )
    );
    assert_eq!(
        evaluate(
            &session,
            "(eval (quote (cond ((eq 1 1) (quote yes))
                                (t (quote no))))
                   (quote ()))"
        ),
        symbol("yes")
    );
}
