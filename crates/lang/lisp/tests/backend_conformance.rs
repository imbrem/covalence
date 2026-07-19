#![cfg(feature = "hol")]

//! Shared-core conformance between the proof-free host machine and an exact,
//! proof-producing HOL realization.

use covalence_kernel_lisp::{Datum, HostValue};
use covalence_lisp::frontend::{CoreAtom, Frontend, HostSession, SurfaceDialect};
use covalence_lisp::reader::read_one;
use covalence_lisp::relation::{Dialect, LispRel};

fn render_host(value: &HostValue<String, CoreAtom, covalence_lisp::frontend::Primitive>) -> String {
    let Some(datum) = value.as_datum() else {
        return "<closure>".to_owned();
    };
    render_datum(&datum)
}

fn render_datum(datum: &Datum<CoreAtom>) -> String {
    match datum {
        Datum::Nil => "()".to_owned(),
        Datum::Atom(CoreAtom::Symbol(bytes)) => String::from_utf8_lossy(bytes).into_owned(),
        Datum::Atom(CoreAtom::String { bytes, .. }) => {
            format!("\"{}\"", String::from_utf8_lossy(bytes))
        }
        Datum::Atom(CoreAtom::Integer(integer)) => integer.to_string(),
        Datum::Cons(_, _) => {
            let mut fields = Vec::new();
            let mut cursor = datum;
            loop {
                match cursor {
                    Datum::Cons(head, tail) => {
                        fields.push(render_datum(head));
                        cursor = tail;
                    }
                    Datum::Nil => return format!("({})", fields.join(" ")),
                    tail => {
                        return format!("({} . {})", fields.join(" "), render_datum(tail));
                    }
                }
            }
        }
    }
}

#[test]
fn one_lowered_program_agrees_across_host_and_exact_hol_backends() {
    let frontend = Frontend::new(SurfaceDialect::Scheme);
    let host = HostSession::new(SurfaceDialect::Scheme, 512);
    let relation = LispRel::with_dialect(Dialect::ExactIntSymbol).unwrap();

    for (source, expected) in [
        ("(quote (1 alpha 3))", "(1 alpha 3)"),
        ("(car (quote (1 alpha 3)))", "1"),
        ("(cdr (quote (1 alpha 3)))", "(alpha 3)"),
        ("(cons (quote head) (quote (tail)))", "(head tail)"),
        ("(atom? (quote (a)))", "()"),
        ("(consp (quote (a)))", "t"),
        ("(null? (quote ()))", "t"),
        ("(integer? (car (quote (1 a))))", "t"),
        ("(integer? (car (cdr (quote (1 a)))))", "()"),
        ("(eq? (quote same) (quote same))", "t"),
        ("(+ (car (quote (40))) 2)", "42"),
        ("(* (+ 2 3) 4)", "20"),
        ("(append (quote (a b)) (quote (c d)))", "(a b c d)"),
        ("(if (null? (quote ())) (quote yes) (quote no))", "yes"),
        (
            "(cond ((null? (quote (x))) (quote no))
                   ((consp (quote (x))) (quote yes)))",
            "yes",
        ),
    ] {
        let expression = frontend.lower(&read_one(source).unwrap()).unwrap();
        let host_value = host.evaluate_core(&expression).unwrap();
        let (proof_value, theorem) = relation
            .reduce_core(&expression, 128)
            .unwrap_or_else(|error| panic!("HOL relation failed for {source}: {error}"));

        assert_eq!(render_host(&host_value), expected, "host: {source}");
        assert_eq!(
            relation.render_value(&proof_value),
            expected,
            "HOL relation: {source}"
        );
        assert!(
            theorem.hyps().is_empty(),
            "closed program must yield a closed theorem: {source}"
        );
    }
}
