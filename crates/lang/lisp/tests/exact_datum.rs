#![cfg(feature = "hol")]

use covalence_hol_eval::{defs, mk_blob, mk_int};
use covalence_init::init::ext::TermExt;
use covalence_init::{Term, Type};
use covalence_lisp::carrier::exact_datum_theory;
use covalence_types::Int;

fn theorem_rhs(theorem: &covalence_hol_eval::EvalThm) -> &Term {
    theorem.concl().as_eq().expect("equational theorem").1
}

#[test]
fn integer_predicate_distinguishes_payload_variants() {
    let theory = exact_datum_theory().unwrap();
    let integer = defs::inl(Type::int(), Type::bytes())
        .apply(mk_int(Int::from(7i128)))
        .unwrap();
    let symbol = defs::inr(Type::int(), Type::bytes())
        .apply(mk_blob(b"seven".to_vec()))
        .unwrap();

    let integer_thm = theory.integer_atom(&integer).unwrap();
    let symbol_thm = theory.integer_atom(&symbol).unwrap();
    assert!(integer_thm.hyps().is_empty());
    assert!(symbol_thm.hyps().is_empty());
    assert_eq!(
        theorem_rhs(&integer_thm).as_bool(),
        Some(true),
        "{}",
        integer_thm.concl()
    );
    assert_eq!(
        theorem_rhs(&symbol_thm).as_bool(),
        Some(false),
        "{}",
        symbol_thm.concl()
    );
}

#[test]
fn integer_predicate_rejects_structural_values() {
    let theory = exact_datum_theory().unwrap();
    let nil_thm = theory.integer_nil().unwrap();
    let cons_thm = theory
        .integer_cons(&theory.sexpr.snil, &theory.sexpr.snil)
        .unwrap();
    assert!(nil_thm.hyps().is_empty());
    assert!(cons_thm.hyps().is_empty());
    assert_eq!(theorem_rhs(&nil_thm).as_bool(), Some(false));
    assert_eq!(theorem_rhs(&cons_thm).as_bool(), Some(false));
}
