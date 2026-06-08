//! Integration test exercising the full stdlib end-to-end —
//! Pure primitives + HOL axioms + closed-form reduction across
//! all major modules.

use covalence_pure::{TermKind, Thm};
use covalence_shell::stdlib::{bytes, byte, either, fun, int, list, nat, option, rat, real};

fn rhs(t: covalence_pure::Term) -> covalence_pure::Term {
    let thm = Thm::reduce_prim(t).unwrap();
    match thm.concl().kind() {
        TermKind::Eq(_, r) => r.clone(),
        _ => panic!(),
    }
}

#[test]
fn nat_arithmetic_chain_reduces() {
    // (2 + 3) * 4 = 20
    let inner = nat::add(nat::lit(2u32), nat::lit(3u32));
    let inner_red = rhs(inner);
    assert_eq!(inner_red, nat::lit(5u32));
    let outer = nat::mul(inner_red, nat::lit(4u32));
    assert_eq!(rhs(outer), nat::lit(20u32));
}

#[test]
fn int_negation_chain() {
    let n = int::neg(int::lit(covalence_types::Int::from_sign_nat(
        covalence_types::Sign::Positive,
        covalence_types::Nat::from_inner(5u32.into()),
    )));
    let neg_5 = rhs(n.clone());
    let back = int::neg(neg_5);
    assert_eq!(
        rhs(back),
        int::lit(covalence_types::Int::from_sign_nat(
            covalence_types::Sign::Positive,
            covalence_types::Nat::from_inner(5u32.into())
        ))
    );
}

#[test]
fn bytes_concat_and_slice() {
    let a = bytes::blob(vec![1u8, 2, 3]);
    let b = bytes::blob(vec![4u8, 5]);
    let combined = rhs(bytes::cat(a, b));
    assert_eq!(combined, bytes::blob(vec![1u8, 2, 3, 4, 5]));
    let sliced = rhs(bytes::slice(combined, nat::lit(1u32), nat::lit(3u32)));
    assert_eq!(sliced, bytes::blob(vec![2u8, 3, 4]));
}

#[test]
fn nat_to_int_round_trips() {
    let n = nat::to_int(nat::lit(42u32));
    let result = rhs(n);
    let expected = int::lit(covalence_types::Int::from_sign_nat(
        covalence_types::Sign::Positive,
        covalence_types::Nat::from_inner(42u32.into()),
    ));
    assert_eq!(result, expected);
}

#[test]
fn axiom_set_well_formed_across_stdlib() {
    // A spot-check from each module — every axiom is at least
    // Prop-typed and self-hyp'd.
    let axioms = vec![
        ("nat induction", nat::axiom_induction()),
        ("int add_neg_r", int::axiom_add_neg_r()),
        ("fun id_def", fun::axiom_id_def()),
        ("list induction", list::axiom_list_induction()),
        ("option some_inj", option::axiom_some_inj()),
        ("either either_cases", either::axiom_either_cases()),
        ("bytes induction", bytes::axiom_bytes_induction()),
        ("byte u8 round_trip", byte::axiom_u8_round_trip()),
        ("rat mul_inv", rat::axiom_mul_inv()),
        ("real completeness", real::axiom_completeness()),
    ];
    for (name, ax) in axioms {
        assert!(
            ax.concl().type_of().unwrap().is_prop(),
            "{name}: concl not prop"
        );
        assert_eq!(ax.hyps().len(), 1, "{name}: self-hyp pattern broken");
    }
}

#[test]
fn lists_compose_with_nats() {
    // Build a list [1, 2, 3] : list nat and check the type works
    // through the polymorphic typecon.
    let xs = list::cons(
        nat::lit(1u32),
        list::cons(
            nat::lit(2u32),
            list::cons(nat::lit(3u32), list::nil_at(nat::ty())),
        ),
    );
    assert_eq!(xs.type_of().unwrap(), list::ty(nat::ty()));
}

#[test]
fn options_round_trip() {
    let some_42 = option::some(nat::lit(42u32));
    assert_eq!(some_42.type_of().unwrap(), option::ty(nat::ty()));
}

#[test]
fn fun_composition_types_check() {
    // compose succ succ : nat → nat (compose at nat, nat, nat)
    let nat_ty = nat::ty();
    let comp = fun::compose_at(nat_ty.clone(), nat_ty.clone(), nat_ty.clone());
    let succ = nat::succ_fn();
    let succ_succ = covalence_pure::Term::app(
        covalence_pure::Term::app(comp, succ.clone()),
        succ,
    );
    assert_eq!(
        succ_succ.type_of().unwrap(),
        covalence_pure::Type::fun(nat_ty.clone(), nat_ty)
    );
}
