use covalence_core::{Term, Type};
use covalence_kernel_data::numeric::nat::{NatAdditiveLaws, NatArithmetic, NatOrder, NatSyntax};

use super::{DoubleSuccNat, UnaryNat, hol::NativeHol};
use crate::init::{nat, nat_binary};

/// One consumer, compiled unchanged for every representation backend.
fn generic_consumer<N>(
    backend: &N,
) -> std::result::Result<(N::Term, N::Term, N::Term, N::Thm), N::Error>
where
    N: NatArithmetic + NatOrder + NatAdditiveLaws,
{
    let one = backend.nat_literal(1);
    let two = backend.nat_add(one.clone(), one.clone())?;
    let one_lt_two = backend.nat_less_than(backend.nat_literal(1), two.clone())?;
    let add_commutative = backend.nat_add_commutative()?;
    Ok((one, two, one_lt_two, add_commutative))
}

#[test]
fn generic_consumer_accepts_all_nat_representation_backends() {
    let native = generic_consumer(&NativeHol).unwrap();
    let binary = generic_consumer(&DoubleSuccNat).unwrap();
    let unary = generic_consumer(&UnaryNat).unwrap();

    for term in [
        &native.0, &native.1, &binary.0, &binary.1, &unary.0, &unary.1,
    ] {
        assert_eq!(term.type_of().unwrap(), Type::nat());
    }
    for proposition in [&native.2, &binary.2, &unary.2] {
        assert!(proposition.type_of().unwrap().is_bool());
    }
    assert_eq!(native.3.concl(), binary.3.concl());
    assert_eq!(native.3.concl(), unary.3.concl());
}

#[test]
fn binary_literals_have_logarithmic_double_successor_syntax() {
    let native_five = NativeHol.nat_literal(5);
    let binary_five = DoubleSuccNat.nat_literal(5);
    let expected = nat_binary::bit1(nat_binary::bit0(nat_binary::bit1(DoubleSuccNat.nat_zero())));

    assert_eq!(binary_five, expected);
    assert_ne!(binary_five, native_five);
    assert_eq!(binary_five.type_of().unwrap(), Type::nat());
}

fn successor_depth(term: &Term) -> Option<u64> {
    match term.as_app() {
        Some((function, argument)) if function == &nat::nat_succ() => {
            Some(1 + successor_depth(argument)?)
        }
        _ if term == &nat::zero() => Some(0),
        _ => None,
    }
}

#[test]
fn unary_literals_have_linear_successor_depth() {
    let native_five = NativeHol.nat_literal(5);
    let unary_five = UnaryNat.nat_literal(5);
    let expected = (0..5).fold(nat::zero(), |term, _| Term::app(nat::nat_succ(), term));

    assert_eq!(unary_five, expected);
    assert_eq!(successor_depth(&unary_five).unwrap(), 5);
    assert_ne!(unary_five, native_five);
    assert_eq!(unary_five.type_of().unwrap(), Type::nat());
}
