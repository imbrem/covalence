//! Smoke tests for the content-hash sidecar.

use covalence_core::{Term, Type};
use covalence_hol::hash::{Hasher, UnitObsHasher, hash_term, hash_type};

#[test]
fn alpha_equivalent_terms_hash_identically() {
    let a = Term::abs("x", Type::bytes(), Term::bound(0));
    let b = Term::abs("y", Type::bytes(), Term::bound(0));
    assert_eq!(hash_term(&a, &UnitObsHasher), hash_term(&b, &UnitObsHasher));
}

#[test]
fn structurally_distinct_terms_hash_differently() {
    let a = Term::free("x", Type::bytes());
    let b = Term::free("y", Type::bytes());
    assert_ne!(hash_term(&a, &UnitObsHasher), hash_term(&b, &UnitObsHasher));
}

#[test]
fn type_hashes_are_stable() {
    let a = Type::fun(Type::bytes(), Type::prop());
    let b = Type::fun(Type::bytes(), Type::prop());
    assert_eq!(hash_type(&a, &UnitObsHasher), hash_type(&b, &UnitObsHasher));
}

#[test]
fn cached_hasher_matches_stateless() {
    let t = Term::all("x", Type::bytes(), Term::eq(Term::bound(0), Term::bound(0)));
    let stateless = hash_term(&t, &UnitObsHasher);
    let mut h = Hasher::new();
    assert_eq!(h.hash_term(&t, &UnitObsHasher), stateless);
    // second query hits the cache
    assert_eq!(h.hash_term(&t, &UnitObsHasher), stateless);
}

#[test]
fn free_var_type_is_part_of_hash() {
    let a = Term::free("x", Type::bytes());
    let b = Term::free("x", Type::tycon("bool", vec![]));
    assert_ne!(hash_term(&a, &UnitObsHasher), hash_term(&b, &UnitObsHasher));
}

#[test]
fn const_distinct_from_free_with_same_name() {
    let f = Term::free("c", Type::bytes());
    let c = Term::const_("c", Type::bytes());
    assert_ne!(hash_term(&f, &UnitObsHasher), hash_term(&c, &UnitObsHasher));
}
