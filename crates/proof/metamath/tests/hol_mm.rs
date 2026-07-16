//! Real-world ingestion: parse and fully verify the vendored `hol.mm` database.
//!
//! `hol.mm` (CC0 / public domain, vendored under `tests/fixtures/hol.mm`) is a
//! complete HOL formalisation in Metamath: 151 `$p` theorems with COMPRESSED
//! (`( labels ) LETTERS`) proofs and no `$[ include $]`s. It exercises the
//! parser, mandatory-frame computation, the RPN proof checker, and — critically
//! — the distinct-variable (`$d`) handling against the theorem's *full* in-scope
//! `$d` set (including dummy/working variables), which a mandatory-filtered set
//! would reject spuriously (the original `cl`/`clf` bug).
//!
//! Verifying ~97 KB is fast, so this is a normal (non-ignored) test.

use covalence_metamath::{parse, verify_all};

#[test]
fn hol_mm_parses_and_fully_verifies() {
    let src = include_str!("fixtures/hol.mm");
    let db = parse(src).expect("hol.mm should parse");
    let verified = verify_all(&db).expect("hol.mm should fully verify");
    assert_eq!(
        verified, 151,
        "expected all 151 $p theorems in hol.mm to verify"
    );
}

/// Round-trip `hol.mm` through the canonical emitter
/// ([`covalence_metamath::to_mm_string`]): parse → emit → re-parse, and confirm
/// all 151 theorems still verify. This is the emitter's toughest in-tree case —
/// it exercises shared `$e` hypotheses (re-labelled per block), full-scope `$d`
/// (dummy variables), and compressed proofs (positional, so re-labelling leaves
/// them untouched).
#[test]
fn hol_mm_round_trips_through_emitter() {
    use covalence_metamath::to_mm_string;
    let src = include_str!("fixtures/hol.mm");
    let db1 = parse(src).unwrap();
    assert_eq!(verify_all(&db1).unwrap(), 151);
    let emitted = to_mm_string(&db1);
    let db2 = parse(&emitted).unwrap_or_else(|e| panic!("re-parse of emitted hol.mm failed: {e}"));
    assert_eq!(
        verify_all(&db2).unwrap(),
        151,
        "all 151 hol.mm theorems must re-verify after emit → re-parse"
    );
}
