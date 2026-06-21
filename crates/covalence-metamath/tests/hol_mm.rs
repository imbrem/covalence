//! Real-world ingestion: parse and fully verify the vendored `hol.mm` database.
//!
//! `hol.mm` (CC0 / public domain, vendored under `tests/fixtures/hol.mm`) is a
//! complete HOL formalisation in Metamath: 151 `$p` theorems with all-NORMAL
//! (uncompressed) proofs and no `$[ include $]`s. It exercises the parser,
//! mandatory-frame computation, the RPN proof checker, and — critically — the
//! distinct-variable (`$d`) handling against the theorem's *full* in-scope `$d`
//! set (including dummy/working variables), which a mandatory-filtered set would
//! reject spuriously (the original `cl`/`clf` bug).
//!
//! Verifying ~97 KB is fast, so this is a normal (non-ignored) test.

use covalence_metamath::{parse, verify_all};

#[test]
fn hol_mm_parses_and_fully_verifies() {
    let src = include_str!("fixtures/hol.mm");
    let db = parse(src).expect("hol.mm should parse");
    let verified = verify_all(&db).expect("hol.mm should fully verify");
    assert_eq!(verified, 151, "expected all 151 $p theorems in hol.mm to verify");
}
