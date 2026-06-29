//! `Stmt` (and friends) support serde — the *untrusted* statement form. `MThm`
//! deliberately does NOT (deserializing a theorem would forge one); you
//! serialize `thm.into_stmt()` and re-derive on the way back.
#![cfg(feature = "serde")]

use covalence_pure::Stmt;

#[test]
fn stmt_serde_roundtrip() {
    let s = Stmt {
        ctx: 1u32,
        prop: vec![2u8, 3, 4],
    };
    let json = serde_json::to_string(&s).unwrap();
    let back: Stmt<u32, Vec<u8>> = serde_json::from_str(&json).unwrap();
    assert_eq!(s, back);
}
