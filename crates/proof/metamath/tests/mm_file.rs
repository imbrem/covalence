//! `.mm` file parsing + round-trip through the **canonical emitter**
//! ([`covalence_metamath::to_mm_string`], `src/emit.rs`).
//!
//! "Round-trip" here means: parse the source, re-emit `.mm` from the parsed
//! [`covalence_metamath::Database`] via the in-crate emitter, parse *that*, and
//! confirm both databases verify and agree on their assertion statements. The
//! test-local emitter this file used to ship has been retired now that the crate
//! has a real one.

use covalence_metamath::{Database, Statement, parse, to_mm_string, verify_all};

const FIXTURE: &str = include_str!("fixtures/demo0.mm");

#[test]
fn parse_mm_file_and_verify() {
    let db = parse(FIXTURE).unwrap();
    assert_eq!(verify_all(&db).unwrap(), 1);
    assert!(db.statement_by_label("th1").is_some());
    assert!(db.statement_by_label("mp").is_some());
}

/// A statement snapshot that ignores `$f`/`$e` labels (the emitter regenerates
/// them — floats globally, essentials per block — so the round-trip contract is
/// *statement* equality: assertion label + conclusion + essential expressions +
/// float typings + `$d`, not hypothesis labels).
fn snapshot(
    db: &Database,
) -> Vec<(
    String,
    String,
    Vec<String>,
    Vec<(String, String)>,
    Vec<(String, String)>,
)> {
    let mut v: Vec<_> = db
        .assertions()
        .map(|a| {
            let mut dd: Vec<(String, String)> = a
                .frame
                .disjoints
                .iter()
                .map(|(x, y)| {
                    if x <= y {
                        (x.clone(), y.clone())
                    } else {
                        (y.clone(), x.clone())
                    }
                })
                .collect();
            dd.sort();
            (
                a.label.clone(),
                a.conclusion.render(),
                a.frame.essentials.iter().map(|h| h.expr.render()).collect(),
                a.frame
                    .floats
                    .iter()
                    .map(|f| (f.typecode.clone(), f.var.clone()))
                    .collect(),
                dd,
            )
        })
        .collect();
    v.sort_by(|x, y| x.0.cmp(&y.0));
    v
}

#[test]
fn roundtrip_through_emitter() {
    let db1 = parse(FIXTURE).unwrap();
    let emitted = to_mm_string(&db1);
    let db2 = parse(&emitted).unwrap_or_else(|e| panic!("re-parse failed: {e}\n---\n{emitted}"));

    // Both verify (the emitted database's proofs still check).
    assert_eq!(verify_all(&db1).unwrap(), 1);
    assert_eq!(verify_all(&db2).unwrap(), 1);

    // The assertion statements agree exactly (label, conclusion, essentials,
    // float typings, and $d).
    assert_eq!(snapshot(&db1), snapshot(&db2));
}

/// The emitter round-trips scoped `$e` hypotheses and `$d` conditions without
/// leaking them into later assertions — the hazard the flat statement list (no
/// `${ $}` markers) creates.
#[test]
fn roundtrip_scopes_and_disjoints() {
    let src = "$c wff |- ( ) -> $.\n$v ph ps $.\n\
               wph $f wff ph $.\nwps $f wff ps $.\n\
               wi $a wff ( ph -> ps ) $.\n\
               ${ $d ph ps $.  h $e |- ph $.  m $a |- ps $. $}\n\
               free $a |- ph $.\n";
    let db1 = parse(src).unwrap();
    let db2 = parse(&to_mm_string(&db1)).unwrap();
    assert_eq!(snapshot(&db1), snapshot(&db2));

    let free = match db2.statement_by_label("free").unwrap() {
        Statement::Assert(a) => a,
        _ => unreachable!(),
    };
    assert!(
        free.frame.essentials.is_empty(),
        "scoped $e leaked into `free`"
    );
    assert!(
        free.frame.disjoints.is_empty(),
        "scoped $d leaked into `free`"
    );
}
