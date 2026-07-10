//! End-to-end proof of concept: read the repo's real `docs/deps/` TCB
//! artifacts, dump them to SQLite, reload, and assert the round-trip is exact
//! — plus a few semantic queries against known-golden facts.

use std::path::Path;

use covalence_sqlite::{Connection, open_memory};
use covalence_tcb_db::{TcbShape, dump, load, read_shape};

/// The repo root, relative to this crate (`crates/app/tcb-db`).
fn repo_root() -> &'static Path {
    Path::new(concat!(env!("CARGO_MANIFEST_DIR"), "/../../.."))
}

fn shape_and_db() -> (TcbShape, Connection) {
    let shape = read_shape(repo_root()).expect("docs/deps artifacts readable");
    let mut conn = open_memory().expect("in-memory db");
    dump(&shape, &mut conn).expect("dump");
    (shape, conn)
}

#[test]
fn roundtrip_is_exact() {
    let (shape, conn) = shape_and_db();
    let reloaded = load(&conn).expect("load");
    assert_eq!(shape, reloaded);
}

#[test]
fn shape_matches_known_goldens() {
    let (shape, conn) = shape_and_db();

    // The three pinned languages are present, non-empty, in MANIFESTS order.
    let names: Vec<&str> = shape
        .languages
        .iter()
        .map(|l| l.language.as_str())
        .collect();
    assert_eq!(names, ["CoreLang", "CoreEval", "Builtins"]);
    assert!(shape.languages.iter().all(|l| !l.rules.is_empty()));

    // Query side: `Refl` is an admitted rule of CoreLang (a golden fact —
    // docs/deps/core-manifest.txt line 1).
    let refl_lang: String = conn
        .query_row(
            "SELECT language FROM language_rules WHERE rule = 'Refl' AND position = 0",
            [],
            |r| r.get(0),
        )
        .expect("Refl admitted");
    assert_eq!(refl_lang, "CoreLang");

    // Query side: nat.add is a Builtins canon op.
    let n: i64 = conn
        .query_row(
            "SELECT COUNT(*) FROM language_rules WHERE language = 'Builtins' AND rule = 'nat.add'",
            [],
            |r| r.get(0),
        )
        .unwrap();
    assert_eq!(n, 1);

    // Every config's stored mint-site COUNT equals its dumped location rows
    // (internal consistency of tcb-audit.json, checked through SQL).
    let mismatches: i64 = conn
        .query_row(
            "SELECT COUNT(*) FROM configs c
             WHERE c.mint_sites !=
                   (SELECT COUNT(*) FROM mint_sites m WHERE m.config = c.name)",
            [],
            |r| r.get(0),
        )
        .unwrap();
    assert_eq!(mismatches, 0, "mintSites count != mintSiteLocations rows");

    // The trusted base has zero `unsafe` (a standing audit invariant).
    let unsafe_in_base: i64 = conn
        .query_row(
            "SELECT unsafe_count FROM configs WHERE name = 'base'",
            [],
            |r| r.get(0),
        )
        .unwrap();
    assert_eq!(unsafe_in_base, 0);

    // Every mint site lives in the trusted base sources — the whole point of
    // the single-gate design (any mint outside trusted/src would be a hole).
    let stray: i64 = conn
        .query_row(
            "SELECT COUNT(*) FROM mint_sites
             WHERE file NOT LIKE 'crates/kernel/base/trusted/src/%'",
            [],
            |r| r.get(0),
        )
        .unwrap();
    assert_eq!(stray, 0, "mint site outside crates/kernel/base/trusted/src");
}

#[test]
fn file_backed_db_roundtrips_too() {
    // The deliverable is "dump a TCB to a .db" — exercise the file path, not
    // just :memory:.
    let shape = read_shape(repo_root()).expect("docs/deps artifacts readable");
    let dir = std::env::temp_dir().join(format!("covalence-tcb-db-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("tcb.db");
    let _ = std::fs::remove_file(&path);
    {
        let mut conn = covalence_sqlite::open(&path).expect("open file db");
        dump(&shape, &mut conn).expect("dump");
    }
    let conn = covalence_sqlite::open(&path).expect("reopen file db");
    assert_eq!(load(&conn).expect("load"), shape);
    drop(conn);
    let _ = std::fs::remove_dir_all(&dir);
}
