//! Source-driven integration tests for `covalence-egglog`.
//!
//! These tests round-trip through the parser + lowering: write a small
//! egglog program as a Rust string, feed it to
//! [`covalence_egglog::ingest_source`], and assert the resulting `Thm`
//! exists. The lowering is restricted to Fiat-only ground equalities —
//! the `(prove …)` target must syntactically match a previous
//! `(union …)`. Derived equalities (via Trans / Sym / Congr) wait until
//! we ingest real proof DAGs from upstream egglog.

use covalence_egglog::ast::{Command, Expr};
use covalence_egglog::{BridgeError, KernelEgglogBridge, ingest_source, parse_program};
use covalence_kernel::Kernel;

// =====================================================================
// Parser smoke tests — round-trip a few command shapes
// =====================================================================

#[test]
fn parse_sort_and_constructor() {
    let src = r#"
        ; declare an EUF universe
        (sort U)
        (constructor a () U)
        (constructor f (U) U)
    "#;
    let cmds = parse_program(src).unwrap();
    assert_eq!(
        cmds,
        vec![
            Command::Sort("U".into()),
            Command::Constructor {
                name: "a".into(),
                params: vec![],
                result: "U".into(),
            },
            Command::Constructor {
                name: "f".into(),
                params: vec!["U".into()],
                result: "U".into(),
            },
        ]
    );
}

#[test]
fn parse_datatype_sugar() {
    let cmds = parse_program("(datatype Math (Num) (Add Math Math))").unwrap();
    assert_eq!(
        cmds,
        vec![Command::Datatype {
            name: "Math".into(),
            ctors: vec![
                ("Num".into(), vec![]),
                ("Add".into(), vec!["Math".into(), "Math".into()]),
            ],
        }]
    );
}

#[test]
fn parse_union_and_prove() {
    let cmds = parse_program("(union a b) (prove (= a b))").unwrap();
    assert_eq!(
        cmds,
        vec![
            Command::Union(Expr::Sym("a".into()), Expr::Sym("b".into())),
            Command::Prove(Expr::Sym("a".into()), Expr::Sym("b".into())),
        ]
    );
}

#[test]
fn parse_app_term() {
    let cmds = parse_program("(union (f a) (f b))").unwrap();
    assert_eq!(
        cmds,
        vec![Command::Union(
            Expr::App("f".into(), vec![Expr::Sym("a".into())]),
            Expr::App("f".into(), vec![Expr::Sym("b".into())]),
        )]
    );
}

#[test]
fn parse_unknown_command_rejected() {
    let err = parse_program("(check (= a b))").expect_err("check is not supported yet");
    assert!(matches!(err, BridgeError::Malformed(_)));
}

// =====================================================================
// End-to-end: source → kernel-checked Thm
// =====================================================================

#[test]
fn euf_source_round_trips_with_constants() {
    let src = r#"
        (sort U)
        (constructor a () U)
        (constructor b () U)
        (union a b)
        (prove (= a b))
    "#;
    let mut kernel = Kernel::new();
    let mut bridge = KernelEgglogBridge::new(&mut kernel);
    let _thm = ingest_source(&mut bridge, src).expect("source EUF should close");
}

#[test]
fn euf_source_round_trips_with_application() {
    // Ground equality over an application — exercises term materialisation
    // through the parser → lower → ingest pipeline.
    let src = r#"
        (sort U)
        (constructor a () U)
        (constructor b () U)
        (constructor f (U) U)
        (union (f a) (f b))
        (prove (= (f a) (f b)))
    "#;
    let mut kernel = Kernel::new();
    let mut bridge = KernelEgglogBridge::new(&mut kernel);
    let _thm = ingest_source(&mut bridge, src).expect("EUF over (f a) = (f b) should close");
}

#[test]
fn datatype_sugar_round_trips() {
    // `(datatype Name (Ctor ...) ...)` registers a sort + per-variant
    // constructors. We assert an equality between two 0-ary variants.
    let src = r#"
        (datatype Color (Red) (Green) (Blue))
        (union Red Blue)
        (prove (= Red Blue))
    "#;
    let mut kernel = Kernel::new();
    let mut bridge = KernelEgglogBridge::new(&mut kernel);
    let _thm = ingest_source(&mut bridge, src).expect("datatype sugar should close");
}

#[test]
fn prove_lookup_handles_reversed_union() {
    // `(union a b)` then `(prove (= b a))` — the lowering indexes both
    // orderings of every union into the prove-lookup map.
    let src = r#"
        (sort U)
        (constructor a () U)
        (constructor b () U)
        (union a b)
        (prove (= b a))
    "#;
    let mut kernel = Kernel::new();
    let mut bridge = KernelEgglogBridge::new(&mut kernel);
    let _thm = ingest_source(&mut bridge, src).expect("reversed prove lookup should hit");
}

// =====================================================================
// Negative paths — loud, structured failures
// =====================================================================

#[test]
fn prove_without_matching_union_rejected() {
    // The Fiat-only lowering can only close `(prove …)` whose sides were
    // previously `union`'d. A bare prove (no derivation) errors loud.
    let src = r#"
        (sort U)
        (constructor a () U)
        (constructor b () U)
        (prove (= a b))
    "#;
    let mut kernel = Kernel::new();
    let mut bridge = KernelEgglogBridge::new(&mut kernel);
    let err =
        ingest_source(&mut bridge, src).expect_err("derivation from source is not yet supported");
    assert!(matches!(err, BridgeError::Malformed(_)));
}

#[test]
fn program_without_prove_rejected() {
    let src = r#"
        (sort U)
        (constructor a () U)
    "#;
    let mut kernel = Kernel::new();
    let mut bridge = KernelEgglogBridge::new(&mut kernel);
    let err = ingest_source(&mut bridge, src).expect_err("no (prove …) is a hard error");
    assert!(matches!(err, BridgeError::Malformed(_)));
}
