//! End-to-end battery for the **ACL2 book import pipeline**
//! ([`covalence_lisp::book`]) — the honest tally contract.
//!
//! # The contract these tests pin
//!
//! - **Exact tallies**: each fixture book's per-event outcomes are asserted
//!   exactly — nothing is silently dropped or upgraded.
//! - **Transported means transported**: every event the tally claims as
//!   *transported* is independently re-checked here — the stored theorem
//!   exists, is **hypothesis-free**, and was proved on the reified
//!   certificate path; spot checks assert the exact base-HOL statements.
//! - **Rejections are honest**: free-variable `defthm`s are rejected naming
//!   induction; false ground goals are refuted; unsupported events carry
//!   reasons. Nothing is stored for a rejected `defthm`.
//! - **Confinement**: `..`, absolute paths, and missing top-level books are
//!   clean errors before any file is touched.
#![cfg(feature = "hol")]

use std::path::{Path, PathBuf};

use covalence_lisp::acl2::{Acl2Proof, Acl2Session};
use covalence_lisp::book::{BookReport, EventOutcome, Tally, run_book};
use covalence_lisp::session::Session;

/// The fixture root: `crates/lang/lisp/tests`.
fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests")
}

fn session() -> Acl2Session {
    Acl2Session::new().expect("session")
}

/// The honesty boundary, re-checked from outside the pipeline: every event
/// the report claims as *transported* has a stored theorem that is
/// hypothesis-free and certificate-proved.
fn check_transported(sess: &Acl2Session, report: &BookReport) {
    for e in &report.events {
        if e.outcome == EventOutcome::Transported {
            let entry = sess
                .theorem_entry(&e.label)
                .unwrap_or_else(|| panic!("transported `{}` must be stored", e.label));
            assert!(
                entry.thm.hyps().is_empty(),
                "transported `{}` must be hyps-free, got {:?}",
                e.label,
                entry.thm.hyps()
            );
            assert!(
                matches!(entry.proof, Acl2Proof::Certificate { .. }),
                "transported `{}` must ride the certificate path",
                e.label
            );
        }
    }
}

fn outcome<'r>(report: &'r BookReport, label: &str) -> &'r EventOutcome {
    &report
        .event(label)
        .unwrap_or_else(|| panic!("no event `{label}` in the report"))
        .outcome
}

fn rejected_reason<'r>(report: &'r BookReport, label: &str) -> &'r str {
    match outcome(report, label) {
        EventOutcome::Rejected { reason } => reason,
        other => panic!("`{label}` must be rejected, got {other:?}"),
    }
}

// ---- the basics book: defuns + ground lemmas + honest rejections ----------

#[test]
fn app_basics_book_exact_tally() {
    let mut s = session();
    let report = run_book(&mut s, &root(), "books/app-basics").expect("book runs");

    // The exact tally: 11 events — 2 transported (four, car-app), 6 admitted
    // (3 defuns + 3 reduction defthms), 1 skipped (in-package), 2 rejected
    // (the induction-needing defthms).
    assert_eq!(
        report.tally(),
        Tally {
            transported: 2,
            admitted: 6,
            skipped: 1,
            rejected: 2,
        },
        "tally mismatch:\n{report}"
    );
    check_transported(&s, &report);

    // Per-event spot checks.
    assert_eq!(*outcome(&report, "four"), EventOutcome::Transported);
    assert_eq!(*outcome(&report, "car-app"), EventOutcome::Transported);
    assert_eq!(*outcome(&report, "app"), EventOutcome::Admitted { hyps: 0 });
    // Reduction-path defthms ride their defun equations as hypotheses.
    for name in ["app-ab-c", "rev-rev-ab", "len2-abc"] {
        match outcome(&report, name) {
            EventOutcome::Admitted { hyps } => {
                assert!(*hyps > 0, "`{name}` must ride defun hypotheses")
            }
            other => panic!("`{name}` must be admitted, got {other:?}"),
        }
        let thm = s.theorem(name).expect("stored");
        assert!(!thm.hyps().is_empty());
        assert!(thm.concl().as_eq().is_some(), "concl is the equation goal");
    }
    // The induction wall, named honestly; nothing stored.
    for name in ["app-assoc", "len2-app"] {
        let reason = rejected_reason(&report, name);
        assert!(
            reason.contains("induction"),
            "`{name}` must name induction: {reason}"
        );
        assert!(s.theorem(name).is_none(), "nothing may be stored");
    }

    // The defuns are genuinely installed.
    for f in ["app", "rev", "len2"] {
        assert!(s.defs().contains(f), "defun `{f}` must be installed");
    }
}

/// The exact transported statement for `four` — the base-HOL model equation
/// `⊢ aplus (aint 2) (aint 2) = aint 4` (the dialect's S3 gate, reached
/// through the book pipeline).
#[test]
fn app_basics_transported_statement_exact() {
    use covalence_init::init::acl2::derivable::ground_env;
    use covalence_init::init::ext::TermExt;

    let mut s = session();
    let report = run_book(&mut s, &root(), "books/app-basics").expect("book runs");
    assert_eq!(*outcome(&report, "four"), EventOutcome::Transported);

    let e = ground_env().expect("ground env");
    let tm = &*e.tm;
    let aint = |i: i128| tm.th.aint_at(&covalence_hol_eval::mk_int(i)).unwrap();
    let expected = tm
        .pr
        .plus
        .clone()
        .apply(aint(2))
        .unwrap()
        .apply(aint(2))
        .unwrap()
        .equals(aint(4))
        .unwrap();
    let entry = s.theorem_entry("four").expect("stored");
    assert!(entry.thm.hyps().is_empty());
    assert_eq!(entry.thm.concl(), &expected, "the model equation, exactly");

    // And `car-app`: ⊢ car (acons (asym "a") (acons (asym "b") anil)) = asym "a".
    let sym = |n: &str| tm.sym(n.as_bytes()).unwrap();
    let acons = |h: covalence_init::Term, t: covalence_init::Term| {
        tm.th.cons.clone().apply(h).unwrap().apply(t).unwrap()
    };
    let lst = acons(sym("a"), acons(sym("b"), tm.th.nil.clone()));
    let expected = tm
        .th
        .car
        .clone()
        .apply(lst)
        .unwrap()
        .equals(sym("a"))
        .unwrap();
    let entry = s.theorem_entry("car-app").expect("stored");
    assert!(entry.thm.hyps().is_empty());
    assert_eq!(entry.thm.concl(), &expected, "the model equation, exactly");
}

// ---- the deliberately-mixed book: every tally category --------------------

#[test]
fn mixed_book_exact_tally() {
    let mut s = session();
    let report = run_book(&mut s, &root(), "books/mixed").expect("book runs");

    // 13 own events + 11 nested (app-basics via include-book) = 24:
    //  transported: three-with-hints + nested {four, car-app}          = 3
    //  admitted:    pair-up-a + nested {app, rev, len2, app-ab-c,
    //               rev-rev-ab, len2-abc}                              = 7
    //  skipped:     in-package ×2 (own + nested), include ×4 (satisfied,
    //               re-include, missing, :dir), local defun            = 7
    //  rejected:    consp-implies, bogus, defmacro, encapsulate,
    //               mutual-recursion + nested {app-assoc, len2-app}    = 7
    assert_eq!(
        report.tally(),
        Tally {
            transported: 3,
            admitted: 7,
            skipped: 7,
            rejected: 7,
        },
        "tally mismatch:\n{report}"
    );
    check_transported(&s, &report);

    // The include-book rows, one per flavour.
    let includes: Vec<_> = report
        .events
        .iter()
        .filter(|e| e.kind == "include-book")
        .collect();
    assert_eq!(includes.len(), 4);
    let reasons: Vec<_> = includes
        .iter()
        .map(|e| match &e.outcome {
            EventOutcome::Skipped { reason } => reason.as_str(),
            other => panic!("include-book must be skipped, got {other:?}"),
        })
        .collect();
    assert!(reasons[0].contains("included"), "satisfied: {}", reasons[0]);
    assert!(
        reasons[1].contains("already included"),
        "idempotent: {}",
        reasons[1]
    );
    assert!(reasons[2].contains("not found"), "missing: {}", reasons[2]);
    assert!(reasons[3].contains(":dir"), "system dir: {}", reasons[3]);

    // Nested events carry the included book's path.
    let four = report.event("four").expect("nested four");
    assert_eq!(four.book, "books/app-basics.lisp");
    assert_eq!(report.path, "books/mixed.lisp");

    // local: processed (pair-up IS installed and usable) but tallied skipped.
    match outcome(&report, "pair-up") {
        EventOutcome::Skipped { reason } => assert!(reason.contains("local"), "got: {reason}"),
        other => panic!("local defun must be skipped-as-local, got {other:?}"),
    }
    assert!(s.defs().contains("pair-up"), "local defun is installed");
    match outcome(&report, "pair-up-a") {
        EventOutcome::Admitted { hyps } => assert!(*hyps > 0),
        other => panic!("pair-up-a must be admitted, got {other:?}"),
    }

    // :hints / :rule-classes ignored but RECORDED.
    let hinted = report.event("three-with-hints").expect("event");
    assert_eq!(hinted.outcome, EventOutcome::Transported);
    assert_eq!(
        hinted.notes,
        vec![":hints ignored".to_string(), ":rule-classes ignored".into()]
    );

    // Honest rejections, with reasons.
    assert!(rejected_reason(&report, "consp-implies").contains("induction"));
    assert!(rejected_reason(&report, "bogus").contains("FALSE"));
    for class in ["defmacro", "encapsulate", "mutual-recursion"] {
        let rec = report
            .events
            .iter()
            .find(|e| e.kind == class)
            .unwrap_or_else(|| panic!("no `{class}` event"));
        match &rec.outcome {
            EventOutcome::Rejected { reason } => {
                assert!(reason.contains("not supported"), "got: {reason}")
            }
            other => panic!("`{class}` must be rejected, got {other:?}"),
        }
    }
    // Nothing was stored for the rejected defthms.
    for name in ["consp-implies", "bogus", "hidden"] {
        assert!(s.theorem(name).is_none(), "`{name}` must not be stored");
    }
}

// ---- confinement -----------------------------------------------------------

#[test]
fn book_paths_are_confined() {
    let mut s = session();
    let r = root();
    // `..` components are rejected lexically (before touching the fs).
    let err = run_book(&mut s, &r, "../src/lib").unwrap_err();
    assert!(err.to_string().contains(".."), "got: {err}");
    // Absolute paths are rejected.
    let abs = r.join("books/app-basics.lisp");
    let err = run_book(&mut s, &r, abs.to_str().unwrap()).unwrap_err();
    assert!(err.to_string().contains("absolute"), "got: {err}");
    // A missing top-level book is a clean error (only missing *dependencies*
    // are tallied skips).
    let err = run_book(&mut s, &r, "books/no-such").unwrap_err();
    assert!(err.to_string().contains("not found"), "got: {err}");
    // Nothing was processed.
    assert!(s.defs().is_empty());
}

// ---- the #book directive through the Session --------------------------------

#[test]
fn book_directive_prints_tally_and_is_confined() {
    let mut s = Session::new().expect("session");
    s.set_book_root(Some(root()));

    // #book requires #lang acl2.
    let err = s.eval_cell("#book books/app-basics").unwrap_err();
    assert!(err.to_string().contains("acl2"), "got: {err}");

    s.eval_cell("#lang acl2").unwrap();
    let out = s.eval_cell("#book books/app-basics").unwrap();
    assert!(
        out.contains("2 of 11 event(s) transported to closed base-HOL theorems"),
        "summary line missing:\n{out}"
    );
    assert!(out.contains("6 admitted"), "got:\n{out}");
    assert!(out.contains("2 rejected"), "got:\n{out}");
    // The session genuinely holds the book's state now.
    assert_eq!(s.acl2().theorem("four").map(|t| t.hyps().len()), Some(0));
    assert!(s.acl2().defs().contains("app"));

    // Confinement through the directive.
    let err = s.eval_cell("#book ../src/lib").unwrap_err();
    assert!(err.to_string().contains(".."), "got: {err}");

    // A disabled root refuses cleanly.
    s.set_book_root(None);
    let err = s.eval_cell("#book books/app-basics").unwrap_err();
    assert!(err.to_string().contains("root"), "got: {err}");
}
