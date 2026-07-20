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

use covalence_hash::sha256;
use covalence_lisp::acl2::{Acl2Proof, Acl2Session};
use covalence_lisp::book::{
    BookConfig, BookReport, CompletenessCount, CompletenessLevel, EventOutcome, EventRecord,
    ImportClass, IncludeStatus, SourceClosureStatus, SourceRole, SourceStatus, Tally,
    TheoremNeutralCapability, TheoremNeutralInterface, run_book, run_book_with_config,
};
use covalence_lisp::progress::{
    NormalizedEventIdentity, NormalizedEventScope, PinnedNormalizedDenominator, ProgressMode,
};
use covalence_lisp::reader::read_book;
use covalence_lisp::session::Session;
use covalence_lisp::world::Acl2World;

/// The fixture root: `crates/lang/lisp/tests`.
fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests")
}

fn sha256_bytes(hex: &str) -> [u8; 32] {
    assert_eq!(hex.len(), 64);
    let mut out = [0; 32];
    for (i, byte) in out.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&hex[i * 2..i * 2 + 2], 16).expect("SHA-256 hex");
    }
    out
}

#[test]
fn macro_lambda_lists_bind_optional_guarded_keys_and_supplied_flags() {
    let forms = read_book(
        "(defmacro advanced (name
                              &optional (suffix 'nil suffix-p)
                              &key
                              ((body true-listp) 'nil body-p)
                              ((:enabled enabledp) 'nil enabled-supplied-p))
            `(progn
               ,@(and suffix-p `((table suffix ',suffix)))
               ,@(and body-p `((table body ',body)))
               ,@(and enabled-supplied-p `((table enabled ',enabledp)))
               (defthm ,name t)))
         (advanced sample extra :body (one two) :enabled t)",
    )
    .unwrap();
    let mut world = Acl2World::new();
    assert!(world.process_event(&forms[0]).unwrap());
    assert_eq!(
        world.expand_macro_call(&forms[1]).unwrap().unwrap(),
        read_book(
            "(progn
               (table suffix 'extra)
               (table body '(one two))
               (table enabled 't)
               (defthm sample t))"
        )
        .unwrap()
        .remove(0)
    );
}

#[test]
fn make_event_evaluator_handles_dotted_calls_mk_name_and_ignored_bstar_names() {
    let forms = read_book(
        "(defun generator (size)
            (b* ((?str-size (if (eql size 8) \"08\" size))
                 (name (mk-name \"N\" str-size)))
              `(defconst ,name ,size)))
         (make-event (generator . (8)))",
    )
    .unwrap();
    let mut world = Acl2World::new();
    assert!(world.process_event(&forms[0]).unwrap());
    assert_eq!(
        world.eval_make_event(&forms[1]).unwrap(),
        read_book("(defconst n08 8)").unwrap().remove(0)
    );
}

#[test]
fn make_event_primitives_preserve_put_assoc_acl2_data_semantics() {
    let forms = read_book(
        "(make-event
           (let ((updated
                   (put-assoc :b 9 '((:a . 1) (:b . 2) (:c . 3)))))
             `(defconst *updated-alist* ',updated)))
         (make-event
           (let ((extended (put-assoc-equal :b 2 '((:a . 1)))))
             `(defconst *extended-alist* ',extended)))",
    )
    .unwrap();
    let mut world = Acl2World::new();
    assert_eq!(
        world.eval_make_event(&forms[0]).unwrap(),
        read_book("(defconst *updated-alist* '((:a . 1) (:b . 9) (:c . 3)))")
            .unwrap()
            .remove(0)
    );
    assert_eq!(
        world.eval_make_event(&forms[1]).unwrap(),
        read_book("(defconst *extended-alist* '((:a . 1) (:b . 2)))")
            .unwrap()
            .remove(0)
    );
}

#[test]
fn bstar_unary_fty_binders_destructure_existing_inst_and_opcode_values() {
    let forms = read_book(
        "(make-event
           (let ((inst '(inst \"MOV\" (op :op 137 :feat (:sse2)) (arg) impl nil)))
             (b* (((inst inst))
                  (opcode inst.opcode)
                  ((opcode opcode))
                  (operands inst.operands)
                  ((operands operands)))
               `(defconst *decoded-fields*
                  '(,inst.mnemonic ,opcode.op ,opcode.feat
                    ,opcode.evex ,opcode.superscripts ,operands.op1)))))",
    )
    .unwrap();
    let mut world = Acl2World::new();
    assert_eq!(
        world.eval_make_event(&forms[0]).unwrap(),
        read_book("(defconst *decoded-fields* '(\"MOV\" 137 (:sse2) () () ()))")
            .unwrap()
            .remove(0)
    );
}

#[test]
fn bstar_unknown_unary_destructuring_remains_rejected() {
    let forms = read_book(
        "(make-event
           (let ((x '(mystery 1)))
             (b* (((mystery x)))
               '(defconst impossible t))))",
    )
    .unwrap();
    let error = Acl2World::new().eval_make_event(&forms[0]).unwrap_err();
    assert!(
        error.to_string().contains("unsupported b* binding arity"),
        "{error}"
    );
}

#[test]
fn catalogue_lookup_matches_acl2_symbol_names_against_pre_map_strings() {
    let forms = read_book(
        "(defconst *pre-one-byte-opcode-map*
             '((inst \"MOV\" (op :op 0) (arg) nil nil)))
         (defconst *pre-two-byte-opcode-map* '())
         (defconst *pre-0f-38-three-byte-opcode-map* '())
         (defconst *pre-0f-3a-three-byte-opcode-map* '())
         (make-event
           (if (find-insts-named '(mov) (all-opcode-maps))
               `(defconst *catalogue-found* ',(symbol-list->names '(mov)))
             (raise \"MOV should be present\")))",
    )
    .unwrap();
    let mut world = Acl2World::new();
    for form in &forms[..4] {
        assert!(world.process_event(form).unwrap());
    }
    assert_eq!(
        world.eval_make_event(&forms[4]).unwrap(),
        read_book("(defconst *catalogue-found* '(\"MOV\"))")
            .unwrap()
            .remove(0)
    );
}

#[test]
fn catalogue_lookup_preserves_mixed_case_escaped_mnemonics() {
    let forms = read_book(
        "(defconst *pre-one-byte-opcode-map*
             '((inst \"JrCXZ\" (op :op 1) (arg) impl nil)
               (inst \"prefetchw(/1)\" (op :op 2) (arg) impl nil)
               (inst \"VBROADCASTI32x2\" (op :op 3) (arg) impl nil)))
         (defconst *pre-two-byte-opcode-map* '())
         (defconst *pre-0f-38-three-byte-opcode-map* '())
         (defconst *pre-0f-3a-three-byte-opcode-map* '())
         (make-event
           (if (not
                (set-difference-equal
                  (symbol-list->names
                    '(|JrCXZ| |prefetchw(/1)| |VBROADCASTI32x2|))
                  (inst-list->mnemonics
                    (find-insts-named
                      '(|JrCXZ| |prefetchw(/1)| |VBROADCASTI32x2|)
                      (all-opcode-maps)))))
               '(defconst *escaped-catalogue-found* t)
             (raise \"escaped mnemonics should be present\")))",
    )
    .unwrap();
    let mut world = Acl2World::new();
    for form in &forms[..4] {
        assert!(world.process_event(form).unwrap());
    }
    assert_eq!(
        world.eval_make_event(&forms[4]).unwrap(),
        read_book("(defconst *escaped-catalogue-found* t)")
            .unwrap()
            .remove(0)
    );
}

#[test]
fn catalogue_feature_expressions_use_authored_opcode_fields() {
    let forms = read_book(
        "(defconst *feature-inst*
             '(inst \"VADDPS\"
                    (op :op 1 :vex '(:0f :256) :feat '(:avx :avx2))
                    (arg) impl nil))
         (make-event
           (if (and (eval-feature-expr '(and :vex :avx2 (not :evex))
                                       *feature-inst*)
                    (eval-feature-expr '(xor :evex :avx)
                                       *feature-inst*)
                    (eval-feature-expr :vex-256 *feature-inst*))
               '(defconst *feature-match* t)
             (raise \"feature expression should match\")))",
    )
    .unwrap();
    let mut world = Acl2World::new();
    assert!(world.process_event(&forms[0]).unwrap());
    assert_eq!(
        world.eval_make_event(&forms[1]).unwrap(),
        read_book("(defconst *feature-match* t)").unwrap().remove(0)
    );
}

#[test]
fn catalogue_promotions_use_prior_sections_and_flat_opcode_materialization() {
    let forms = read_book(
        "(defconst *promoted-inst*
             '(inst \"VADDPS\"
                    (op :op 1 :evex '(:evex) :feat '(:avx512f))
                    (arg) impl nil))
         (defconst *pre-one-byte-opcode-map* (list *promoted-inst*))
         (defconst *pre-two-byte-opcode-map* '())
         (defconst *pre-0f-38-three-byte-opcode-map* '())
         (defconst *pre-0f-3a-three-byte-opcode-map* '())
         (defconst *catalogue-table*
           (list (cons '(5 13)
                       (list :implemented (list *promoted-inst*)
                             :unimplemented nil))))
         (make-event
           (if (and (all-opcode-maps)
                    (sdm-instruction-table-sort *catalogue-table*)
                    (get-promoted-avx512-insts
                       '(5 19 2) :avx512f *catalogue-table*))
               '(defconst *promotion-found* t)
             (raise \"promotion should be found\")))",
    )
    .unwrap();
    let mut world = Acl2World::new();
    for form in &forms[..6] {
        assert!(world.process_event(form).unwrap());
    }
    assert_eq!(
        world.eval_make_event(&forms[6]).unwrap(),
        read_book("(defconst *promotion-found* t)")
            .unwrap()
            .remove(0)
    );
}

#[test]
fn catalogue_table_organization_is_iterative_and_section_ordered() {
    let forms = read_book(
        "(defconst *i1* '(inst \"ONE\" (op :op 1) (arg) impl nil))
         (defconst *i2* '(inst \"TWO\" (op :op 2) (arg) nil nil))
         (defconst *unordered-table*
           (list
             (cons '(5 10) (list :implemented (list *i1*) :unimplemented nil))
             (cons '(5 2) (list :implemented nil :unimplemented (list *i2*)))))
         (make-event
           (b* ((ordered (sdm-instruction-table-organize *unordered-table*))
                (implemented
                  (sdm-instruction-table-implemented-instructions ordered))
                (unimplemented
                  (sdm-instruction-table-unimplemented-instructions ordered)))
             (if (and (equal (len implemented) 1)
                      (equal (len unimplemented) 1)
                      (equal (acl2::nat-list-fix '(5 -1 2)) '(5 0 2)))
                 `(defconst *ordered-table* ',ordered)
               (raise \"table organization failed\"))))",
    )
    .unwrap();
    let mut world = Acl2World::new();
    for form in &forms[..3] {
        assert!(world.process_event(form).unwrap());
    }
    let generated = world.eval_make_event(&forms[3]).unwrap();
    let rendered = format!("{generated:?}");
    assert!(
        rendered.find("Symbol(\"2\")").unwrap_or(usize::MAX)
            < rendered.find("Symbol(\"10\")").unwrap_or(usize::MAX),
        "section 5.2 must precede 5.10: {generated:?}"
    );
}

#[test]
fn make_event_evaluator_handles_x86_state_loop_collect() {
    // Reduced verbatim shape of the read-time event in
    // projects/x86isa/machine/state.lisp.  LOOP$ is used here only as an
    // eager data traversal; evaluating it installs a constant and carries no
    // theorem authority.
    let forms = read_book(
        "(defconst *x86isa-state*
            '((:doc \"heading\")
              (ms :type t)
              (fault :type t)))
         (make-event
           `(defconst *x86-field-names-as-keywords*
              ',(loop$ for i in (strip-cars *x86isa-state*)
                       when (not (equal i :doc))
                       collect
                       (intern$ (symbol-name i) \"KEYWORD\"))))
         (make-event
           `(progn
              ,@(loop$ for events in '(((defthm first t))
                                        ((defthm second t)))
                       append events)))",
    )
    .unwrap();
    let mut world = Acl2World::new();
    assert!(world.process_event(&forms[0]).unwrap());
    assert_eq!(
        world.eval_make_event(&forms[1]).unwrap(),
        read_book("(defconst *x86-field-names-as-keywords* '(:ms :fault))")
            .unwrap()
            .remove(0)
    );
    assert_eq!(
        world.eval_make_event(&forms[2]).unwrap(),
        read_book("(progn (defthm first t) (defthm second t))")
            .unwrap()
            .remove(0)
    );
}

fn session() -> Acl2Session {
    Acl2Session::new().expect("session")
}

/// The honesty boundary, re-checked from outside the pipeline: every event
/// the report claims as *transported* has a stored theorem that is
/// hypothesis-free and proved by a reified certificate (directly or through
/// the generic induction premise builder).
fn check_transported(sess: &Acl2Session, report: &BookReport) {
    for e in &report.events {
        if matches!(
            e.outcome,
            EventOutcome::Transported | EventOutcome::LocalTransported
        ) {
            let entry = sess
                .theorem_entry(&e.label)
                .unwrap_or_else(|| panic!("transported `{}` must be stored", e.label));
            assert!(
                entry.thm.hyps().is_empty(),
                "transported `{}` must be hyps-free, got {:?}",
                e.label,
                entry.thm.hyps()
            );
            match &entry.proof {
                Acl2Proof::Certificate { derivation } | Acl2Proof::Induction { derivation, .. } => {
                    assert!(
                        derivation.hyps().is_empty(),
                        "transported `{}` must have a closed object derivation",
                        e.label
                    )
                }
                Acl2Proof::Reduction => {
                    panic!("transported `{}` cannot ride reduction", e.label)
                }
            }
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

    // The exact tally: both universally quantified staples are transported.
    assert_eq!(
        report.tally(),
        Tally {
            transported: 4,
            local_transported: 0,
            admitted: 6,
            skipped: 1,
            rejected: 0,
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
    for name in ["app-assoc", "len2-app"] {
        assert_eq!(*outcome(&report, name), EventOutcome::Transported);
        let entry = s
            .theorem_entry(name)
            .unwrap_or_else(|| panic!("stored {name}"));
        assert!(entry.thm.hyps().is_empty());
        match &entry.proof {
            Acl2Proof::Induction {
                variable,
                derivation,
            } => {
                assert_eq!(
                    variable.as_deref(),
                    Some(b"X".as_slice()),
                    "{name} induction variable"
                );
                assert!(derivation.hyps().is_empty());
            }
            other => panic!("{name} must use kernel induction, got {other:?}"),
        }
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
    //  transported: three-with-hints, consp-implies
    //               + nested {four, car-app}                           = 4
    //  admitted:    pair-up-a + nested {app, rev, len2, app-ab-c,
    //               rev-rev-ab, len2-abc}                              = 7
    //  skipped:     in-package ×2 (own + nested), include ×4 (satisfied,
    //               re-include, missing, :dir), local defun            = 7
    //  rejected:    bogus, defmacro, encapsulate, mutual-recursion
    //               + nested {app-assoc, len2-app}                     = 6
    assert_eq!(
        report.tally(),
        Tally {
            transported: 4,
            local_transported: 0,
            admitted: 7,
            skipped: 7,
            rejected: 6,
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
            EventOutcome::Skipped { reason } | EventOutcome::UnresolvedDependency { reason } => {
                reason.as_str()
            }
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
    assert_eq!(
        report
            .includes
            .iter()
            .map(|include| include.status)
            .collect::<Vec<_>>(),
        vec![
            IncludeStatus::Replayed,
            IncludeStatus::Idempotent,
            IncludeStatus::Missing,
            IncludeStatus::Unconfigured,
        ]
    );
    assert_eq!(report.includes[0].encounter_ordinal, 0);
    assert_eq!(report.includes[0].requested_by.root, None);
    assert_eq!(report.includes[0].requested_by.path, "books/mixed.lisp");
    assert_eq!(
        report.includes[0]
            .resolved
            .as_ref()
            .map(|identity| identity.path.as_str()),
        Some("books/app-basics.lisp")
    );
    assert_eq!(
        report
            .sources
            .iter()
            .map(|source| (source.role, source.status))
            .collect::<Vec<_>>(),
        vec![
            (SourceRole::Target, SourceStatus::Replayed),
            (SourceRole::Include, SourceStatus::Replayed),
        ]
    );
    for (ordinal, source) in report.sources.iter().enumerate() {
        assert_eq!(source.attempt_ordinal, ordinal);
        assert!(source.sha256.is_some(), "exact-byte digest is retained");
    }

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

    // The generic implication transport now closes this ordinary theorem.
    assert_eq!(
        *outcome(&report, "consp-implies"),
        EventOutcome::Transported
    );
    assert!(
        s.theorem("consp-implies")
            .is_some_and(|theorem| theorem.hyps().is_empty())
    );
    // Honest rejections, with reasons.
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
    for name in ["bogus", "hidden"] {
        assert!(s.theorem(name).is_none(), "`{name}` must not be stored");
    }
}

#[test]
fn empty_encapsulate_inline_defun_and_portcullis_events() {
    let mut s = session();
    let report = run_book(&mut s, &root(), "books/event-compat").expect("book runs");

    assert_eq!(
        report.tally(),
        Tally {
            transported: 0,
            local_transported: 0,
            admitted: 2,
            skipped: 7,
            rejected: 0,
        },
        "tally mismatch:\n{report}"
    );
    assert!(s.defs().contains("inline-id"));
    assert!(s.theorem("inline-id-a").is_some());
    assert!(matches!(
        outcome(&report, "inline-id"),
        EventOutcome::Admitted { .. }
    ));
    let table = report
        .events
        .iter()
        .find(|event| event.kind == "table")
        .expect("table row");
    assert!(matches!(table.outcome, EventOutcome::Skipped { .. }));
}

#[test]
fn safe_function_and_rule_event_aliases() {
    let mut s = session();
    let report = run_book(&mut s, &root(), "books/event-aliases").expect("book runs");

    assert_eq!(
        report.tally(),
        Tally {
            transported: 0,
            local_transported: 0,
            admitted: 11,
            skipped: 2,
            rejected: 1,
        },
        "tally mismatch:\n{report}"
    );
    for name in [
        "plain-id",
        "nx-id",
        "old-id",
        "typed-id",
        "extended-id",
        "post-metadata-id",
    ] {
        assert!(
            s.defs().contains(name),
            "missing normalized definition {name}"
        );
    }
    for name in ["plain-id-a", "nx-id-a", "old-id-a", "extended-id-a"] {
        assert!(
            s.theorem(name).is_some(),
            "missing normalized theorem {name}"
        );
    }
    assert!(matches!(
        outcome(&report, "returns-two"),
        EventOutcome::Rejected { .. }
    ));
    assert!(matches!(
        outcome(&report, "prepwork-id"),
        EventOutcome::Admitted { .. }
    ));
    assert!(
        s.defs().contains("hidden-helper"),
        ":prepwork definition must be processed before the parent definition"
    );
}

#[test]
fn inventory_manifest_is_deterministic_and_does_not_execute_logic() {
    let config = BookConfig::new(root()).inventory_only();
    let mut s = session();
    let report =
        run_book_with_config(&mut s, &config, "books/event-aliases").expect("inventory runs");
    let manifest = report.manifest();

    assert!(s.defs().is_empty());
    assert!(s.theorem("plain-id-a").is_none());
    assert_eq!(manifest.classes[&ImportClass::LogicalDefinition], 9);
    assert_eq!(manifest.classes[&ImportClass::LogicalTheorem], 4);
    assert_eq!(manifest.classes[&ImportClass::ExecutionOrDocs], 1);
    assert_eq!(
        manifest
            .classes
            .get(&ImportClass::UnresolvedLogicalDependency),
        None
    );
    assert_eq!(manifest.rejections.get("define"), None);
    assert!(manifest.unresolved.is_empty());
    assert_eq!(manifest, report.manifest(), "manifest must be stable");
}

#[test]
fn structured_completeness_distinguishes_inventory_from_a_green_island() {
    let mut inventory_session = session();
    let inventory = run_book_with_config(
        &mut inventory_session,
        &BookConfig::new(root()).inventory_only(),
        "books/generic-rules",
    )
    .expect("inventory");
    let inventory_progress = inventory.completeness();
    assert_eq!(
        inventory_progress.level,
        CompletenessLevel::DefinitionsComplete
    );
    assert_eq!(
        inventory_progress.closure.theorems,
        CompletenessCount {
            complete: 0,
            total: 3
        }
    );
    assert!(!inventory_progress.is_green_island());

    let mut proving_session = session();
    let proved = run_book(&mut proving_session, &root(), "books/generic-rules")
        .expect("checked book import");
    let progress = proved.completeness();
    assert_eq!(progress.level, CompletenessLevel::TheoremsComplete);
    assert_eq!(
        progress.closure.theorems,
        CompletenessCount {
            complete: 3,
            total: 3
        }
    );
    assert!(progress.closure.events.is_complete());
    assert!(progress.closure.definitions.is_complete());
    assert_eq!(progress.target.theorems, progress.closure.theorems);
    assert!(progress.is_green_island());
}

#[test]
fn structured_completeness_fails_closed_on_an_unresolved_dependency() {
    let mut s = session();
    let report = run_book(&mut s, &root(), "books/linking").expect("book import");
    let progress = report.completeness();

    assert_eq!(progress.level, CompletenessLevel::Observed);
    assert_eq!(progress.closure.unresolved_dependencies, 2);
    assert!(!progress.closure.events.is_complete());
    assert!(!progress.is_green_island());
    assert_eq!(
        report
            .events
            .iter()
            .filter(|event| matches!(event.outcome, EventOutcome::UnresolvedDependency { .. }))
            .count(),
        2
    );
}

#[test]
fn structured_completeness_keeps_rejected_logic_in_the_denominator() {
    let report = BookReport {
        path: "target.lisp".into(),
        dependency_interfaces: vec![],
        sources: vec![],
        includes: vec![],
        events: vec![
            EventRecord {
                book: "target.lisp".into(),
                kind: "defun".into(),
                label: "bad-fn".into(),
                outcome: EventOutcome::Rejected {
                    reason: "unsupported".into(),
                },
                notes: vec![],
            },
            EventRecord {
                book: "target.lisp".into(),
                kind: "defthm".into(),
                label: "bad-thm".into(),
                outcome: EventOutcome::Rejected {
                    reason: "unproved".into(),
                },
                notes: vec![],
            },
        ],
    };
    let progress = report.completeness();
    assert_eq!(
        progress.target.definitions,
        CompletenessCount {
            complete: 0,
            total: 1
        }
    );
    assert_eq!(
        progress.target.theorems,
        CompletenessCount {
            complete: 0,
            total: 1
        }
    );
    assert!(!progress.is_green_island());
}

#[test]
fn structured_completeness_never_greens_deferred_generated_logic() {
    let report = BookReport {
        path: "target.lisp".into(),
        dependency_interfaces: vec![],
        sources: vec![],
        includes: vec![],
        events: vec![EventRecord {
            book: "target.lisp".into(),
            kind: "fty::bitstruct-obligations".into(),
            label: "flags".into(),
            outcome: EventOutcome::DeferredLogical {
                reason: "generated theorem family awaits replay".into(),
            },
            notes: vec![],
        }],
    };
    let progress = report.completeness();
    assert_eq!(progress.level, CompletenessLevel::Observed);
    assert!(!progress.target.events.is_complete());
    assert!(!progress.is_green_island());
}

#[test]
fn theorem_neutral_include_interface_is_hash_bound_and_logical_only() {
    let dependency = root().join("books/interface-dep.lisp");
    let digest = sha256(&std::fs::read(&dependency).unwrap());
    let interface = TheoremNeutralInterface::new(
        digest,
        TheoremNeutralCapability::TransparentDefsection,
        "fixture target uses only transparent defsection",
    );
    let config = BookConfig::new(root())
        .with_theorem_neutral_interface("books/interface-dep.lisp", interface);
    let mut s = session();
    let report = run_book_with_config(&mut s, &config, "books/interface-target").unwrap();
    let progress = report.completeness();

    assert!(progress.is_logical_green_island(), "{report}");
    assert!(!progress.is_green_island(), "{report}");
    assert_eq!(progress.closure.dependency_interfaces, 1);
    assert_eq!(
        progress.source_closure,
        SourceClosureStatus::Interfaced { verified: 1 }
    );
    assert_eq!(report.dependency_interfaces.len(), 1);
    assert_eq!(report.includes.len(), 1);
    assert_eq!(report.includes[0].status, IncludeStatus::Interface);
    assert_eq!(report.sources.len(), 2);
    assert_eq!(report.sources[1].role, SourceRole::Interface);
    assert_eq!(report.sources[1].status, SourceStatus::Interface);
    assert_eq!(report.sources[1].sha256, Some(digest));
    assert!(matches!(
        report.event("interface-dep").map(|event| &event.outcome),
        Some(EventOutcome::DependencyInterface { .. })
    ));
    assert!(s.theorem("interface-target-theorem").is_some());
}

#[test]
fn theorem_neutral_include_interface_hash_mismatch_fails_closed() {
    let dependency = root().join("books/interface-dep.lisp");
    let interface = TheoremNeutralInterface::new(
        [0; 32],
        TheoremNeutralCapability::TransparentDefsection,
        "deliberately forged fixture digest",
    );
    let config = BookConfig::new(root())
        .with_theorem_neutral_interface("books/interface-dep.lisp", interface);
    let mut s = session();
    let report = run_book_with_config(&mut s, &config, "books/interface-target").unwrap();
    let progress = report.completeness();

    assert!(!progress.is_logical_green_island());
    assert!(!progress.is_green_island());
    assert_eq!(progress.closure.unresolved_dependencies, 1);
    assert!(report.dependency_interfaces.is_empty());
    assert_eq!(report.includes[0].status, IncludeStatus::HashMismatch);
    assert_eq!(report.sources[1].status, SourceStatus::HashMismatch);
    assert_eq!(
        report.sources[1].sha256,
        Some(sha256(&std::fs::read(dependency).unwrap()))
    );
    assert!(matches!(
        report.event("interface-dep").map(|event| &event.outcome),
        Some(EventOutcome::UnresolvedDependency { reason })
            if reason.contains("SHA-256 mismatch")
    ));
}

#[test]
fn conflicting_theorem_neutral_interfaces_are_rejected_before_loading() {
    let first = TheoremNeutralInterface::new(
        [1; 32],
        TheoremNeutralCapability::TransparentDefsection,
        "first",
    );
    let second = TheoremNeutralInterface::new(
        [2; 32],
        TheoremNeutralCapability::TransparentDefsection,
        "second",
    );
    let config = BookConfig::new(root())
        .with_theorem_neutral_interface("books/interface-dep.lisp", first)
        .with_theorem_neutral_interface("books/interface-dep.lisp", second);
    let error = run_book_with_config(&mut session(), &config, "books/interface-target")
        .expect_err("conflicting interface must fail before loading");
    assert!(error.to_string().contains("conflicting theorem-neutral"));
}

#[test]
fn certification_sidecar_establishes_the_initial_book_world() {
    let config = BookConfig::new(root()).inventory_only();
    let mut s = session();
    let report = run_book_with_config(&mut s, &config, "books/cert-prelude")
        .expect("certification prelude and source book load in order");
    assert_eq!(
        report
            .sources
            .iter()
            .map(|source| source.role)
            .collect::<Vec<_>>(),
        vec![SourceRole::Prelude, SourceRole::Target]
    );
    assert!(
        report.includes.is_empty(),
        "the sidecar is not a fake include"
    );

    let prelude = report
        .event("*prelude-base*")
        .expect("sidecar defconst is inventoried");
    assert!(
        prelude.book.ends_with("books/cert-prelude.acl2"),
        "prelude provenance must remain explicit: {prelude:?}"
    );
    assert!(matches!(
        outcome(&report, "*from-certified-world*"),
        EventOutcome::Skipped { .. }
    ));
    assert!(
        report.manifest().unresolved.is_empty(),
        "the source defconst must see the sidecar world: {report}"
    );
}

#[test]
fn local_generated_events_remain_local_in_the_manifest_stream() {
    let mut s = session();
    let report =
        run_book(&mut s, &root(), "books/local-generated").expect("local generated book runs");

    for name in ["local-generated-a", "local-generated-b"] {
        let event = report.event(name).expect("generated theorem row");
        assert!(
            event.kind.starts_with("local "),
            "generated local row lost scope: {event:?}"
        );
        assert_eq!(event.outcome, EventOutcome::LocalTransported);
    }
    let public = report.event("public-after-local").unwrap();
    assert_eq!(public.outcome, EventOutcome::Transported);
    assert!(!public.kind.starts_with("local "));

    let mut progress = covalence_lisp::progress::CorpusProgress::new("fixture");
    progress.record_report(&report);
    let manifest = progress.to_manifest_tsv();
    assert!(manifest.contains("\tlocal\tlocal defthm\tlocal-generated-a\tlocal-transported\t"));
    assert!(manifest.contains("\tpublic\tdefthm\tpublic-after-local\ttransported\t"));
}

#[test]
fn define_type_prescription_is_an_explicit_theorem_obligation() {
    let config = BookConfig::new(root()).inventory_only();
    let mut s = session();
    let report = run_book_with_config(&mut s, &config, "books/define-type-prescription")
        .expect("define with a type-prescription inventories");

    assert!(matches!(
        outcome(&report, "natural-id"),
        EventOutcome::Skipped { .. }
    ));
    let obligation = report
        .event("natural-id-type-prescription")
        .expect("generated type theorem remains visible");
    assert_eq!(obligation.kind, "define :type-prescription");
    assert!(matches!(obligation.outcome, EventOutcome::Skipped { .. }));
    assert!(
        obligation
            .notes
            .iter()
            .any(|note| note.contains("(natp (natural-id x))")),
        "exact generated formula is retained: {obligation:?}"
    );
    assert!(report.manifest().unresolved.is_empty());
}

#[test]
fn theorem_macro_and_proof_world_inventory() {
    let config = BookConfig::new(root()).inventory_only();
    let mut s = session();
    let report =
        run_book_with_config(&mut s, &config, "books/proof-world").expect("inventory runs");
    let manifest = report.manifest();

    assert_eq!(manifest.classes[&ImportClass::LogicalTheorem], 5);
    assert_eq!(manifest.classes[&ImportClass::ProofControl], 3);
    assert_eq!(manifest.classes[&ImportClass::ExecutionOrDocs], 1);
    assert_eq!(
        manifest.classes[&ImportClass::UnresolvedLogicalDependency],
        1
    );
    assert_eq!(manifest.unresolved[0].kind, "defequiv");
    let equivalence = report
        .event("equal-is-an-equivalence")
        .expect("generated event");
    assert!(equivalence.notes.iter().any(|note| {
        note.contains(
            "(and (booleanp (equal x y)) (equal x x) \
             (implies (equal x y) (equal y x))",
        )
    }));
    let congruence = report
        .event("equal-implies-equal-+-1")
        .expect("generated congruence");
    assert!(congruence.notes.iter().any(|note| {
        note.contains("(implies (equal x x-equiv) (equal (+ x y) (+ x-equiv y)))")
    }));
    let theory = report
        .events
        .iter()
        .find(|event| event.kind == "in-theory")
        .expect("theory event");
    assert_eq!(
        theory.notes,
        vec!["form: (in-theory (e/d (foo) (bar baz)))"]
    );
}

#[test]
fn defrefinement_emits_the_exact_implication_obligation() {
    let config = BookConfig::new(root()).inventory_only();
    let mut s = session();
    let report =
        run_book_with_config(&mut s, &config, "books/refinement").expect("refinement inventory");

    assert!(report.manifest().unresolved.is_empty());
    assert_eq!(report.manifest().classes[&ImportClass::LogicalTheorem], 2);
    let default = report
        .event("fine-equiv-refines-coarse-equiv")
        .expect("default refinement theorem");
    assert!(
        default
            .notes
            .iter()
            .any(|note| { note.contains("(implies (fine-equiv x y) (coarse-equiv x y))",) })
    );
    let named = report
        .event("named-refinement")
        .expect("explicitly named refinement theorem");
    assert!(
        named
            .notes
            .iter()
            .any(|note| note.contains("(implies (fine-equiv x y) (other-equiv x y))"))
    );
}

#[test]
fn gl_wrappers_emit_exact_theorem_obligations_without_authority() {
    let config = BookConfig::new(root()).inventory_only();
    let mut s = session();
    let report =
        run_book_with_config(&mut s, &config, "books/gl-theorems").expect("GL wrappers inventory");
    let manifest = report.manifest();

    let theorem = report.event("gl-identity").expect("global GL obligation");
    assert_eq!(theorem.kind, "defthm-using-gl");
    assert!(matches!(theorem.outcome, EventOutcome::Skipped { .. }));
    assert!(
        theorem
            .notes
            .iter()
            .any(|note| note.contains("(implies (natp x) (equal x x))")),
        "exact implication retained: {theorem:?}"
    );
    let local = report
        .event("local-gl-identity")
        .expect("local GL obligation");
    assert_eq!(local.kind, "local def-gl-thm");
    assert_eq!(manifest.classes[&ImportClass::LogicalTheorem], 2);
    assert!(manifest.unresolved.is_empty());
    assert!(s.theorem("gl-identity").is_none());
}

#[test]
fn generated_equivalence_obligations_still_require_proof() {
    let mut s = session();
    let report = run_book(&mut s, &root(), "books/proof-world").expect("book runs");
    for name in ["equal-is-an-equivalence", "equal-implies-equal-+-1"] {
        assert!(
            matches!(outcome(&report, name), EventOutcome::Rejected { .. }),
            "{name} must be proved, never merely accepted"
        );
        assert!(s.theorem(name).is_none());
    }
}

#[test]
fn generic_rule_macros_emit_theorems_and_registry_records() {
    let config = BookConfig::new(root()).inventory_only();
    let mut inventory_session = session();
    let inventory = run_book_with_config(&mut inventory_session, &config, "books/generic-rules")
        .expect("inventory");
    let manifest = inventory.manifest();
    assert_eq!(manifest.classes[&ImportClass::LogicalTheorem], 3);
    assert_eq!(manifest.classes[&ImportClass::ProofControl], 6);
    assert_eq!(manifest.classes[&ImportClass::ExecutionOrDocs], 1);
    assert!(manifest.unresolved.is_empty(), "{manifest}");
    assert_eq!(manifest.kinds.get("generic-rule-table"), Some(&3));

    let mut proving_session = session();
    let proved =
        run_book(&mut proving_session, &root(), "books/generic-rules").expect("normal import");
    for name in ["generic-ground", "listp-ground", "projection-ground"] {
        assert!(
            matches!(outcome(&proved, name), EventOutcome::Transported),
            "{name} theorem obligation must be genuinely proved"
        );
        assert!(proving_session.theorem(name).is_some());
    }
}

#[test]
fn scalar_bitstruct_emits_fixtype_obligations() {
    let config = BookConfig::new(root()).inventory_only();
    let mut s = session();
    let report =
        run_book_with_config(&mut s, &config, "books/scalar-bitstruct").expect("inventory");
    let manifest = report.manifest();

    assert_eq!(manifest.classes[&ImportClass::LogicalDefinition], 11);
    assert_eq!(manifest.classes[&ImportClass::LogicalTheorem], 2);
    assert_eq!(manifest.classes[&ImportClass::ProofControl], 5);
    assert_eq!(manifest.classes[&ImportClass::ExecutionOrDocs], 1);
    assert!(manifest.unresolved.is_empty(), "{manifest}");
    for name in ["8bits-p", "8bits-fix", "8bits-equiv"] {
        assert!(
            report.event(name).is_some(),
            "missing generated definition {name}"
        );
    }
    let equivalence = report
        .event("8bits-equiv-is-an-equivalence")
        .expect("generated equivalence obligation");
    assert!(
        equivalence
            .notes
            .iter()
            .any(|note| note.contains("equivalence-relation-condition"))
    );
    for name in [
        "byte-pair-p",
        "byte-pair-fix",
        "byte-pair-equiv",
        "byte-pair",
        "byte-pair->low",
        "!byte-pair->low",
        "byte-pair->high",
        "!byte-pair->high",
    ] {
        let event = report
            .event(name)
            .unwrap_or_else(|| panic!("missing aggregate definition {name}"));
        assert!(
            event
                .notes
                .iter()
                .any(|note| { note == "generated by full unsigned FTY defbitstruct expansion" })
        );
    }

    let mut proving = session();
    let normal = run_book(&mut proving, &root(), "books/scalar-bitstruct").expect("normal import");
    for name in [
        "8bits-p",
        "8bits-fix",
        "8bits-equiv",
        "8bits-p-of-8bits-fix",
        "8bits-equiv-is-an-equivalence",
    ] {
        assert!(
            matches!(outcome(&normal, name), EventOutcome::Rejected { .. }),
            "{name} must remain a real admission/proof obligation"
        );
    }
}

#[test]
fn fty_container_inventory_retains_public_surface_and_post_events() {
    let config = BookConfig::new(root()).inventory_only();
    let mut s = session();
    let report = run_book_with_config(&mut s, &config, "books/fty-containers").expect("inventory");
    let manifest = report.manifest();

    assert!(manifest.unresolved.is_empty(), "{manifest}");
    for name in [
        "packet-p",
        "packet-fix",
        "packet-equiv",
        "packet",
        "packet->tag",
        "packet->payload",
        "packet-list-p",
        "packet-list-fix",
        "packet-list-equiv",
        "packet-list-count",
        "maybe-packet-p",
        "maybe-packet-fix",
        "maybe-packet-equiv",
        "maybe-packet-some->val",
    ] {
        let event = report
            .event(name)
            .unwrap_or_else(|| panic!("missing FTY public definition {name}"));
        assert!(
            event
                .notes
                .iter()
                .any(|note| note.starts_with("generated by ")),
            "missing macro provenance for {name}"
        );
    }
    assert!(report.event("packet-post-obligation").is_some());
}

#[test]
fn macro_aliases_normalize_logical_calls_without_authority() {
    let mut s = session();
    let report = run_book(&mut s, &root(), "books/macro-aliases").expect("book runs");

    let alias = report
        .events
        .iter()
        .find(|event| event.kind == "add-macro-alias" && event.label == "alias-view")
        .expect("alias row");
    assert!(matches!(alias.outcome, EventOutcome::Skipped { .. }));
    assert!(
        alias
            .notes
            .iter()
            .any(|note| note == "resolved logical target: alias-target")
    );
    assert!(s.theorem("alias-view-ground").is_some());
    assert!(matches!(
        outcome(&report, "missing-view"),
        EventOutcome::Rejected { reason }
            if reason.contains("not an ordered logical function")
    ));
    let cycle = report
        .events
        .iter()
        .find(|event| event.kind == "add-macro-alias" && event.label == "alias-target")
        .expect("cycle row");
    assert!(matches!(
        cycle.outcome,
        EventOutcome::Rejected { ref reason } if reason.contains("cycle")
    ));
    assert_eq!(
        report
            .events
            .iter()
            .filter(|event| event.kind == "add-macro-alias")
            .count(),
        3
    );
}

#[test]
#[ignore = "requires a separately downloaded ACL2 community-books corpus"]
fn official_x86isa_rflags_macro_aliases_resolve() {
    let books = std::env::var_os("ACL2_CORPUS_DIR")
        .map(PathBuf::from)
        .expect("set ACL2_CORPUS_DIR to the ACL2 checkout's books directory");
    let x86 = books.join("projects/x86isa");
    let config = BookConfig::new(&books)
        .with_dir_root("system", &books)
        .with_dir_root("utils", x86.join("utils"))
        .with_dir_root("proof-utils", x86.join("proofs/utilities"))
        .with_dir_root("machine", x86.join("machine"))
        .inventory_only();
    let mut s = session();
    let report = run_book_with_config(&mut s, &config, "projects/x86isa/machine/rflags-spec")
        .expect("rflags book loads");
    let unresolved = report
        .manifest()
        .unresolved
        .into_iter()
        .filter(|item| item.kind == "add-macro-alias")
        .collect::<Vec<_>>();
    assert!(unresolved.is_empty(), "{unresolved:#?}");
    assert_eq!(
        report
            .events
            .iter()
            .filter(|event| {
                event.kind == "add-macro-alias"
                    && matches!(event.outcome, EventOutcome::Skipped { .. })
            })
            .count(),
        4
    );
}

#[test]
fn deffixtype_define_emits_logical_obligations() {
    let config = BookConfig::new(root()).inventory_only();
    let mut s = session();
    let report = run_book_with_config(&mut s, &config, "books/deffixtype").expect("inventory");
    let manifest = report.manifest();

    assert_eq!(manifest.classes[&ImportClass::LogicalDefinition], 1);
    assert_eq!(manifest.classes[&ImportClass::LogicalTheorem], 3);
    assert_eq!(manifest.classes[&ImportClass::ProofControl], 2);
    assert_eq!(manifest.classes[&ImportClass::ExecutionOrDocs], 1);
    assert_eq!(
        manifest.classes[&ImportClass::UnresolvedLogicalDependency],
        1
    );
    for name in [
        "sample-equiv",
        "sample-p-of-sample-fix",
        "sample-fix-when-sample-p",
        "sample-equiv-is-an-equivalence",
    ] {
        assert!(report.event(name).is_some(), "missing obligation {name}");
    }
    assert_eq!(manifest.unresolved[0].label, "existing");

    let mut proving = session();
    let normal = run_book(&mut proving, &root(), "books/deffixtype").expect("normal import");
    for name in [
        "sample-equiv",
        "sample-p-of-sample-fix",
        "sample-fix-when-sample-p",
        "sample-equiv-is-an-equivalence",
    ] {
        assert!(
            matches!(outcome(&normal, name), EventOutcome::Rejected { .. }),
            "{name} must remain a real logical obligation"
        );
    }
}

#[test]
fn documentation_and_execution_wrappers_inventory() {
    let config = BookConfig::new(root()).inventory_only();
    let mut s = session();
    let report =
        run_book_with_config(&mut s, &config, "books/wrapper-world").expect("inventory runs");
    let manifest = report.manifest();

    assert_eq!(manifest.classes[&ImportClass::LogicalDefinition], 1);
    assert_eq!(manifest.classes[&ImportClass::LogicalTheorem], 1);
    assert_eq!(manifest.classes[&ImportClass::ExecutionOrDocs], 6);
    assert_eq!(manifest.classes[&ImportClass::ProofControl], 5);
    assert!(manifest.unresolved.is_empty());
    let wrapper = report
        .events
        .iter()
        .find(|event| event.kind == "with-output")
        .expect("wrapper row");
    assert_eq!(wrapper.notes, vec!["options: :off :all :gag-mode nil"]);
}

#[test]
fn program_and_logic_events_order_subsequent_definition_modes() {
    let config = BookConfig::new(root()).inventory_only();
    let mut s = session();
    let report = run_book_with_config(&mut s, &config, "books/program-mode")
        .expect("ordered mode changes load");
    let manifest = report.manifest();

    assert!(matches!(
        outcome(&report, "host-helper"),
        EventOutcome::Skipped { .. }
    ));
    assert_eq!(report.event("host-helper").unwrap().kind, "program defun");
    assert_eq!(report.event("logical-id").unwrap().kind, "defun");
    assert_eq!(manifest.classes[&ImportClass::ExecutionOrDocs], 2);
    assert_eq!(manifest.classes[&ImportClass::LogicalDefinition], 1);
    assert_eq!(manifest.classes[&ImportClass::ProofControl], 2);
    assert!(manifest.unresolved.is_empty());
}

#[test]
fn included_book_definition_mode_does_not_leak_into_parent() {
    let config = BookConfig::new(root()).inventory_only();
    let mut s = session();
    let report = run_book_with_config(&mut s, &config, "books/program-parent")
        .expect("included mode is scoped");

    assert_eq!(
        report.event("child-host-helper").unwrap().kind,
        "program defun"
    );
    assert_eq!(report.event("after-program-child").unwrap().kind, "defun");
    assert!(report.manifest().unresolved.is_empty());
}

#[test]
fn event_wrappers_preserve_obligations_and_assertions_fail_closed() {
    let mut s = session();
    let report =
        run_book(&mut s, &root(), "books/event-wrappers").expect("event wrapper import runs");

    for theorem in [
        "wrapper-id-exact",
        "local-supporter",
        "exported-with-supporter",
    ] {
        assert!(
            report.event(theorem).is_some(),
            "nested theorem obligation {theorem} must be exposed: {:#?}",
            report.events
        );
    }
    assert_eq!(
        report.event("local-supporter").unwrap().outcome,
        EventOutcome::LocalTransported,
        "a checked local theorem must remain distinguishable from an admitted or skipped event"
    );
    check_transported(&s, &report);
    let more_returns = report
        .events
        .iter()
        .find(|event| event.kind == "std::more-returns")
        .expect("more-returns wrapper row");
    assert!(matches!(more_returns.outcome, EventOutcome::Skipped { .. }));
    let supporters = report
        .events
        .iter()
        .find(|event| event.kind == "acl2::with-supporters")
        .expect("with-supporters wrapper row");
    assert!(matches!(supporters.outcome, EventOutcome::Skipped { .. }));

    let assertions = report
        .events
        .iter()
        .filter(|event| event.kind == "assert-event")
        .collect::<Vec<_>>();
    assert_eq!(assertions.len(), 3);
    assert!(matches!(
        assertions[0].outcome,
        EventOutcome::Skipped { .. }
    ));
    assert!(matches!(
        assertions[1].outcome,
        EventOutcome::Rejected { .. }
    ));
    assert!(matches!(
        assertions[2].outcome,
        EventOutcome::Rejected { .. }
    ));
    assert!(
        assertions[0]
            .notes
            .iter()
            .any(|note| note.contains("not imported as a theorem"))
    );
}

#[test]
fn constants_and_make_event_build_an_ordered_theorem_neutral_world() {
    let mut s = session();
    let report = run_book(&mut s, &root(), "books/world-events").expect("book runs");

    for name in ["*byte-mask*", "*r0*", "*last-register*", "*masks*"] {
        let event = report
            .event(name)
            .unwrap_or_else(|| panic!("missing generated/read-time event {name}"));
        assert!(
            matches!(event.outcome, EventOutcome::Skipped { .. }),
            "{name}: {:?}",
            event.outcome
        );
        assert!(
            event
                .notes
                .iter()
                .any(|note| note.contains("no theorem") || note.contains("generated by")),
            "{name} must retain the honesty/provenance note: {:?}",
            event.notes
        );
    }
    let generated = report.event("*r0*").expect("generated defconsts row");
    assert_eq!(generated.kind, "defconsts");
    assert!(
        generated
            .notes
            .iter()
            .any(|note| note.contains("generated by make-event"))
    );
    let generated_index = report
        .events
        .iter()
        .position(|event| event.label == "*r0*")
        .unwrap();
    let parent_index = report
        .events
        .iter()
        .position(|event| event.kind == "make-event")
        .unwrap();
    assert!(
        generated_index < parent_index,
        "generated event is processed inline before its parent tally row"
    );
    assert!(
        s.theorem("*byte-mask*").is_none(),
        "world evaluation must not mint theorem entries"
    );
    assert!(
        report
            .event("*masks*")
            .unwrap()
            .notes
            .iter()
            .any(|note| note.contains("generated by macro call"))
    );
    assert!(matches!(
        outcome(&report, "*must-not-exist*"),
        EventOutcome::Skipped { .. }
    ));
    assert!(
        report
            .events
            .iter()
            .any(|event| { event.kind == "defconst" && event.label == "*must-not-exist*" })
    );
    let manifest = report.manifest();
    assert_eq!(manifest.classes[&ImportClass::ReadTimeWorld], 10);
}

#[test]
fn configurable_extensions_and_dir_roots_link_recursively() {
    let mut s = session();
    let config = BookConfig::new(root())
        .with_dir_root("system", root().join("system-books"))
        .with_extensions([".lsp", "acl2", "lisp"]);
    let report = run_book_with_config(&mut s, &config, "books/linking").expect("book links");

    assert_eq!(
        report.tally(),
        Tally {
            transported: 4,
            local_transported: 0,
            admitted: 0,
            skipped: 5,
            rejected: 0,
        },
        "tally mismatch:\n{report}"
    );
    check_transported(&s, &report);
    for theorem in [
        "linked-relative",
        "linked-explicit",
        "linked-system-leaf",
        "linked-system-top",
    ] {
        assert_eq!(*outcome(&report, theorem), EventOutcome::Transported);
    }
    assert_eq!(
        report.event("linked-relative").unwrap().book,
        "books/linked/relative.lsp"
    );
    assert_eq!(
        report.event("linked-system-leaf").unwrap().book,
        ":system/arithmetic/leaf.acl2"
    );
    assert_eq!(report.sources.len(), 5);
    assert_eq!(
        report
            .sources
            .iter()
            .map(|source| (
                source.identity.root.as_deref(),
                source.identity.path.as_str()
            ))
            .collect::<Vec<_>>(),
        vec![
            (None, "books/linking.lisp"),
            (None, "books/linked/relative.lsp"),
            (Some("system"), "arithmetic/top.lisp"),
            (Some("system"), "arithmetic/leaf.acl2"),
            (None, "books/linked/explicit.acl2"),
        ]
    );
    for source in &report.sources {
        let source_root = source
            .identity
            .root
            .as_deref()
            .map(|_| root().join("system-books"))
            .unwrap_or_else(root);
        assert_eq!(
            source.sha256,
            Some(sha256(
                &std::fs::read(source_root.join(&source.identity.path)).unwrap()
            ))
        );
    }
    let mut include_ordinals: Vec<_> = report
        .includes
        .iter()
        .map(|include| include.encounter_ordinal)
        .collect();
    include_ordinals.sort_unstable();
    assert_eq!(include_ordinals, (0..5).collect::<Vec<_>>());
    assert!(report.includes.iter().any(|include| {
        include.status == IncludeStatus::Unconfigured && include.root.as_deref() == Some("missing")
    }));

    let missing = report
        .events
        .iter()
        .find(|event| {
            event.kind == "include-book"
                && matches!(
                    &event.outcome,
                    EventOutcome::UnresolvedDependency { reason } if reason.contains(":missing")
                )
        })
        .expect("unconfigured :dir is recorded");
    assert_eq!(missing.label, "arithmetic/top");

    let explicit = report
        .events
        .iter()
        .find(|event| event.label == "linked/explicit.acl2")
        .expect("explicit include");
    assert_eq!(explicit.notes, vec![":uncertified-okp ignored"]);

    let manifest = report.manifest();
    let unresolved_includes: Vec<_> = manifest
        .unresolved
        .iter()
        .filter(|item| item.kind == "include-book")
        .map(|item| item.label.as_str())
        .collect();
    assert_eq!(
        unresolved_includes,
        vec!["arithmetic/top"],
        "missing includes are unresolved, while linked/already-linked includes are not"
    );
}

#[test]
fn include_cycle_has_unique_preorder_edges_and_idempotent_back_edge() {
    let mut s = session();
    let config = BookConfig::new(root()).inventory_only();
    let report = run_book_with_config(&mut s, &config, "books/include-cycle-a")
        .expect("include cycle terminates");

    assert_eq!(report.sources.len(), 2);
    assert_eq!(
        report
            .sources
            .iter()
            .map(|source| source.identity.path.as_str())
            .collect::<Vec<_>>(),
        vec!["books/include-cycle-a.lisp", "books/include-cycle-b.lisp"]
    );
    let mut by_encounter: Vec<_> = report.includes.iter().collect();
    by_encounter.sort_by_key(|include| include.encounter_ordinal);
    assert_eq!(by_encounter.len(), 2);
    assert_eq!(by_encounter[0].encounter_ordinal, 0);
    assert_eq!(by_encounter[0].status, IncludeStatus::Replayed);
    assert_eq!(by_encounter[1].encounter_ordinal, 1);
    assert_eq!(by_encounter[1].status, IncludeStatus::Idempotent);
    assert_eq!(
        by_encounter[1].resolved.as_ref(),
        Some(&report.sources[0].identity)
    );
}

#[test]
fn dir_roots_are_independent_confinement_boundaries() {
    let mut s = session();
    let config = BookConfig::new(root()).with_dir_root(":system", root().join("system-books"));
    let report =
        run_book_with_config(&mut s, &config, "books/system-escape").expect("event is tallied");
    assert_eq!(report.tally().rejected, 1);
    let reason = rejected_reason(&report, "../books/app-basics");
    assert!(reason.contains(".."), "got: {reason}");
    assert!(s.defs().is_empty(), "escaping dependency was not processed");
}

#[test]
fn relative_parent_include_may_cross_project_root_inside_system_root() {
    let mut s = session();
    let system = root().join("system-books");
    let config = BookConfig::new(root())
        .with_dir_root(":system", &system)
        .with_dir_root(":project", system.join("project"));
    let report = run_book_with_config(&mut s, &config, "books/system-sibling-link")
        .expect("project-relative include links through the containing system root");

    assert_eq!(
        report.tally(),
        Tally {
            transported: 2,
            local_transported: 0,
            admitted: 0,
            skipped: 2,
            rejected: 0,
        },
        "tally mismatch:\n{report}"
    );
    assert_eq!(
        report.event("linked-system-sibling").unwrap().book,
        ":system/shared/leaf.lisp"
    );
    assert_eq!(
        report.event("linked-project-child").unwrap().book,
        ":project/nested/child.lisp"
    );
    check_transported(&s, &report);
}

#[test]
fn explicit_dir_is_root_relative_even_when_already_inside_that_dir() {
    let mut s = session();
    let system = root().join("system-books");
    let config = BookConfig::new(root()).with_dir_root(":system", &system);
    let report = run_book_with_config(&mut s, &config, "books/nested-explicit-system")
        .expect("nested explicit :system include remains root-relative");

    assert_eq!(report.tally().rejected, 0, "{report}");
    assert_eq!(
        *outcome(&report, "linked-system-sibling"),
        EventOutcome::Transported
    );
    assert!(
        report.manifest().unresolved.is_empty(),
        "all explicit system dependencies resolved:\n{report}"
    );
}

#[test]
fn common_book_containers_and_disabled_aliases_are_transparent() {
    let mut s = session();
    let report = run_book(&mut s, &root(), "books/containers").expect("book runs");
    assert_eq!(
        report.tally(),
        Tally {
            transported: 1,
            local_transported: 0,
            admitted: 2,
            skipped: 2,
            rejected: 0,
        },
        "tally mismatch:\n{report}"
    );
    assert!(s.defs().contains("section-id"));
    assert_eq!(report.event("section-id").unwrap().kind, "defund");
    assert_eq!(report.event("section-ground").unwrap().kind, "defthmd");
    assert_eq!(*outcome(&report, "progn-ground"), EventOutcome::Transported);
    let section = report.event("linked-section").expect("section wrapper");
    assert_eq!(
        section.notes,
        vec!["documentation ignored", ":parents ignored"]
    );
}

/// End-to-end compatibility gate against an independently downloaded checkout
/// of the official ACL2 community books. The checkout is intentionally not a
/// repository dependency; set `ACL2_CORPUS_DIR` to its `books/` directory.
#[test]
#[ignore = "requires a separately downloaded ACL2 community-books corpus"]
fn official_std_lists_append_imports_with_system_linking() {
    let books = std::env::var_os("ACL2_CORPUS_DIR")
        .map(PathBuf::from)
        .expect("set ACL2_CORPUS_DIR to the ACL2 checkout's books directory");
    let config = BookConfig::new(&books).with_dir_root("system", &books);
    let mut s = session();
    let report = run_book_with_config(&mut s, &config, "std/lists/append")
        .expect("official std/lists/append book parses and links");

    assert!(
        report.events.len() >= 50,
        "expected a sizeable linked import, got:\n{report}"
    );
    assert!(
        report
            .events
            .iter()
            .any(|event| event.book.starts_with(":system/")),
        "expected at least one :dir :system dependency:\n{report}"
    );
}

/// Pinned target-local APPEND frontier. This deliberately does not gate the
/// recursive `list-fix`/`abstract`/XDOC closure: it measures the first payoff
/// from checked built-in APPEND without calling the whole book a green island.
#[test]
#[ignore = "requires ACL2 community-books revision 2dbf2b63"]
fn official_std_lists_append_transports_builtin_append_frontier() {
    let books = std::env::var_os("ACL2_CORPUS_DIR")
        .map(PathBuf::from)
        .expect("set ACL2_CORPUS_DIR to the ACL2 checkout's books directory");
    assert_eq!(
        sha256(&std::fs::read(books.join("std/lists/append.lisp")).unwrap()),
        sha256_bytes("240dde02cc141e1d55e3dd6845d1995777a3d6b782e0cf9d6f24abfdcef377da"),
        "pinned std/lists/append target changed"
    );
    let mut s = session();
    let report = run_book_with_config(
        &mut s,
        &BookConfig::new(&books).with_dir_root("system", &books),
        "std/lists/append",
    )
    .expect("official std/lists/append book parses and links");

    let target_sequence: Vec<_> = report
        .events
        .iter()
        .filter(|event| event.book == report.path)
        .map(|event| (event.kind.as_str(), event.label.as_str()))
        .collect();
    assert_eq!(
        target_sequence,
        [
            ("in-package", "\"ACL2\""),
            ("include-book", "list-fix"),
            ("local include-book", "std/basic/inductions"),
            ("local defthm", "len-when-consp"),
            ("defthm", "append-when-not-consp"),
            ("defthm", "append-of-cons"),
            ("defthm", "true-listp-of-append"),
            ("defthm", "consp-of-append"),
            ("defthm", "append-under-iff"),
            ("defthm", "len-of-append"),
            ("defthm", "equal-when-append-same"),
            ("local defthm", "append-nonempty-list"),
            ("defthm", "equal-of-append-and-append-same-arg2"),
            ("defthm", "append-of-nil"),
            ("in-theory", "?"),
            ("defthm", "list-fix-of-append"),
            ("defthm", "car-of-append"),
            ("defthmd", "car-of-append-when-consp"),
            ("theory-invariant", "?"),
            ("defthmd", "cdr-of-append"),
            ("defthm", "cdr-of-append-when-consp"),
            ("theory-invariant", "?"),
            ("defthm", "associativity-of-append"),
            (
                "defcong",
                "element-list-equiv-implies-element-list-equiv-append-1",
            ),
            ("table", "listfix-rules"),
            (
                "defcong",
                "element-list-equiv-implies-element-list-equiv-append-2",
            ),
            ("table", "listfix-rules"),
            ("defthm", "."),
            ("table", "listp-rules"),
            ("progn", "progn"),
            ("def-generic-rule", "(def-generic-rule listp-rules . …)"),
            (
                "def-listp-rule",
                "(def-listp-rule element-list-p-of-append-true-list (equal (element-list-p (append a b)) (and (element-list-p (list-fix a)) (element-list-p b))) …)",
            ),
            ("defsection", "std/lists/append"),
        ],
        "pinned target normalization changed"
    );

    for label in [
        "append-when-not-consp",
        "append-of-cons",
        "consp-of-append",
        "equal-when-append-same",
        "append-nonempty-list",
        "car-of-append",
        "car-of-append-when-consp",
        "cdr-of-append",
        "cdr-of-append-when-consp",
        "associativity-of-append",
    ] {
        let event = report
            .events
            .iter()
            .find(|event| event.book == report.path && event.label == label)
            .unwrap_or_else(|| panic!("missing pinned target event `{label}`"));
        let expected = if label == "append-nonempty-list" {
            EventOutcome::LocalTransported
        } else {
            EventOutcome::Transported
        };
        assert!(
            event.outcome == expected,
            "`{label}` did not cross the checked APPEND frontier:\n{event:?}"
        );
    }
    let target_theorems = report.completeness().target.theorems;
    assert_eq!(target_theorems.total, 18);
    assert!(
        target_theorems.complete >= 9,
        "at least nine public theorems belong to the APPEND-only frontier"
    );
}

/// First checked upstream logical-export gate.  The target exports are kept
/// separate from the recursively included XDOC source closure: this test
/// requires all four official fixer theorems to become closed NativeHol
/// theorems, while the structured report continues to expose XDOC blockers.
#[test]
#[ignore = "requires ACL2 community-books revision 2dbf2b63"]
fn official_std_basic_fixers_transport_all_logical_exports() {
    let books = std::env::var_os("ACL2_CORPUS_DIR")
        .map(PathBuf::from)
        .expect("set ACL2_CORPUS_DIR to the ACL2 checkout's books directory");
    let constructors_sha =
        sha256_bytes("c58a403e94ab4c86c0dfa0da2477b29189cfc49bb3b1a0ca2a6949a89a38b793");
    assert_eq!(
        sha256(&std::fs::read(books.join("xdoc/constructors.lisp")).unwrap()),
        constructors_sha,
        "pinned XDOC interface source changed"
    );
    let config = BookConfig::new(&books)
        .with_dir_root("system", &books)
        .with_dir_theorem_neutral_interface(
            "system",
            "xdoc/constructors.lisp",
            TheoremNeutralInterface::new(
                constructors_sha,
                TheoremNeutralCapability::TransparentDefsection,
                "target uses only built-in transparent defsection event semantics",
            ),
        );

    for (book, source_sha, theorem_names) in [
        (
            "std/basic/nfix",
            "79e853d1e85aa8539a57b50a50586bca53d094c73f40cfae3450d11427524310",
            ["nfix-when-natp", "natp-of-nfix"],
        ),
        (
            "std/basic/ifix",
            "f9614f59dfd1857b45f1d5739bd81df56f5bd0f1b2ce03937379daed2a69fb49",
            ["ifix-when-integerp", "integerp-of-ifix"],
        ),
    ] {
        assert_eq!(
            sha256(&std::fs::read(books.join(format!("{book}.lisp"))).unwrap()),
            sha256_bytes(source_sha),
            "pinned target source changed"
        );
        let mut s = session();
        let report =
            run_book_with_config(&mut s, &config, book).expect("official fixer book imports");
        let progress = report.completeness();

        assert_eq!(
            progress.target.theorems,
            CompletenessCount {
                complete: 2,
                total: 2
            },
            "target export gate failed:\n{report}"
        );
        for name in theorem_names {
            assert_eq!(
                report.event(name).map(|event| &event.outcome),
                Some(&EventOutcome::Transported),
                "`{name}` was not transported:\n{report}"
            );
            let theorem = s
                .theorem(name)
                .unwrap_or_else(|| panic!("missing stored theorem `{name}`"));
            assert!(
                theorem.hyps().is_empty(),
                "`{name}` must be a closed NativeHol theorem"
            );
        }

        assert!(
            progress.is_logical_green_island(),
            "content-verified logical boundary must be green:\n{report}"
        );
        assert_eq!(progress.closure.dependency_interfaces, 1);
        assert_eq!(
            progress.source_closure,
            SourceClosureStatus::Interfaced { verified: 1 }
        );
        assert_eq!(report.dependency_interfaces.len(), 1);
        assert_eq!(
            report.dependency_interfaces[0].capability,
            TheoremNeutralCapability::TransparentDefsection
        );
        assert!(
            !progress.is_green_island(),
            "the recursive XDOC source closure is not complete yet"
        );
    }
}

/// First strict upstream source-green candidate: this official book has no
/// includes, so success requires all five exported theorems and every source
/// event without any dependency interface.
#[test]
#[ignore = "requires ACL2 community-books revision 2dbf2b63"]
fn official_std_lists_acl2_count_is_source_green() {
    const REVISION: &str = "2dbf2b63bb9a27070c8573d72c16c04a4809c8d1";
    const BOOK: &str = "std/lists/acl2-count.lisp";
    let books = std::env::var_os("ACL2_CORPUS_DIR")
        .map(PathBuf::from)
        .expect("set ACL2_CORPUS_DIR to the ACL2 checkout's books directory");
    let source = books.join(BOOK);
    let source_sha = sha256(&std::fs::read(&source).unwrap());
    let pinned_sha =
        sha256_bytes("952499bebe748a4411377644ea6b47208a38f496fd908812099e49af35df8ab1");
    assert_eq!(source_sha, pinned_sha, "pinned ACL2-COUNT book changed");
    let mut s = session();
    let report = run_book_with_config(
        &mut s,
        &BookConfig::new(&books).with_dir_root("system", &books),
        "std/lists/acl2-count",
    )
    .expect("official ACL2-COUNT book imports");
    let progress = report.completeness();

    assert_eq!(
        progress.target.theorems,
        CompletenessCount {
            complete: 5,
            total: 5
        },
        "five-theorem source-green gate failed:\n{report}"
    );
    assert_eq!(progress.source_closure, SourceClosureStatus::Recursive);
    assert!(progress.is_green_island(), "{report}");

    // This exact source contains no macros or generated events, so its six
    // top-level forms are also the independently inspected normalized ACL2
    // denominator. Observed source-green status alone is not enough: require
    // exact revision, bytes, ordering, heads, labels, and public scope.
    let event = |kind: &str, label: &str| NormalizedEventIdentity {
        book: BOOK.into(),
        kind: kind.into(),
        label: label.into(),
        scope: NormalizedEventScope::Public,
    };
    let denominator = PinnedNormalizedDenominator::new(
        REVISION,
        BOOK,
        pinned_sha,
        vec![
            event("in-package", "\"ACL2\""),
            event("defthmd", "acl2-count-of-car"),
            event("defthmd", "acl2-count-of-cdr"),
            event("defthm", "acl2-count-of-sum"),
            event("defthm", "acl2-count-of-consp-positive"),
            event("defthm", "acl2-count-of-cons-greater"),
        ],
    );
    let upstream = denominator
        .compare(&report, REVISION, source_sha, ProgressMode::Replay)
        .expect("ACL2-COUNT must match its authoritative normalized denominator");
    assert!(upstream.is_upstream_complete());

    for name in [
        "acl2-count-of-car",
        "acl2-count-of-cdr",
        "acl2-count-of-sum",
        "acl2-count-of-consp-positive",
        "acl2-count-of-cons-greater",
    ] {
        let theorem = s
            .theorem(name)
            .unwrap_or_else(|| panic!("missing stored theorem `{name}`"));
        assert!(theorem.hyps().is_empty(), "`{name}` must be closed");
    }
}

#[test]
#[ignore = "requires a separately downloaded ACL2 community-books corpus"]
fn official_x86isa_portcullis_builds_ordered_constant_world() {
    let books = std::env::var_os("ACL2_CORPUS_DIR")
        .map(PathBuf::from)
        .expect("set ACL2_CORPUS_DIR to the ACL2 checkout's books directory");
    let x86 = books.join("projects/x86isa");
    let config = BookConfig::new(&books)
        .with_dir_root("system", &books)
        .with_dir_root("utils", x86.join("utils"))
        .with_dir_root("proof-utils", x86.join("proofs/utilities"))
        .with_dir_root("machine", x86.join("machine"))
        .inventory_only();
    let mut s = session();
    let report = run_book_with_config(
        &mut s,
        &config,
        "projects/x86isa/portcullis/sharp-dot-constants",
    )
    .expect("x86isa portcullis constants load");

    let world_events: Vec<_> = report
        .events
        .iter()
        .filter(|event| {
            event.book.contains("projects/x86isa/portcullis/")
                && matches!(event.kind.as_str(), "defconst" | "defconsts" | "make-event")
        })
        .collect();
    assert!(
        world_events.len() >= 360,
        "expected the sizeable generated constant world, got {} rows",
        world_events.len()
    );
    let failed_world_events: Vec<_> = world_events
        .iter()
        .filter(|event| matches!(event.outcome, EventOutcome::Rejected { .. }))
        .collect();
    assert!(
        failed_world_events.is_empty(),
        "read-time world failures: {failed_world_events:#?}"
    );
    assert!(
        world_events.iter().any(|event| {
            event.kind == "defconsts"
                && event
                    .notes
                    .iter()
                    .any(|note| note.contains("generated by make-event"))
        }),
        "expected generated register defconsts with make-event provenance"
    );
    let manifest = report.manifest();
    assert!(
        manifest.unresolved.len() <= 60,
        "ordered world support should keep the portcullis closure near the measured \
         56 unresolved rows, down by at least the 361 authored defconst/make-event rows"
    );
    eprintln!(
        "x86 portcullis manifest: world={}, total={}, unresolved={}",
        manifest
            .classes
            .get(&ImportClass::ReadTimeWorld)
            .copied()
            .unwrap_or(0),
        report.events.len(),
        manifest.unresolved.len()
    );
}

#[test]
#[ignore = "requires a separately downloaded ACL2 community-books corpus"]
fn official_x86isa_utils_installs_template_macros_with_honest_rejections() {
    let books = std::env::var_os("ACL2_CORPUS_DIR")
        .map(PathBuf::from)
        .expect("set ACL2_CORPUS_DIR to the ACL2 checkout's books directory");
    let x86 = books.join("projects/x86isa");
    let config = BookConfig::new(&books)
        .with_dir_root("system", &books)
        .with_dir_root("utils", x86.join("utils"))
        .with_dir_root("proof-utils", x86.join("proofs/utilities"))
        .with_dir_root("machine", x86.join("machine"))
        .inventory_only();
    let mut s = session();
    let report = run_book_with_config(&mut s, &config, "projects/x86isa/utils/utilities")
        .expect("x86isa utilities load");

    for name in [
        "mk-name",
        "forced-and",
        "globally-disable",
        "show-globally-disabled-events-ruleset",
        "show-globally-disabled-events-status",
    ] {
        assert!(
            matches!(outcome(&report, name), EventOutcome::Skipped { .. }),
            "template macro {name} should install: {:?}",
            outcome(&report, name)
        );
    }
    for name in ["defuns-np", "n-size", "ntoi"] {
        assert!(
            matches!(outcome(&report, name), EventOutcome::Rejected { .. }),
            "computational macro {name} must remain explicit: {:?}",
            outcome(&report, name)
        );
    }
    let manifest = report.manifest();
    assert!(
        manifest.unresolved.len() <= 160,
        "template macros should keep the measured utils closure at 156 unresolved rows"
    );
    eprintln!(
        "x86 utils macro manifest: total={}, macro-definitions={}, unresolved={}",
        report.events.len(),
        manifest.kinds.get("defmacro").copied().unwrap_or(0),
        manifest.unresolved.len()
    );
}

#[test]
#[ignore = "requires a separately downloaded ACL2 community-books corpus"]
fn official_x86isa_scalar_def_inst_expands_with_provenance() {
    let books = std::env::var_os("ACL2_CORPUS_DIR")
        .map(PathBuf::from)
        .expect("set ACL2_CORPUS_DIR to the ACL2 checkout's books directory");
    let x86 = books.join("projects/x86isa");
    let config = BookConfig::new(&books)
        .with_dir_root("system", &books)
        .with_dir_root("utils", x86.join("utils"))
        .with_dir_root("proof-utils", x86.join("proofs/utilities"))
        .with_dir_root("machine", x86.join("machine"))
        .inventory_only();
    let mut s = session();
    let report = run_book_with_config(
        &mut s,
        &config,
        "projects/x86isa/machine/instructions/cache",
    )
    .expect("scalar instruction book loads");

    let generated = report
        .events
        .iter()
        .find(|event| {
            event.kind == "define"
                && event.label == "x86-invlpg"
                && event
                    .notes
                    .iter()
                    .any(|note| note.contains("generated by macro call"))
        })
        .unwrap_or_else(|| {
            panic!(
                "def-inst must emit the x86-invlpg define with provenance: {:#?}",
                report
                    .events
                    .iter()
                    .filter(|event| {
                        event.kind == "def-inst"
                            || event.label == "x86-invlpg"
                            || event.kind == "defmacro"
                    })
                    .collect::<Vec<_>>()
            )
        });
    assert!(
        matches!(generated.outcome, EventOutcome::Skipped { .. }),
        "the exact generated std::define should normalize in inventory mode: {generated:#?}"
    );
    let parent = report
        .events
        .iter()
        .find(|event| event.kind == "def-inst")
        .expect("def-inst call row");
    assert!(matches!(parent.outcome, EventOutcome::Skipped { .. }));
    let manifest = report.manifest();
    assert!(
        !manifest
            .unresolved
            .iter()
            .any(|item| item.kind == "define" && item.label == "x86-invlpg"),
        "generated scalar instruction define must leave the unresolved set"
    );
    assert!(
        !manifest
            .unresolved
            .iter()
            .any(|item| item.kind == "defmacro" && item.label == "def-generic-rule"),
        "the real supplied-p/guarded-key macro must install"
    );
    let generic_generated = report
        .events
        .iter()
        .filter(|event| {
            event
                .notes
                .iter()
                .any(|note| note.contains("generated by macro call def-generic-rule"))
        })
        .count();
    eprintln!(
        "x86 scalar def-inst manifest: total={}, def-inst={}, def-generic-rule-generated={}, unresolved={}",
        report.events.len(),
        manifest.kinds.get("def-inst").copied().unwrap_or(0),
        generic_generated,
        manifest.unresolved.len()
    );
    for item in manifest.unresolved.iter().take(8) {
        eprintln!(
            "  unresolved: {} ({} {}) — {}",
            item.book, item.kind, item.label, item.reason
        );
    }
    for item in manifest
        .unresolved
        .iter()
        .filter(|item| item.kind == "defmacro")
    {
        eprintln!(
            "  unresolved macro: {} ({}) — {}",
            item.book, item.label, item.reason
        );
    }
}

/// North-star smoke gate for the official x86isa development. This currently
/// asserts scalable loading/link traversal and honest classification, not
/// successful certification of every event.
#[test]
#[ignore = "requires a separately downloaded ACL2 community-books corpus"]
fn official_x86isa_top_loads_and_links_sizeably() {
    let books = std::env::var_os("ACL2_CORPUS_DIR")
        .map(PathBuf::from)
        .expect("set ACL2_CORPUS_DIR to the ACL2 checkout's books directory");
    let x86 = books.join("projects/x86isa");
    let config = BookConfig::new(&books)
        .with_dir_root("system", &books)
        .with_dir_root("utils", x86.join("utils"))
        .with_dir_root("proof-utils", x86.join("proofs/utilities"))
        .with_dir_root("machine", x86.join("machine"))
        .inventory_only();
    let mut s = session();
    eprintln!("x86 manifest: loading certification prelude and top book");
    let report = run_book_with_config(&mut s, &config, "projects/x86isa/top")
        .expect("official x86isa/top book loads and traverses its include graph");
    eprintln!("x86 manifest: load complete, classifying events");

    assert!(
        report.events.len() >= 1_000,
        "expected a sizeable x86isa import, got {} events",
        report.events.len()
    );
    assert!(
        report
            .events
            .iter()
            .any(|event| event.book.contains("projects/x86isa/machine/")),
        "expected linked machine books in the report"
    );
    let manifest = report.manifest();
    assert!(
        manifest
            .classes
            .get(&ImportClass::LogicalDefinition)
            .copied()
            .unwrap_or(0)
            > 0,
        "expected inventoried x86 logical definitions"
    );
    eprintln!(
        "x86 manifest: classes={:?}, kinds={}, rejection-kinds={:?}, unresolved={}",
        manifest.classes,
        manifest.kinds.len(),
        manifest.rejections,
        manifest.unresolved.len()
    );
    let mut make_event_reasons =
        std::collections::BTreeMap::<String, (usize, String, String)>::new();
    for item in manifest
        .unresolved
        .iter()
        .filter(|item| item.kind == "make-event")
    {
        let entry = make_event_reasons
            .entry(item.reason.clone())
            .or_insert_with(|| (0, item.book.clone(), item.label.clone()));
        entry.0 += 1;
    }
    let mut make_event_reasons = make_event_reasons.into_iter().collect::<Vec<_>>();
    make_event_reasons.sort_by_key(|(_, (count, _, _))| std::cmp::Reverse(*count));
    for (reason, (count, book, label)) in make_event_reasons.iter().take(20) {
        eprintln!("  unresolved make-event x{count}: {reason}; e.g. {book} {label}");
    }
    let mut unresolved_kinds =
        std::collections::BTreeMap::<String, (usize, String, String, String)>::new();
    for item in &manifest.unresolved {
        let entry = unresolved_kinds
            .entry(item.kind.clone())
            .or_insert_with(|| {
                (
                    0,
                    item.book.clone(),
                    item.label.clone(),
                    item.reason.clone(),
                )
            });
        entry.0 += 1;
    }
    let mut unresolved_kinds = unresolved_kinds.into_iter().collect::<Vec<_>>();
    unresolved_kinds.sort_by_key(|(_, (count, _, _, _))| std::cmp::Reverse(*count));
    for (kind, (count, book, label, reason)) in unresolved_kinds.iter().take(20) {
        eprintln!("  unresolved kind {kind} x{count}: {reason}; e.g. {book} {label}");
    }
    for item in manifest.unresolved.iter().filter(|item| {
        item.label.contains("*x86isa-state*")
            || item.label.contains("*x86-field-names-as-keywords*")
    }) {
        eprintln!(
            "  unresolved x86 state world: {} {} {}",
            item.kind, item.label, item.reason
        );
    }
    let unresolved_catalogue = manifest
        .unresolved
        .iter()
        .filter(|item| {
            item.kind == "make-event"
                && item.book.ends_with("machine/catalogue-data.lisp")
                && item.label.contains("def-sdm-instruction-section-fn")
        })
        .count();
    eprintln!("  unresolved catalogue calls={unresolved_catalogue}");
    let mut define_reasons = std::collections::BTreeMap::<String, (usize, String, String)>::new();
    for item in manifest
        .unresolved
        .iter()
        .filter(|item| item.kind == "define")
    {
        let entry = define_reasons
            .entry(item.reason.clone())
            .or_insert_with(|| (0, item.book.clone(), item.label.clone()));
        entry.0 += 1;
    }
    let mut define_reasons = define_reasons.into_iter().collect::<Vec<_>>();
    define_reasons.sort_by_key(|(_, (count, _, _))| std::cmp::Reverse(*count));
    for (reason, (count, book, label)) in define_reasons.iter().take(12) {
        eprintln!("  unresolved define x{count}: {reason}; e.g. {book} {label}");
    }
    let mut bitstruct_reasons =
        std::collections::BTreeMap::<String, (usize, String, String)>::new();
    for item in manifest
        .unresolved
        .iter()
        .filter(|item| item.kind == "defbitstruct")
    {
        let entry = bitstruct_reasons.entry(item.reason.clone()).or_insert((
            0,
            item.book.clone(),
            item.label.clone(),
        ));
        entry.0 += 1;
    }
    for (reason, (count, book, label)) in bitstruct_reasons {
        eprintln!("  unresolved defbitstruct x{count}: {reason}; e.g. {book} {label}");
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
