//! End-to-end tests demonstrating that `covalence-metamath` is **theory
//! agnostic**: the same substitution/DV/RPN machinery checks proofs in several
//! unrelated hand-encoded theories, and rejects ill-formed proofs.

use covalence_metamath::{MmError, parse, verify_all, verify_assertion};

// ===========================================================================
// Theory 1 — "demo0": the Metamath book's introductory theory.
// A mix of a term/equality arithmetic and a propositional `->` connective,
// proving `|- t = t`.
// ===========================================================================

const DEMO0: &str = "\
    $c 0 + = -> ( ) term wff |- $.
    $v t r s P Q $.
    tt $f term t $.
    tr $f term r $.
    ts $f term s $.
    wp $f wff P $.
    wq $f wff Q $.
    tze $a term 0 $.
    tpl $a term ( t + r ) $.
    weq $a wff t = r $.
    wim $a wff ( P -> Q ) $.
    a1 $a |- ( t = r -> ( t = s -> r = s ) ) $.
    a2 $a |- ( t + 0 ) = t $.
    ${
      min $e |- P $.
      maj $e |- ( P -> Q ) $.
      mp $a |- Q $.
    $}
    th1 $p |- t = t $= tt tze tpl tt weq tt tt weq tt a2 tt tze tpl
        tt weq tt tze tpl tt weq tt tt weq wim tt a2 tt tze tpl
        tt tt a1 mp mp $.
";

#[test]
fn demo0_verifies() {
    let db = parse(DEMO0).unwrap();
    assert_eq!(verify_all(&db).unwrap(), 1);
}

#[test]
fn demo0_second_theorem_reuses_first() {
    // th2 : |- 0 = 0, by applying th1 with t := 0.
    let src = format!("{DEMO0}\n th2 $p |- 0 = 0 $= tze th1 $.\n");
    let db = parse(&src).unwrap();
    assert_eq!(verify_all(&db).unwrap(), 2);
}

#[test]
fn demo0_bad_proof_rejected_truncated() {
    // Truncate th1's proof: the stack will not reduce to the claimed statement.
    let bad = DEMO0.replace(
        "$= tt tze tpl tt weq tt tt weq tt a2 tt tze tpl\n        \
         tt weq tt tze tpl tt weq tt tt weq wim tt a2 tt tze tpl\n        \
         tt tt a1 mp mp $.",
        "$= tt tze tpl tt weq $.",
    );
    let db = parse(&bad).unwrap();
    let err = verify_all(&db).unwrap_err();
    assert!(
        matches!(err, MmError::StackResidue { .. } | MmError::ResultMismatch { .. }),
        "expected residue/mismatch, got {err}"
    );
}

#[test]
fn demo0_unknown_label_rejected() {
    let bad = DEMO0.replace("tt tt a1 mp mp $.", "tt tt a1 mp bogus mp $.");
    let db = parse(&bad).unwrap();
    assert!(matches!(
        verify_all(&db).unwrap_err(),
        MmError::UnknownLabel { .. }
    ));
}

// ===========================================================================
// Theory 2 — propositional calculus (set.mm's ax-1 / ax-2 / ax-mp).
// A completely different signature from demo0; proves `a1i` (a derived rule
// with an essential hypothesis).
// ===========================================================================

const PROP: &str = "\
    $c ( ) -> wff |- $.
    $v ph ps ch $.
    wph $f wff ph $.
    wps $f wff ps $.
    wch $f wff ch $.
    wi $a wff ( ph -> ps ) $.
    ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
    ax-2 $a |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $.
    ${
      mp.maj $e |- ph $.
      mp.min $e |- ( ph -> ps ) $.
      ax-mp $a |- ps $.
    $}
";

#[test]
fn prop_axioms_parse_and_verify_trivially() {
    let db = parse(PROP).unwrap();
    // No `$p` yet; verify_all returns 0 but does not error.
    assert_eq!(verify_all(&db).unwrap(), 0);
    assert!(db.statement_by_label("ax-1").is_some());
    assert!(db.statement_by_label("ax-mp").is_some());
}

#[test]
fn prop_a1i_verifies() {
    // a1i : given |- ph, derive |- ( ps -> ph ).
    //   ax-1[ph,ps]  : |- ( ph -> ( ps -> ph ) )
    //   ax-mp        : from |- ph and |- ( ph -> ( ps -> ph ) ), get |- ( ps -> ph ).
    // ax-mp's floats are (ph := ph, ps := ( ps -> ph )); essentials maj=|- ph,
    // min=|- ( ph -> ( ps -> ph ) ).
    let src = format!(
        "{PROP}
        ${{
          a1i.1 $e |- ph $.
          a1i $p |- ( ps -> ph ) $=
            wph  wps wph wi  a1i.1  wph wps ax-1  ax-mp $.
        $}}
        "
    );
    let db = parse(&src).unwrap();
    assert_eq!(verify_all(&db).unwrap(), 1);
}

#[test]
fn prop_ax2_instance_verifies() {
    // A theorem proved by a single axiom instance: instantiate ax-2 with
    // ch := ph, giving
    //   |- ( ( ph -> ( ps -> ph ) ) -> ( ( ph -> ps ) -> ( ph -> ph ) ) ).
    // The three floats of ax-2 (ph, ps, ch) are supplied as wff args.
    let src = format!(
        "{PROP}
        ax2i $p |- ( ( ph -> ( ps -> ph ) ) -> ( ( ph -> ps ) -> ( ph -> ph ) ) ) $=
          wph wps wph ax-2 $.
        "
    );
    let db = parse(&src).unwrap();
    match verify_all(&db) {
        Ok(n) => assert_eq!(n, 1),
        Err(e) => panic!("ax2i proof failed: {e}"),
    }
}

#[test]
fn prop_a1i_bad_substitution_rejected() {
    // Feed ax-mp a `maj` whose typecode/shape does not match the substitution
    // dictated by the floats: swap the two ax-mp arguments so the essential
    // hypothesis check fails.
    let src = format!(
        "{PROP}
        ${{
          a1i.1 $e |- ph $.
          bad $p |- ( ps -> ph ) $=
            wph  wps wph wi  wph wps ax-1  a1i.1  ax-mp $.
        $}}
        "
    );
    let db = parse(&src).unwrap();
    assert!(matches!(
        verify_all(&db).unwrap_err(),
        MmError::HypothesisMismatch { .. } | MmError::ResultMismatch { .. }
    ));
}

#[test]
fn prop_type_error_rejected() {
    // Build a wff where a `|-` proof expression is supplied where a `wff` is
    // expected: apply `wi` (which needs two wff args) to a `|-` expression.
    // We do this by proving a bogus wff using ax-1 (a `|-` assertion) as a wi
    // argument.
    let src = format!(
        "{PROP}
        bad $p wff ( ph -> ph ) $=
          wph wph wph ax-1 wi $.
        "
    );
    let db = parse(&src).unwrap();
    // ax-1 yields a `|-` expression; `wi`'s float wps expects typecode `wff`.
    assert!(matches!(
        verify_all(&db).unwrap_err(),
        MmError::TypecodeMismatch { expected, found, .. } if expected == "wff" && found == "|-"
    ));
}

// ===========================================================================
// Theory 3 — a tiny binary-operation ("group-ish") theory: a distinct third
// signature, to underline theory-agnosticism, and to exercise reuse of a
// proved theorem as a lemma.
// ===========================================================================

const GROUP: &str = "\
    $c term = ( ) o e |- $.
    $v a b c $.
    ta $f term a $.
    tb $f term b $.
    tc $f term c $.
    te $a term e $.
    top $a term ( a o b ) $.
    weq $a |- ( a = b ) $.   $( degenerate 'everything is provably equal' demo theory $)
    refl $a |- ( a = a ) $.
    symm $a |- ( b = a ) $.
";

#[test]
fn group_theory_parses_and_axioms_ok() {
    let db = parse(GROUP).unwrap();
    assert!(db.is_symbol("o"));
    assert!(db.is_variable("a"));
    // refl is parameterised over `a` only (its conclusion mentions only a).
    let refl = db
        .assertions()
        .find(|x| x.label == "refl")
        .expect("refl present");
    assert_eq!(refl.frame.floats.len(), 1);
    assert_eq!(refl.frame.floats[0].var, "a");
}

#[test]
fn group_theorem_via_axiom_instance() {
    // Prove `|- ( ( a o b ) = ( a o b ) )` by instantiating refl with
    // a := ( a o b ). The float arg is built with `top`.
    let src = format!(
        "{GROUP}
        th $p |- ( ( a o b ) = ( a o b ) ) $=
          ta tb top refl $.
        "
    );
    let db = parse(&src).unwrap();
    assert_eq!(verify_all(&db).unwrap(), 1);
}

// ===========================================================================
// Distinct-variable ($d) checking — its own minimal theory.
// `dvax` requires `$d x y`; a theorem that declares the matching `$d`
// discharges it, one that omits it (or collapses x and y) is rejected.
// ===========================================================================

const DV: &str = "\
    $c |- wff dist $.
    $v x y z $.
    vx $f wff x $.
    vy $f wff y $.
    vz $f wff z $.
    ${
      $d x y $.
      dvax $a |- dist x y $.
    $}
";

#[test]
fn dv_axiom_frame_has_disjoint() {
    let db = parse(DV).unwrap();
    let ax = db.assertions().find(|a| a.label == "dvax").unwrap();
    assert_eq!(ax.frame.disjoints.len(), 1);
}

#[test]
fn dv_satisfied_when_declared() {
    // good : with `$d x y`, instantiate dvax[x:=x, y:=y]. The obligation
    // `$d x y` is present in good's own frame, so it is discharged.
    let src = format!(
        "{DV}
        ${{
          $d x y $.
          good $p |- dist x y $= vx vy dvax $.
        $}}
        "
    );
    let db = parse(&src).unwrap();
    assert_eq!(verify_all(&db).unwrap(), 1);
}

#[test]
fn dv_violation_when_collapsed() {
    // bad1 : instantiate dvax[x:=x, y:=x]. The images of x and y share the
    // variable x, violating `$d x y` outright.
    let src = format!(
        "{DV}
        bad1 $p |- dist x x $= vx vx dvax $.
        "
    );
    let db = parse(&src).unwrap();
    assert!(matches!(
        verify_all(&db).unwrap_err(),
        MmError::DisjointViolation { .. }
    ));
}

#[test]
fn dv_violation_when_obligation_not_declared() {
    // bad2 : instantiate dvax[x:=x, y:=y] but WITHOUT declaring `$d x y` in the
    // theorem's own frame. The distinctness obligation is undischarged.
    let src = format!(
        "{DV}
        bad2 $p |- dist x y $= vx vy dvax $.
        "
    );
    let db = parse(&src).unwrap();
    assert!(matches!(
        verify_all(&db).unwrap_err(),
        MmError::DisjointViolation { .. }
    ));
}

// ===========================================================================
// Cross-theory sanity: verifying one theory's database never consults another.
// ===========================================================================

#[test]
fn single_assertion_verify_api() {
    let db = parse(DEMO0).unwrap();
    let th1 = db.assertions().find(|a| a.label == "th1").unwrap();
    verify_assertion(&db, th1).unwrap();
}
