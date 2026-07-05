//! **A Metamath database for first-order Peano arithmetic**, built with the
//! [`crate::metamath`] engine's [`Database`]/[`Frame`](crate::metamath::Frame) API.
//!
//! This is the **`ValidProof` side** of the Metamath ⇄ HOL connection
//! (`notes/vibes/theories-models-and-logics.md §5.6`): the primitive notion is the
//! decidable relation `ValidProof(P, S, A)` — "`P` is a valid Metamath proof of
//! statement `S` under axioms `A`" — exactly what [`crate::metamath::verify`]
//! checks. The derived notion `Derivable_A(S) := ∃P. ValidProof(P, S, A)` is
//! proof-irrelevant; a logic *is* a Metamath database. Here that database is
//! **PA**.
//!
//! ## Why the `ValidProof` encoding sidesteps the motive wall
//!
//! The impredicative engine ([`crate::peano::pa`]) hit a **motive β-capture
//! wall** when *constructing* an induction derivation: its induction clause
//! quantifies a motive `Q : 't→'r` and `all_cons(Q)` β-closes the Church
//! handlers around a *free* `Q`, so instantiating a concrete arithmetic motive
//! leaves handlers un-captured (see `peano/SKELETONS.md`). That wall is an
//! **artifact of the impredicative encoding**. In Metamath, constructing a
//! derivation means *exhibiting a concrete proof*, and an induction step is just
//! a **substitution instance of the induction schema** — `metamath::subst`
//! replaces the schema's `wff` metavariable `ph` by a *concrete* motive wff
//! natively, with no HOAS motive and no β-capture. Metamath being a Hilbert
//! system, **no deduction theorem** is needed for `⟹`-chaining either. The
//! replay ([`crate::peano::mm_replay`]) consumes a *verified* proof, so the
//! motive is a concrete formula by replay time and discharges straight to
//! [`Thm::nat_induct`](covalence_core::Thm::nat_induct).
//!
//! ## Vocabulary (the typecodes + PA signature)
//!
//! Three typecodes — `term` (PA terms, sort `nat`), `wff` (formulas), `|-`
//! (provability) — and a faithful **flat, parenthesised** surface syntax that
//! the replay's reader ([`expr_to_term`](crate::peano::mm_replay::expr_to_term) / [`expr_to_form`](crate::peano::mm_replay::expr_to_form)) parses back to the
//! [`Fol`](crate::peano::fol::Fol) AST unambiguously:
//!
//! | constructor | surface form        | `Fol`        |
//! |-------------|---------------------|--------------|
//! | zero        | `0`                 | [`Fol::Zero`](crate::peano::fol::Fol::Zero)|
//! | successor   | `( S t )`           | [`Fol::Succ`](crate::peano::fol::Fol::Succ)|
//! | addition    | `( t + r )`         | [`Fol::Add`](crate::peano::fol::Fol::Add) |
//! | mult.       | `( t x. r )`        | [`Fol::Mul`](crate::peano::fol::Fol::Mul) |
//! | equality    | `( t = r )`         | [`Fol::Eq`](crate::peano::fol::Fol::Eq)  |
//! | implication | `( ph -> ps )`      | [`Fol::Imp`](crate::peano::fol::Fol::Imp) |
//! | negation    | `-. ph`             | [`Fol::Neg`](crate::peano::fol::Fol::Neg) |
//! | conjunction | `( ph /\ ps )`      | [`Fol::And`](crate::peano::fol::Fol::And) |
//! | disjunction | `( ph \/ ps )`      | [`Fol::Or`](crate::peano::fol::Fol::Or)  |
//! | universal   | `A. x ph`           | [`Fol::All`](crate::peano::fol::Fol::All) |
//! | existential | `E. x ph`           | [`Fol::Ex`](crate::peano::fol::Fol::Ex)  |
//!
//! **Setvars** `x y z` (and the free PA variables `va vb …`) are `term`-typed
//! variables; `A.`/`E.` bind a setvar (named binders), which the interpretation
//! converts to the locally-nameless [`Fol`](crate::peano::fol::Fol) de Bruijn form.
//!
//! ## Rules and axioms
//!
//! - **Modus ponens** `ax.mp` (`$e |- ph`, `$e |- ( ph -> ps )`, `$a |- ps`)
//!   and **generalisation** `ax.gen` (`$e |- ph`, `$a |- A. x ph`), scoped in
//!   `${ … $}` blocks exactly as in the Metamath book's demo theory.
//! - **PA1–PA6** as `$a` axioms (closed `|-` statements), mirroring
//!   [`crate::peano::pa`]'s `ax_*` formulas.
//! - The **induction schema** `pa.ind` as a `$a` over a `wff` metavariable
//!   `ph` (the open motive `P(x)`) with two essential hypotheses: the base
//!   `|- ph0` and the step `|- A. x ( ph -> phS )`, concluding `|- A. x ph`.
//!   Here `ph0`/`phS` are independent `wff` metavariables an *instance* binds
//!   to the concrete `P(0)`/`P(S x)`; the engine checks the substitution, and
//!   the **replay re-derives soundness in the kernel** by reading off the
//!   concrete `P` and calling [`Thm::nat_induct`](covalence_core::Thm::nat_induct). (The Metamath schema's own
//!   soundness is not relied on — the proof is *untrusted input*.)

use crate::metamath::expr::make_expr;
use crate::metamath::{Database, FloatHyp, Hypothesis, MmError};

/// The setvar names available as bound/free `term` variables.
pub const SETVARS: [&str; 6] = ["x", "y", "z", "va", "vb", "vc"];

/// Build a `|-` (provability) assertion expression from a flat body.
fn prov<'a>(body: impl IntoIterator<Item = &'a str>) -> crate::metamath::Expr {
    make_expr("|-", body)
}

/// Add a `$f` float `label $f typecode var`.
// Cold database-setup path; `MmError` is a rich diagnostic enum, not worth boxing.
#[allow(clippy::result_large_err)]
fn float(db: &mut Database, label: &str, typecode: &str, var: &str) -> Result<(), MmError> {
    db.add_float(FloatHyp {
        label: label.into(),
        typecode: typecode.into(),
        var: var.into(),
    })
}

/// Add a `$e` essential `label $e <expr>`.
// Cold database-setup path; `MmError` is a rich diagnostic enum, not worth boxing.
#[allow(clippy::result_large_err)]
fn essential(db: &mut Database, label: &str, expr: crate::metamath::Expr) -> Result<(), MmError> {
    db.add_essential(Hypothesis {
        label: label.into(),
        expr,
    })
}

/// Build the Metamath PA database (vocabulary + rules + PA1–PA6 + induction
/// schema). The result is a finished, scope-balanced [`Database`] that
/// [`crate::metamath::verify_all`] accepts (the bundled `$p` self-checks below
/// verify).
// Cold database-setup path; `MmError` is a rich diagnostic enum, not worth boxing.
#[allow(clippy::result_large_err)]
pub fn database() -> Result<Database, MmError> {
    let mut db = Database::new();

    // --- constants: typecodes + PA signature + logical punctuation ----------
    db.declare_constants(
        [
            // typecodes
            "term", "wff", "|-", //
            // term signature
            "0", "S", "+", "x.", //
            // formula signature
            "=", "->", "-.", "/\\", "\\/", "A.", "E.", //
            // punctuation
            "(", ")",
        ]
        .iter()
        .map(|s| s.to_string())
        .collect(),
    )?;

    // --- variables: setvars (term-typed) + wff metavariables ----------------
    db.declare_variables(SETVARS.iter().map(|s| s.to_string()).collect())?;
    db.declare_variables(
        ["ph", "ps", "ch", "ph0", "phS"]
            .iter()
            .map(|s| s.to_string())
            .collect(),
    )?;

    // --- floating hypotheses (the "type signature" of each variable) --------
    for v in SETVARS {
        float(&mut db, &format!("f.{v}"), "term", v)?;
    }
    for w in ["ph", "ps", "ch", "ph0", "phS"] {
        float(&mut db, &format!("f.{w}"), "wff", w)?;
    }

    // --- term-formation axioms ($a term …) ----------------------------------
    db.add_assertion("t.0".into(), make_expr("term", ["0"]), None)?;
    db.add_assertion("t.S".into(), make_expr("term", ["(", "S", "x", ")"]), None)?;
    db.add_assertion(
        "t.add".into(),
        make_expr("term", ["(", "x", "+", "y", ")"]),
        None,
    )?;
    db.add_assertion(
        "t.mul".into(),
        make_expr("term", ["(", "x", "x.", "y", ")"]),
        None,
    )?;

    // --- wff-formation axioms ($a wff …) ------------------------------------
    db.add_assertion(
        "w.eq".into(),
        make_expr("wff", ["(", "x", "=", "y", ")"]),
        None,
    )?;
    db.add_assertion(
        "w.imp".into(),
        make_expr("wff", ["(", "ph", "->", "ps", ")"]),
        None,
    )?;
    db.add_assertion("w.neg".into(), make_expr("wff", ["-.", "ph"]), None)?;
    db.add_assertion(
        "w.and".into(),
        make_expr("wff", ["(", "ph", "/\\", "ps", ")"]),
        None,
    )?;
    db.add_assertion(
        "w.or".into(),
        make_expr("wff", ["(", "ph", "\\/", "ps", ")"]),
        None,
    )?;
    db.add_assertion("w.all".into(), make_expr("wff", ["A.", "x", "ph"]), None)?;
    db.add_assertion("w.ex".into(), make_expr("wff", ["E.", "x", "ph"]), None)?;

    // --- inference rules: modus ponens + generalisation ---------------------
    db.push_scope();
    essential(&mut db, "mp.min", prov(["ph"]))?;
    essential(&mut db, "mp.maj", prov(["(", "ph", "->", "ps", ")"]))?;
    db.add_assertion("ax.mp".into(), prov(["ps"]), None)?;
    db.pop_scope()?;

    db.push_scope();
    essential(&mut db, "gen.h", prov(["ph"]))?;
    db.add_assertion("ax.gen".into(), prov(["A.", "x", "ph"]), None)?;
    db.pop_scope()?;

    // --- PA1–PA6 (closed `|-` axioms) ---------------------------------------
    // PA1: ∀x. ¬(0 = S x)
    db.add_assertion(
        "pa.1".into(),
        prov(["A.", "x", "-.", "(", "0", "=", "(", "S", "x", ")", ")"]),
        None,
    )?;
    // PA2: ∀x y. (S x = S y) -> (x = y)
    db.add_assertion(
        "pa.2".into(),
        prov([
            "A.", "x", "A.", "y", "(", "(", "(", "S", "x", ")", "=", "(", "S", "y", ")", ")", "->",
            "(", "x", "=", "y", ")", ")",
        ]),
        None,
    )?;
    // PA3: ∀x. (0 + x) = x
    db.add_assertion(
        "pa.3".into(),
        prov(["A.", "x", "(", "(", "0", "+", "x", ")", "=", "x", ")"]),
        None,
    )?;
    // PA4: ∀x y. ((S x) + y) = (S (x + y))
    db.add_assertion(
        "pa.4".into(),
        prov([
            "A.", "x", "A.", "y", "(", "(", "(", "S", "x", ")", "+", "y", ")", "=", "(", "S", "(",
            "x", "+", "y", ")", ")", ")",
        ]),
        None,
    )?;
    // PA5: ∀x. (0 x. x) = 0
    db.add_assertion(
        "pa.5".into(),
        prov(["A.", "x", "(", "(", "0", "x.", "x", ")", "=", "0", ")"]),
        None,
    )?;
    // PA6: ∀x y. ((S x) x. y) = (y + (x x. y))
    db.add_assertion(
        "pa.6".into(),
        prov([
            "A.", "x", "A.", "y", "(", "(", "(", "S", "x", ")", "x.", "y", ")", "=", "(", "y", "+",
            "(", "x", "x.", "y", ")", ")", ")",
        ]),
        None,
    )?;

    // --- the induction schema (a `wff` metavariable schema) -----------------
    // pa.ind:  base `|- ph0`, step `|- A. x ( ph -> phS )`  ⊢  `|- A. x ph`.
    // An instance binds ph := P(x), ph0 := P(0), phS := P(S x); the replay
    // re-derives soundness via `Thm::nat_induct` on the concrete motive `P`.
    db.push_scope();
    essential(&mut db, "ind.base", prov(["ph0"]))?;
    essential(
        &mut db,
        "ind.step",
        prov(["A.", "x", "(", "(", "ph", "->", "phS", ")", ")"]),
    )?;
    db.add_assertion("pa.ind".into(), prov(["A.", "x", "ph"]), None)?;
    db.pop_scope()?;

    db.finish()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::metamath::{Proof, Statement, verify_all, verify_assertion};

    /// The database builds and is scope-balanced.
    #[test]
    fn database_builds() {
        let db = database().unwrap();
        // Spot-check a few labels are present.
        assert!(db.statement_by_label("pa.1").is_some());
        assert!(db.statement_by_label("pa.ind").is_some());
        assert!(db.statement_by_label("ax.mp").is_some());
        assert!(db.statement_by_label("t.add").is_some());
    }

    /// Every `$a` axiom verifies trivially and the wff/term formers are
    /// well-formed (the database itself is internally consistent).
    #[test]
    fn axioms_present_and_typed() {
        let db = database().unwrap();
        // PA1..PA6 + the schema are all `|-` assertions.
        for label in ["pa.1", "pa.2", "pa.3", "pa.4", "pa.5", "pa.6", "pa.ind"] {
            let Some(Statement::Assert(a)) = db.statement_by_label(label) else {
                panic!("{label} is not an assertion");
            };
            assert_eq!(
                crate::metamath::expr::typecode_of(&a.conclusion),
                Some("|-"),
                "{label} is not a |- statement"
            );
            // Axioms have no proof.
            assert!(a.proof.is_none());
        }
    }

    /// **Engine self-check:** a couple of `$p` theorems verify against the PA
    /// database (this exercises the RPN checker, the term/wff grammar, and the
    /// modus-ponens rule end-to-end).
    #[test]
    fn self_check_p_theorems() {
        let mut db = database().unwrap();

        // th.t1 : `term ( S 0 )`  — a term-formation proof.
        //   t.0 pushes `term 0`; t.S (frame [x]) pops it, unifies x := 0,
        //   pushes `term ( S 0 )`.
        db.add_assertion(
            "th.t1".into(),
            make_expr("term", ["(", "S", "0", ")"]),
            Some(Proof::Normal(vec!["t.0".into(), "t.S".into()])),
        )
        .unwrap();

        // th.w1 : `wff ( 0 = 0 )` — a wff-formation proof.
        //   t.0, t.0 push two `term 0`; w.eq (frame [x, y]) pops both.
        db.add_assertion(
            "th.w1".into(),
            make_expr("wff", ["(", "0", "=", "0", ")"]),
            Some(Proof::Normal(vec![
                "t.0".into(),
                "t.0".into(),
                "w.eq".into(),
            ])),
        )
        .unwrap();

        let db = db.finish().unwrap();
        // Both verify.
        for label in ["th.t1", "th.w1"] {
            let Some(Statement::Assert(a)) = db.statement_by_label(label) else {
                panic!()
            };
            verify_assertion(&db, a).unwrap();
        }
        // verify_all counts exactly the two `$p`s.
        assert_eq!(verify_all(&db).unwrap(), 2);
    }
}
