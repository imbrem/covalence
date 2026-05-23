//! DRAT proof rejection tests.
//!
//! Each test constructs a CNF formula and an invalid DRAT proof, then verifies
//! that both [`NaiveDratChecker`] and [`WatchedDratChecker`] reject the proof.

use covalence_sat::{
    Clause, Cnf, DratProof, DratStep, DratVerifier, NaiveDratChecker, WatchedDratChecker,
    check_proof,
};

/// Run a DRAT proof through both checkers, returning `(naive_result, watched_result)`.
fn check_both(cnf: &Cnf, proof: &DratProof) -> (bool, bool) {
    let mut naive = NaiveDratChecker::new(cnf);
    let naive_result = check_proof(&mut naive, proof);
    let mut watched = WatchedDratChecker::new(cnf);
    let watched_result = check_proof(&mut watched, proof);
    (naive_result, watched_result)
}

/// Assert that both checkers reject the proof.
fn assert_both_reject(cnf: &Cnf, proof: &DratProof) {
    let (naive, watched) = check_both(cnf, proof);
    assert!(
        !naive,
        "NaiveDratChecker should reject this proof, but it accepted"
    );
    assert!(
        !watched,
        "WatchedDratChecker should reject this proof, but it accepted"
    );
}

/// Assert that both checkers accept the proof (used for sanity checks).
fn assert_both_accept(cnf: &Cnf, proof: &DratProof) {
    let (naive, watched) = check_both(cnf, proof);
    assert!(
        naive,
        "NaiveDratChecker should accept this proof, but it rejected"
    );
    assert!(
        watched,
        "WatchedDratChecker should accept this proof, but it rejected"
    );
}

// -----------------------------------------------------------------------
// 1. Non-AT clause added
// -----------------------------------------------------------------------

#[test]
fn non_at_clause_added_two_vars() {
    // Formula: {x, y} ∧ {x, ~y}
    // This is SAT (x=true), but suppose we try to add {~x} as an AT lemma.
    //
    // AT check for {~x}: negate ~x → assign x=true.
    // With x=true, both {x,y} and {x,~y} are satisfied. No conflict.
    // So {~x} is NOT AT. The checker should reject at the Add step.
    //
    // Actually wait — the clauses are all satisfied, so no conflict is found
    // during unit prop. That means no empty clause is falsified, and
    // propagation reaches fixpoint without conflict → not AT.
    //
    // Hmm, actually re-checking: when we negate ~x we set x=true (the
    // negation of ~x). With x=true both clauses are satisfied, fixpoint
    // reached without conflict → not AT. Correct.
    //
    // Let's use a formula where the added clause is clearly not AT.
    // Formula: {x, y} ∧ {~x, y}
    // Try to add {~y}:
    //   Negate ~y → assign y=true.
    //   Both clauses are satisfied → fixpoint, no conflict → not AT.
    let mut cnf = Cnf::new();
    let x = cnf.fresh();
    let y = cnf.fresh();
    cnf.clause([x, y]);
    cnf.clause([!x, y]);

    let proof = DratProof::new([DratStep::Add(Clause::new([!y]))]);
    assert_both_reject(&cnf, &proof);
}

#[test]
fn non_at_clause_added_three_vars() {
    // Formula: {x, y, z} (single clause, three variables).
    // Try to add {~x, ~y} as an AT step.
    //
    // AT check for {~x, ~y}: negate both → assign x=true, y=true.
    // The clause {x, y, z} is satisfied (x=true) → no conflict → not AT.
    let mut cnf = Cnf::new();
    let x = cnf.fresh();
    let y = cnf.fresh();
    let z = cnf.fresh();
    cnf.clause([x, y, z]);

    let proof = DratProof::new([DratStep::Add(Clause::new([!x, !y]))]);
    assert_both_reject(&cnf, &proof);
}

#[test]
fn non_at_unit_clause_no_conflict() {
    // Formula: {x, y} ∧ {~x, y}
    // The resolvent on x is {y}, so {y} IS AT. But {~y} is not.
    //
    // Sanity: verify {y} is accepted.
    let mut cnf = Cnf::new();
    let x = cnf.fresh();
    let y = cnf.fresh();
    cnf.clause([x, y]);
    cnf.clause([!x, y]);

    // {y} should be AT: negate y → assign y=false.
    // {x,y}: y false, x unset → unit, assign x=true.
    // {~x,y}: ~x false (x=true), y false → conflict. AT!
    let _valid_proof = DratProof::new([DratStep::Add(Clause::new([y]))]);
    // Just test AT step is accepted (won't complete because no empty clause)
    let mut naive = NaiveDratChecker::new(&cnf);
    assert!(naive.add_clause(&Clause::new([y])));
    let mut watched = WatchedDratChecker::new(&cnf);
    assert!(watched.add_clause(&Clause::new([y])));

    // But {~y} is not AT (as shown above), so this proof should be rejected.
    let invalid_proof = DratProof::new([
        DratStep::Add(Clause::new([!y])),
        DratStep::Add(Clause::new([])),
    ]);
    assert_both_reject(&cnf, &invalid_proof);
}

// -----------------------------------------------------------------------
// 2. Proof for SAT formula
// -----------------------------------------------------------------------

#[test]
fn sat_formula_proof_rejected() {
    // Formula: {x} — trivially SAT.
    // Any proof that claims UNSAT should fail. In particular, the empty
    // clause is not AT w.r.t. {x}:
    //   AT check for ∅: empty assignment. Unit prop: {x} → assign x=true.
    //   Fixpoint reached (only one clause, now satisfied). No conflict → not AT.
    let mut cnf = Cnf::new();
    let x = cnf.fresh();
    cnf.clause([x]);

    let proof = DratProof::new([DratStep::Add(Clause::new([]))]);
    assert_both_reject(&cnf, &proof);
}

#[test]
fn sat_formula_two_clauses_rejected() {
    // Formula: {x, y} ∧ {~x, y} — SAT (y=true satisfies both).
    // Attempt to derive the empty clause directly.
    //
    // AT check for ∅: empty assignment. Unit prop:
    //   {x, y}: 2 unset → not unit.
    //   {~x, y}: 2 unset → not unit.
    //   Fixpoint. No conflict → not AT.
    let mut cnf = Cnf::new();
    let x = cnf.fresh();
    let y = cnf.fresh();
    cnf.clause([x, y]);
    cnf.clause([!x, y]);

    let proof = DratProof::new([DratStep::Add(Clause::new([]))]);
    assert_both_reject(&cnf, &proof);
}

#[test]
fn sat_formula_with_intermediate_steps_rejected() {
    // Formula: {x} ∧ {y} — SAT (x=true, y=true).
    // Try adding {~x} first, then ∅.
    //
    // AT check for {~x}: negate ~x → assign x=true.
    // {x}: satisfied. {y}: y unset, unit → assign y=true.
    // Fixpoint, all satisfied, no conflict → not AT.
    // Rejected at first step.
    let mut cnf = Cnf::new();
    let x = cnf.fresh();
    let y = cnf.fresh();
    cnf.clause([x]);
    cnf.clause([y]);

    let proof = DratProof::new([
        DratStep::Add(Clause::new([!x])),
        DratStep::Add(Clause::new([])),
    ]);
    assert_both_reject(&cnf, &proof);
}

// -----------------------------------------------------------------------
// 3. Incomplete proof — valid AT steps but never derives empty clause
// -----------------------------------------------------------------------

#[test]
fn incomplete_proof_no_empty_clause() {
    // Formula: {x, y} ∧ {x, ~y} ∧ {~x, y} ∧ {~x, ~y} — UNSAT (all 4
    // combinations of 2 variables).
    //
    // A valid full proof would be:
    //   Add({x})    — AT: negate x → x=false. {~x,y}: unit y=true.
    //                 {~x,~y}: ~y false → conflict. AT!
    //   Add({~x})   — AT: negate ~x → x=true. {x,y}: sat. {x,~y}: sat.
    //                 {~x,y}: y unset, ~x false → unit y=true.
    //                 {~x,~y}: ~x false, ~y false → conflict. AT!
    //   Add(∅)      — AT: empty assignment. {x}: unit x=true.
    //                 {~x}: unit x=false → conflict. AT!
    //
    // But if we stop after {x} and {~x}, we never derive ∅. The proof
    // is "incomplete" — check_proof should return false.
    let mut cnf = Cnf::new();
    let x = cnf.fresh();
    let y = cnf.fresh();
    cnf.clause([x, y]);
    cnf.clause([x, !y]);
    cnf.clause([!x, y]);
    cnf.clause([!x, !y]);

    // Only add intermediate lemmas, never the empty clause.
    let proof = DratProof::new([
        DratStep::Add(Clause::new([x])),
        DratStep::Add(Clause::new([!x])),
    ]);
    assert_both_reject(&cnf, &proof);

    // Sanity: the full proof should be accepted.
    let full_proof = DratProof::new([
        DratStep::Add(Clause::new([x])),
        DratStep::Add(Clause::new([!x])),
        DratStep::Add(Clause::new([])),
    ]);
    assert_both_accept(&cnf, &full_proof);
}

#[test]
fn incomplete_proof_single_valid_step() {
    // Formula: {x} ∧ {~x, y} ∧ {~y} — UNSAT (x forced true, y forced true,
    // but {~y} contradicts).
    //
    // Full proof: Add(∅) is directly AT here:
    //   Empty assignment → {x} unit → x=true → {~x,y} unit → y=true →
    //   {~y} all false → conflict. AT!
    //
    // But if the proof only adds {y} (which is AT) and stops, it's incomplete.
    let mut cnf = Cnf::new();
    let x = cnf.fresh();
    let y = cnf.fresh();
    cnf.clause([x]);
    cnf.clause([!x, y]);
    cnf.clause([!y]);

    // Add {y} — is it AT? Negate y → y=false. {~y}: satisfied.
    // {x}: unit → x=true. {~x,y}: ~x false, y false → conflict. AT!
    // But we never add the empty clause.
    let proof = DratProof::new([DratStep::Add(Clause::new([y]))]);
    assert_both_reject(&cnf, &proof);
}

// -----------------------------------------------------------------------
// 4. Skip intermediate steps (re-test with both checkers)
// -----------------------------------------------------------------------

#[test]
fn skip_intermediate_steps_four_clause() {
    // {x,y} ∧ {x,~y} ∧ {~x,y} ∧ {~x,~y} — UNSAT.
    // Trying to jump directly to ∅ without intermediate lemmas fails
    // because ∅ is not AT w.r.t. the original clauses alone.
    //
    // AT check for ∅: empty assignment. Unit prop:
    //   All four clauses have 2 unset literals → no unit clause → fixpoint.
    //   No conflict → not AT.
    let mut cnf = Cnf::new();
    let x = cnf.fresh();
    let y = cnf.fresh();
    cnf.clause([x, y]);
    cnf.clause([x, !y]);
    cnf.clause([!x, y]);
    cnf.clause([!x, !y]);

    let proof = DratProof::new([DratStep::Add(Clause::new([]))]);
    assert_both_reject(&cnf, &proof);
}

#[test]
fn skip_intermediate_steps_three_var() {
    // A 3-variable UNSAT formula requiring multiple resolution steps.
    // {x,y} ∧ {x,~y} ∧ {~x,z} ∧ {~x,~z} — UNSAT.
    //
    // Resolving on y: {x}. Resolving on z: {~x}. Then {x} ∧ {~x} → ∅.
    // But ∅ is not directly AT without first deriving {x} or {~x}.
    //
    // AT check for ∅: empty assignment. Unit prop:
    //   All clauses have ≥2 unset literals → fixpoint. Not AT.
    let mut cnf = Cnf::new();
    let x = cnf.fresh();
    let y = cnf.fresh();
    let z = cnf.fresh();
    cnf.clause([x, y]);
    cnf.clause([x, !y]);
    cnf.clause([!x, z]);
    cnf.clause([!x, !z]);

    let proof = DratProof::new([DratStep::Add(Clause::new([]))]);
    assert_both_reject(&cnf, &proof);

    // With intermediate steps it should work:
    // Add {x}: negate x → x=false. {~x,z}: unit z=true. {~x,~z}: conflict. AT!
    // Add {~x}: negate ~x → x=true. {x,y}: sat. {x,~y}: sat.
    //   Remaining: {~x,z}: ~x false, z unset → unit z=true.
    //   {~x,~z}: ~x false, ~z false → conflict. AT!
    // Add ∅: {x}: unit x=true. {~x}: conflict. AT!
    let valid_proof = DratProof::new([
        DratStep::Add(Clause::new([x])),
        DratStep::Add(Clause::new([!x])),
        DratStep::Add(Clause::new([])),
    ]);
    assert_both_accept(&cnf, &valid_proof);
}

// -----------------------------------------------------------------------
// 5. Wrong variable in proof
// -----------------------------------------------------------------------

#[test]
fn wrong_variable_in_proof() {
    // Formula: {x} ∧ {~x} — UNSAT.
    // Valid proof: Add(∅).
    // Invalid proof: Add({y}), Add(∅).
    //
    // Add({y}): negate y → y=false. Unit prop:
    //   {x}: unit → x=true. {~x}: conflict. AT!
    //   So {y} is actually AT (the existing clauses force a conflict
    //   independent of y). This is fine — y is irrelevant but AT.
    //
    // Let's use a formula where the wrong variable actually prevents AT.
    // Formula: {x, y} ∧ {x, ~y} ∧ {~x, y} ∧ {~x, ~y} — UNSAT.
    // Try adding {z} where z is a new variable not in the formula.
    //
    // AT check for {z}: negate z → z=false.
    //   All four original clauses have 2 unset lits (x, y) → fixpoint.
    //   No conflict → not AT.
    let mut cnf = Cnf::new();
    let x = cnf.fresh();
    let y = cnf.fresh();
    let z = cnf.fresh();
    cnf.clause([x, y]);
    cnf.clause([x, !y]);
    cnf.clause([!x, y]);
    cnf.clause([!x, !y]);

    // Try to add {z} — z is irrelevant, doesn't help propagation at all.
    let proof = DratProof::new([
        DratStep::Add(Clause::new([z])),
        DratStep::Add(Clause::new([])),
    ]);
    assert_both_reject(&cnf, &proof);
}

#[test]
fn wrong_variable_unit_clause() {
    // Formula: {x, y} ∧ {x, ~y} ∧ {~x, y} ∧ {~x, ~y} — UNSAT.
    // The correct intermediate lemma would be {x} (AT via {~x,y} and {~x,~y}).
    // Instead we try {z} — a completely unrelated variable.
    //
    // AT check for {z}: negate z → z=false. No clauses mention z.
    // All original clauses have 2 unset lits → fixpoint → not AT.
    let mut cnf = Cnf::new();
    let x = cnf.fresh();
    let y = cnf.fresh();
    let z = cnf.fresh();
    cnf.clause([x, y]);
    cnf.clause([x, !y]);
    cnf.clause([!x, y]);
    cnf.clause([!x, !y]);

    let proof = DratProof::new([DratStep::Add(Clause::new([z]))]);
    assert_both_reject(&cnf, &proof);
}

#[test]
fn wrong_polarity_in_proof() {
    // Formula: {x, y} ∧ {x, ~y} ∧ {~x, y} ∧ {~x, ~y} — UNSAT.
    // Correct proof step 1: Add({x}) — AT.
    // Wrong polarity: Add({~y}) instead.
    //
    // AT check for {~y}: negate ~y → y=true.
    // {x, y}: satisfied. {~x, y}: satisfied.
    // {x, ~y}: ~y false, x unset → unit, assign x=true.
    // {~x, ~y}: ~x false, ~y false → conflict. AT!
    //
    // Hmm, {~y} is also AT. Let me find something that truly fails.
    // Actually, in this fully symmetric formula, any unit clause over x or y
    // is AT. Let me use a different formula.
    //
    // Formula: {x, y} ∧ {~x, y} — SAT (y=true). UNSAT if we add {~y}.
    // Actually this is SAT, so can't derive ∅.
    //
    // Let me use: {a, b} ∧ {a, ~b} ∧ {~a} — UNSAT.
    // Correct proof: Add({a}) then Add(∅). But {a} is AT:
    //   Negate a → a=false. {~a}: satisfied. {a,b}: a false, b unit → b=true.
    //   {a,~b}: a false, ~b false → conflict. AT!
    //
    // Wrong: Add({b}) instead.
    // AT check for {b}: negate b → b=false.
    //   {~a}: a unset → unit → a=false. {a,b}: a false, b false → conflict. AT!
    // So {b} is also AT here. Both are AT because the formula is strongly
    // constrained.
    //
    // The 4-clause formula with a third variable is the cleanest test for
    // "wrong variable". We already test this above. Let's verify with a
    // fresh variable as the "wrong polarity".
    //
    // Use: {x, y} ∧ {~x} ∧ {~y} — UNSAT.
    // Correct: Add(∅) directly (AT: {~x} → x=false, {x,y} → y=true,
    //   {~y} → conflict).
    // Wrong: Add({x}) — not AT because:
    //   Negate x → x=false. {~x}: satisfied. {x,y}: x false, y unit → y=true.
    //   {~y}: ~y false → conflict. Wait, that IS a conflict → AT!
    // Hmm, {x} is AT too.
    //
    // It's hard to find a "wrong variable" that isn't AT when the formula
    // has enough constraint propagation. The 4-clause 2-var formula with
    // an extra variable z is the right test — we already have it above.
    // Let's try a different angle: wrong clause that creates no propagation.
    //
    // Formula: {x, y} ∧ {~x, ~y} — SAT (x=true, y=false or x=false, y=true).
    // This is SAT, so ∅ can never be AT. But we try adding {x} which is not AT:
    //   Negate x → x=false. {x,y}: x false, y unit → y=true.
    //   {~x,~y}: ~x true → satisfied. Fixpoint, no conflict → not AT.
    // Wait, {~x,~y} has ~x true (x=false), so it's satisfied. And after y=true
    // everything is satisfied. No conflict. Not AT.
    //
    // OK so this clause IS rejected. But the formula is SAT so it's category 2.
    // Let's just keep the tests we have for category 5 (they work correctly).
    // Adding a note to explain the scenario.

    // Formula: {a, b} ∧ {~a, ~b} — SAT, but we use it to show {a, b, c}
    // (with a fresh var c) is not AT, demonstrating that "wrong" extra
    // variables in a clause weaken the AT check.
    //
    // Actually, the fundamental test for "wrong variable" is using a variable
    // that doesn't appear in the formula and adds no propagation power.
    // That's already covered by wrong_variable_in_proof and
    // wrong_variable_unit_clause above. Let's add one more with a
    // "wrong binary clause".
    let mut cnf = Cnf::new();
    let x = cnf.fresh();
    let y = cnf.fresh();
    let z = cnf.fresh();
    cnf.clause([x, y]);
    cnf.clause([x, !y]);
    cnf.clause([!x, y]);
    cnf.clause([!x, !y]);

    // Try adding {y, z} — two irrelevant/wrong literals.
    // AT check for {y, z}: negate y → y=false, negate z → z=false.
    // {x, y}: y false, x unset. {x, ~y}: ~y true → satisfied.
    // {~x, y}: y false, ~x unset. {~x, ~y}: ~y true → satisfied.
    // Remaining unsatisfied: {x, y} with x unset, {~x, y} with ~x unset.
    // {x, y}: 1 unset (x) → unit → x=true.
    // {~x, y}: ~x false, y false → conflict. AT!
    //
    // Hmm, so {y, z} IS AT because y=false drives enough propagation.
    // This is because y appears in the formula. Let's use only z.

    // {z, z}: duplicate, but let's try a binary with two fresh vars.
    let w = cnf.fresh();
    let proof = DratProof::new([
        DratStep::Add(Clause::new([z, w])),
        DratStep::Add(Clause::new([])),
    ]);
    // AT check for {z, w}: negate z → z=false, negate w → w=false.
    // All four original clauses have 2 unset (x, y) → fixpoint. Not AT.
    assert_both_reject(&cnf, &proof);
}

// -----------------------------------------------------------------------
// 6. Empty proof
// -----------------------------------------------------------------------

#[test]
fn empty_proof_rejected() {
    // Formula: {x} ∧ {~x} — UNSAT.
    // An empty proof (no steps) never derives the empty clause.
    let mut cnf = Cnf::new();
    let x = cnf.fresh();
    cnf.clause([x]);
    cnf.clause([!x]);

    let proof = DratProof::new([]);
    assert_both_reject(&cnf, &proof);
}

#[test]
fn empty_proof_on_sat_formula_rejected() {
    // Formula: {x} — SAT.
    // Empty proof, obviously rejected (no empty clause derived).
    let mut cnf = Cnf::new();
    let x = cnf.fresh();
    cnf.clause([x]);

    let proof = DratProof::new([]);
    assert_both_reject(&cnf, &proof);
}

#[test]
fn empty_proof_on_empty_formula_rejected() {
    // Empty formula (vacuously SAT). Empty proof.
    // The empty clause is never derived → rejected.
    let cnf = Cnf::new();
    let proof = DratProof::new([]);
    assert_both_reject(&cnf, &proof);
}

// -----------------------------------------------------------------------
// 7. Delete-only proof
// -----------------------------------------------------------------------

#[test]
fn delete_only_proof_rejected() {
    // Formula: {x} ∧ {~x} — UNSAT.
    // Proof only deletes clauses, never adds the empty clause.
    let mut cnf = Cnf::new();
    let x = cnf.fresh();
    cnf.clause([x]);
    cnf.clause([!x]);

    let proof = DratProof::new([
        DratStep::Delete(Clause::new([x])),
        DratStep::Delete(Clause::new([!x])),
    ]);
    assert_both_reject(&cnf, &proof);
}

#[test]
fn delete_only_proof_multiple_clauses() {
    // Formula: {x, y} ∧ {x, ~y} ∧ {~x, y} ∧ {~x, ~y} — UNSAT.
    // Delete all clauses but never add anything.
    let mut cnf = Cnf::new();
    let x = cnf.fresh();
    let y = cnf.fresh();
    cnf.clause([x, y]);
    cnf.clause([x, !y]);
    cnf.clause([!x, y]);
    cnf.clause([!x, !y]);

    let proof = DratProof::new([
        DratStep::Delete(Clause::new([x, y])),
        DratStep::Delete(Clause::new([x, !y])),
        DratStep::Delete(Clause::new([!x, y])),
        DratStep::Delete(Clause::new([!x, !y])),
    ]);
    assert_both_reject(&cnf, &proof);
}

#[test]
fn delete_then_attempt_empty_clause() {
    // Formula: {x} ∧ {~x} — UNSAT.
    // Delete both clauses, then try to add ∅. After deletion, there are no
    // active clauses, so unit prop from the empty assignment reaches fixpoint
    // immediately with no conflict → ∅ is not AT.
    let mut cnf = Cnf::new();
    let x = cnf.fresh();
    cnf.clause([x]);
    cnf.clause([!x]);

    let proof = DratProof::new([
        DratStep::Delete(Clause::new([x])),
        DratStep::Delete(Clause::new([!x])),
        DratStep::Add(Clause::new([])),
    ]);
    assert_both_reject(&cnf, &proof);
}

// -----------------------------------------------------------------------
// 8. Add non-empty then stop
// -----------------------------------------------------------------------

#[test]
fn add_valid_at_clauses_but_no_empty() {
    // Formula: {x, y} ∧ {x, ~y} ∧ {~x, y} ∧ {~x, ~y} — UNSAT.
    // Add valid AT lemmas {x} and {~x}, but never derive ∅.
    let mut cnf = Cnf::new();
    let x = cnf.fresh();
    let y = cnf.fresh();
    cnf.clause([x, y]);
    cnf.clause([x, !y]);
    cnf.clause([!x, y]);
    cnf.clause([!x, !y]);

    let proof = DratProof::new([
        DratStep::Add(Clause::new([x])),
        DratStep::Add(Clause::new([!x])),
        // Missing: DratStep::Add(Clause::new([]))
    ]);
    assert_both_reject(&cnf, &proof);
}

#[test]
fn add_single_valid_at_clause_then_stop() {
    // Formula: {x} ∧ {~x, y} ∧ {~y} — UNSAT.
    // The empty clause is directly AT, but instead we add {~x} (AT) and stop.
    //
    // AT check for {~x}: negate ~x → x=true. {x}: satisfied.
    //   {~x,y}: ~x false, y unit → y=true. {~y}: ~y false → conflict. AT!
    // But we never add ∅.
    let mut cnf = Cnf::new();
    let x = cnf.fresh();
    let y = cnf.fresh();
    cnf.clause([x]);
    cnf.clause([!x, y]);
    cnf.clause([!y]);

    let proof = DratProof::new([DratStep::Add(Clause::new([!x]))]);
    assert_both_reject(&cnf, &proof);
}

#[test]
fn add_tautological_clause_then_stop() {
    // Formula: {x} ∧ {~x} — UNSAT.
    // Add {y, ~y} (tautological — always AT since it contains complementary
    // literals), then stop. Since we never derive the empty clause, the proof
    // is rejected despite the tautological clause being accepted.
    //
    // AT check for {y, ~y}: negate y → y=false, negate ~y → y=true.
    // But wait — the AT check assigns ¬(y)=false and ¬(~y)=true, i.e.
    // y=false then y=true. The second assignment sees y is already Sat
    // (from the perspective of the literal ~y whose negation is y=true...
    // let's trace carefully.
    //
    // Actually: negate y → assign y=false. Negate ~y → assign y=true.
    // When we try to negate ~y, we check model.get(~y). Since y=false,
    // ~y evaluates to Sat. So the checker sees the literal ~y is Sat
    // under the current assignment, meaning the clause is trivially a
    // tautology. Returns true immediately.
    let mut cnf = Cnf::new();
    let x = cnf.fresh();
    let y = cnf.fresh();
    cnf.clause([x]);
    cnf.clause([!x]);

    let proof = DratProof::new([DratStep::Add(Clause::new([y, !y]))]);
    assert_both_reject(&cnf, &proof);
}

#[test]
fn add_multiple_non_empty_clauses_then_stop() {
    // Formula: {x, y, z} ∧ {x, y, ~z} ∧ {x, ~y, z} ∧ {x, ~y, ~z}
    //        ∧ {~x, y, z} ∧ {~x, y, ~z} ∧ {~x, ~y, z} ∧ {~x, ~y, ~z}
    // All 8 clauses over 3 variables — UNSAT.
    //
    // Derive intermediate lemmas but never the empty clause.
    let mut cnf = Cnf::new();
    let x = cnf.fresh();
    let y = cnf.fresh();
    let z = cnf.fresh();
    // All 8 possible 3-literal clauses
    for sx in [x, !x] {
        for sy in [y, !y] {
            for sz in [z, !z] {
                cnf.clause([sx, sy, sz]);
            }
        }
    }

    // Add some valid AT lemmas (binary clauses via resolution on z).
    // {x, y}: AT via {x, y, z} and {x, y, ~z} (negate x, negate y → z unit
    //   via {x, y, z} but both x and y are false so clause becomes {z} → z=true,
    //   then {x, y, ~z} has x false, y false, ~z false → conflict).
    //
    // Let's verify {x, y} is AT:
    //   Negate x, negate y → x=false, y=false.
    //   {x, y, z}: x false, y false, z unset → unit z=true.
    //   {x, y, ~z}: x false, y false, ~z false → conflict. AT!
    let proof = DratProof::new([
        DratStep::Add(Clause::new([x, y])),
        DratStep::Add(Clause::new([x, !y])),
        // Could continue to derive {x}, {~x}, then ∅, but we stop here.
    ]);
    assert_both_reject(&cnf, &proof);
}

// -----------------------------------------------------------------------
// Sanity checks: valid proofs that should be accepted by both checkers
// -----------------------------------------------------------------------

#[test]
fn sanity_trivial_unsat_accepted() {
    // {x} ∧ {~x}, proof: Add(∅). Both should accept.
    let mut cnf = Cnf::new();
    let x = cnf.fresh();
    cnf.clause([x]);
    cnf.clause([!x]);

    let proof = DratProof::new([DratStep::Add(Clause::new([]))]);
    assert_both_accept(&cnf, &proof);
}

#[test]
fn sanity_four_clause_full_proof_accepted() {
    // {x,y} ∧ {x,~y} ∧ {~x,y} ∧ {~x,~y}
    // Full valid proof: Add({x}), Add({~x}), Add(∅).
    let mut cnf = Cnf::new();
    let x = cnf.fresh();
    let y = cnf.fresh();
    cnf.clause([x, y]);
    cnf.clause([x, !y]);
    cnf.clause([!x, y]);
    cnf.clause([!x, !y]);

    let proof = DratProof::new([
        DratStep::Add(Clause::new([x])),
        DratStep::Add(Clause::new([!x])),
        DratStep::Add(Clause::new([])),
    ]);
    assert_both_accept(&cnf, &proof);
}

#[test]
fn sanity_proof_with_deletion_accepted() {
    // {x} ∧ {~x}, proof: Add(∅), Delete(∅), Add(∅).
    let mut cnf = Cnf::new();
    let x = cnf.fresh();
    cnf.clause([x]);
    cnf.clause([!x]);

    let proof = DratProof::new([
        DratStep::Add(Clause::new([])),
        DratStep::Delete(Clause::new([])),
        DratStep::Add(Clause::new([])),
    ]);
    assert_both_accept(&cnf, &proof);
}
