//! **Using Metamath-style proofs from outside Metamath.**
//!
//! A self-contained tour of [`covalence_init::metalogic::DbSession`]: reify a
//! small Metamath-style database of propositional axioms as a HOL value, then
//! *compose* its rules in the HOL kernel to derive a theorem the database never
//! states — the composite's Metamath derivation is never written down, yet its
//! existence is certified as a genuine `⊢ Derivable_DB db ⌜S⌝` HOL theorem.
//!
//! (The `Derivable_DB` conclusions are large impredicative terms — `∀d.
//! Closed_DB db d ⟹ d ⌜S⌝` — so we print compact symbolic labels for the
//! formulas rather than the raw kernel terms. Each `⊢` line below is a real,
//! hypothesis-free HOL theorem.)
//!
//! Run it:
//! ```sh
//! cargo run -p covalence-init --example mm_compose
//! ```

use covalence_init::metalogic::DbSession;

fn main() {
    // A tiny "database": the axioms  p0,  p0 ⟹ p1,  p1 ⟹ p2.
    // (`var k` is a reified propositional atom; `imp` the encoded implication.)
    let p0 = DbSession::var(0);
    let p1 = DbSession::var(1);
    let p2 = DbSession::var(2);
    let imp01 = DbSession::imp(&p0, &p1);
    let imp12 = DbSession::imp(&p1, &p2);

    let sess = DbSession::new(vec![p0.clone(), imp01.clone(), imp12.clone()])
        .expect("non-empty axiom set");

    println!("database db (a Metamath-style propositional theory), axioms:");
    println!("  a0 = ⌜p0⌝");
    println!("  a1 = ⌜p0 ⟹ p1⌝");
    println!("  a2 = ⌜p1 ⟹ p2⌝\n");

    // Introduce the axioms as derivability theorems: ⊢ Derivable_DB db ⌜aᵢ⌝.
    let d_p0 = sess.axiom(&p0).expect("p0 is an axiom");
    let d_imp01 = sess.axiom(&imp01).expect("p0⟹p1 is an axiom");
    let d_imp12 = sess.axiom(&imp12).expect("p1⟹p2 is an axiom");
    println!("axiom introduction (genuine hypothesis-free kernel theorems):");
    println!("  ⊢ Derivable_DB db ⌜p0⌝");
    println!("  ⊢ Derivable_DB db ⌜p0 ⟹ p1⌝");
    println!("  ⊢ Derivable_DB db ⌜p1 ⟹ p2⌝\n");

    // Compose by modus ponens — INSIDE the HOL kernel, OUTSIDE Metamath.
    //   p0, p0⟹p1  ⊢  p1
    let d_p1 = sess
        .mp(&p0, &p1, &d_p0, &d_imp01)
        .expect("MP: p0, p0⟹p1 ⊢ p1");
    //   p1, p1⟹p2  ⊢  p2
    let d_p2 = sess
        .mp(&p1, &p2, &d_p1, &d_imp12)
        .expect("MP: p1, p1⟹p2 ⊢ p2");

    println!("composed by modus ponens (no Metamath proof of these was written):");
    println!("  ⊢ Derivable_DB db ⌜p1⌝     (from a0, a1)");
    println!("  ⊢ Derivable_DB db ⌜p2⌝     (from that, a2)\n");

    // The composites are hypothesis-free and `p2` is NOT an axiom of db — its
    // derivability is a *derived* fact, certified without materialising a proof.
    assert!(d_p0.hyps().is_empty() && d_p1.hyps().is_empty() && d_p2.hyps().is_empty());
    assert_eq!(d_p2.concl(), &sess.derivable(&p2).unwrap());
    assert!(
        sess.axiom(&p2).is_err(),
        "p2 is not an axiom — it was DERIVED"
    );

    // Cross-check: the raw conclusion really is the `∀d. Closed_DB db d ⟹ d ⌜p2⌝`
    // term (printed truncated so the point isn't buried).
    let concl = format!("{}", d_p2.concl());
    println!(
        "raw ⊢ conclusion is a {}-char impredicative term beginning:\n  {}…\n",
        concl.len(),
        &concl[..concl.len().min(78)],
    );

    println!("✓ ⊢ Derivable_DB db ⌜p2⌝ holds, yet p2 is not an axiom of db.");
    println!("  The Metamath derivation of p2 exists but was never constructed.");
}
