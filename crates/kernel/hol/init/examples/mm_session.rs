//! **Composing real imported Metamath theorems in HOL.**
//!
//! A self-contained tour of [`covalence_init::metalogic::MmSession`]: parse a
//! small propositional-calculus Metamath database (wff former `wi`, axioms
//! `ax-1`/`ax-2`, inference rule `ax-mp`, and one stored `$p` theorem), then
//!
//! 1. re-derive two stored theorems into genuine `⊢ Derivable_L ⌜S⌝` HOL theorems
//!    (`theorem`, via a verified, kernel-re-checked replay — the Metamath
//!    verifier's say-so is *not* trusted), and
//! 2. **compose a statement the database has no `$p` proof for** by applying its
//!    `ax-mp` rule in the HOL kernel (`apply`/`mp`) — the composite's Metamath
//!    derivation is never written down, yet its existence is certified in HOL.
//!
//! (The `Derivable_L` conclusions are huge impredicative terms — `∀d. Closed_L d
//! ⟹ d ⌜S⌝` over the whole database's rule set — so we print short descriptions
//! and *assert* each theorem is hypothesis-free rather than dumping the term.)
//!
//! Run it:
//! ```sh
//! cargo run -p covalence-init --example mm_session
//! ```

use covalence_init::metalogic::MmSession;
use covalence_init::metamath;

/// A minimal propositional-calculus database with two stored `$p` theorems
/// (`a1i`, `a2i` — the same shape, distinct labels) so we can show two
/// derivations sharing one `Derivable_L` head.
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
    ${
      a1i.1 $e |- ph $.
      a1i $p |- ( ps -> ph ) $=
        wph  wps wph wi  a1i.1  wph wps ax-1  ax-mp $.
    $}
    ${
      a2i.1 $e |- ph $.
      a2i $p |- ( ps -> ph ) $=
        wph  wps wph wi  a2i.1  wph wps ax-1  ax-mp $.
    $}
";

/// Build a `wff`-typecoded Metamath expression from its body tokens.
fn wff(body: &str) -> metamath::Expr {
    metamath::expr::from_symbols(std::iter::once("wff").chain(body.split_whitespace()))
        .expect("non-empty wff")
}
/// Build a `|-`-typecoded Metamath expression from its body tokens.
fn prov(body: &str) -> metamath::Expr {
    metamath::expr::from_symbols(std::iter::once("|-").chain(body.split_whitespace()))
        .expect("non-empty |-")
}

fn main() {
    let db = metamath::parse(PROP).expect("PROP database parses");
    // The Metamath verifier accepts both stored `$p` proofs (untrusted input).
    let verified = metamath::verify_all(&db).expect("verify");
    println!("parsed a propositional-calculus database: {verified} verified $p theorem(s)\n");

    let sess = MmSession::new(db).expect("build session");

    // (1) Re-derive two stored theorems — genuine, kernel-re-checked replays.
    let a1i = sess.theorem("a1i").expect("replay a1i");
    let a2i = sess.theorem("a2i").expect("replay a2i");
    println!("re-derived stored $p theorems (verified replays, verifier NOT trusted):");
    println!("  a1i : ⊢ Derivable_L ⌜( ps -> ph )⌝   (1 hypothesis: Derivable_L ⌜ph⌝)");
    println!("  a2i : ⊢ Derivable_L ⌜( ps -> ph )⌝   (1 hypothesis: Derivable_L ⌜ph⌝)");
    assert_eq!(a1i.hyps().len(), 1);
    assert_eq!(a2i.hyps().len(), 1);
    // Both derivations share the SAME `Derivable_L` head (same rule set), so their
    // conclusions are structurally identical.
    assert_eq!(a1i.concl(), a2i.concl(), "one shared Derivable_L head");
    println!("  ✓ both share ONE `Derivable_L` head (they compose directly)\n");

    // (2) Compose a statement the database has NO `$p` proof for, by applying the
    // database's own `ax-1` axiom schema and `ax-mp` rule in the HOL kernel.

    // ax-1 instance @ (ph := ( ph -> ph ), ps := ph):
    //   ⊢ Derivable_L ⌜( ( ph -> ph ) -> ( ph -> ( ph -> ph ) ) )⌝
    let php = sess.encode(&wff("( ph -> ph )")).unwrap();
    let ph = sess.encode(&wff("ph")).unwrap();
    let ax1 = sess.apply("ax-1", &[php, ph], &[]).expect("apply ax-1");
    assert!(ax1.hyps().is_empty(), "ax-1 instance is hypothesis-free");
    println!("applied the ax-1 schema (a statement the db has no $p for):");
    println!("  ⊢ Derivable_L ⌜( ( ph -> ph ) -> ( ph -> ( ph -> ph ) ) )⌝   (hypothesis-free)\n");

    // Assume the major premise `Der ⌜( ph -> ph )⌝`, then MP it against the ax-1
    // implication to compose `Der ⌜( ph -> ( ph -> ph ) )⌝`.
    let a_enc = sess.encode(&prov("( ph -> ph )")).unwrap();
    let major = covalence_init::metalogic::derivable(sess.rule_set(), &a_enc)
        .and_then(covalence_hol_eval::EvalThm::assume)
        .expect("assume major");
    let mp_ph = sess.encode(&wff("( ph -> ph )")).unwrap();
    let mp_ps = sess.encode(&wff("( ph -> ( ph -> ph ) )")).unwrap();
    let composed = sess
        .mp(None, &[mp_ph, mp_ps], &major, &ax1)
        .expect("compose by ax-mp");
    println!("composed by ax-mp (INSIDE HOL, OUTSIDE Metamath — no $p was written):");
    println!("  ⊢ Derivable_L ⌜( ph -> ( ph -> ph ) )⌝   (1 hypothesis: the assumed major)\n");
    assert_eq!(
        composed.hyps().len(),
        1,
        "carries the assumed major premise"
    );

    // The composite is a genuine kernel theorem; its raw conclusion is a large
    // impredicative term we deliberately do not dump.
    let concl_len = format!("{}", composed.concl()).len();
    println!(
        "✓ composed a Derivable_L theorem the database never proves; its raw conclusion is a\n  \
         {concl_len}-character impredicative term (`∀d. Closed_L d ⟹ d ⌜…⌝`), not printed."
    );
}
