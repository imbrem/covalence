//! End-to-end K demo: load a `.k` definition from source, reduce programs in it,
//! and check the resulting `⊢ Reduces` theorems are hypothesis-free. The
//! medium-term north star made concrete (`notes/vibes/k/reduction-demo-scope.md`).

use covalence_hol_eval::EvalThm as Thm;
use covalence_init::k::session::KSession;

const PEANO: &str = include_str!("../../../../lang/k/examples/k-demo/peano.k");
const COLORS: &str = include_str!("../../../../lang/k/examples/k-demo/colors.k");
const BOOLSIMP: &str = include_str!("../../../../lang/k/examples/k-demo/boolsimp.k");

fn assert_genuine(thm: &Thm) {
    assert!(
        thm.hyps().is_empty(),
        "reduction theorem must be hypothesis-free"
    );
}

#[test]
fn peano_arithmetic_reduces() {
    let k = KSession::from_source(PEANO).unwrap();
    assert_eq!(k.report().lowered, 4);

    // 2 + 1 = 3
    let r = k.reduce("plus(s(s(z())), s(z()))").unwrap();
    assert!(r.complete);
    assert_eq!(r.rendered, "s(s(s(z)))");
    assert_genuine(&r.thm);
    // ⊢ Reduces ⌜plus(s(s(z)), s(z))⌝ ⌜s(s(s(z)))⌝ — the theorem is about the
    // encoded start and the normal form.
    assert_eq!(
        r.thm.concl(),
        &k.reduce_term(&k.parse_program("plus(s(s(z())), s(z()))").unwrap(), 10_000)
            .unwrap()
            .thm
            .concl()
            .clone()
    );

    // 2 * 3 = 6
    let r = k.reduce("mult(s(s(z())), s(s(s(z()))))").unwrap();
    assert_eq!(r.rendered, "s(s(s(s(s(s(z))))))");
    assert_genuine(&r.thm);
}

#[test]
fn k_tutorial_lesson_1_2_reduces() {
    let k = KSession::from_source(COLORS).unwrap();
    assert_eq!(k.reduce("colorOf(Banana())").unwrap().rendered, "Yellow");
    assert_eq!(k.reduce("colorOf(Blueberry())").unwrap().rendered, "Blue");
    // variable binding: contentsOfJar(Jar(X)) => X
    assert_eq!(
        k.reduce("contentsOfJar(Jar(Grape()))").unwrap().rendered,
        "Grape"
    );
    assert_genuine(&k.reduce("colorOf(Banana())").unwrap().thm);
}

#[test]
fn boolean_simplification_reduces() {
    let k = KSession::from_source(BOOLSIMP).unwrap();
    // and(or(tt, ff), neg(ff)) →* tt
    let r = k.reduce("and(or(tt(), ff()), neg(ff()))").unwrap();
    assert_eq!(r.rendered, "tt");
    assert_genuine(&r.thm);
    // A deeper nesting still normalizes.
    let r = k
        .reduce("neg(and(or(ff(), tt()), neg(neg(ff()))))")
        .unwrap();
    assert_eq!(r.rendered, "tt");
}
