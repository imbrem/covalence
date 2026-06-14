//! `int` theorems: the `defs/int.rs` catalogue re-exported, plus the
//! **postulated** ordered-commutative-ring (with discreteness) theory of
//! HOL `int` — mirroring how [`init::nat`] pairs the `nat` definitions
//! with their Peano facts.
//!
//! [`init::nat`]: crate::init::nat
//!
//! ## Status — all postulated
//!
//! Every theorem here is a `Thm::assume` **postulate** (flagged in
//! `SKELETONS.md`), carrying its statement as a self-hypothesis so the
//! audit trail is visible in any downstream theorem. They are the
//! ingredients an integer-linear-arithmetic certificate checker (the
//! Alethe `la_generic` / `la_mult_*` family) needs:
//!
//! - **Commutative ring** — [`add_comm`], [`add_assoc`], [`add_zero`],
//!   [`add_neg`], [`mul_comm`], [`mul_assoc`], [`mul_one`], [`mul_zero`],
//!   [`distrib`], [`sub_def`].
//! - **Linear order** — [`lt_irrefl`], [`lt_trans`], [`lt_trichotomy`],
//!   [`le_def`].
//! - **Ordered-ring compatibility** — [`lt_add_mono`], [`lt_mul_pos`].
//! - **Discreteness** (the integer-specific axiom) — [`lt_succ`]:
//!   `a < b ⟺ a + 1 ≤ b`.
//!
//! `int := (nat × nat) / ~` is the Grothendieck construction, so each of
//! these is a *theorem* of HOL, derivable from the `nat` Peano facts in
//! [`init::nat`] through the quotient. Discharging them is downstream
//! work; until then they are the `int` postulate set. The public surface
//! (these `fn`s) does not change when the proofs land — only the bodies.
//!
//! ## What the proofs are waiting on
//!
//! Two ingredients. The **`nat` side** is in place: [`init::nat`] proves
//! the additive theory (`add_comm`/`add_assoc`/`add_zero`/…) by induction,
//! and the order/multiplicative facts will follow the same way. The
//! **quotient side** is now started in [`init::quotient`](crate::init::quotient):
//! `int` is a subtype of the powerset, so the kernel's subtype laws apply,
//! and `quotient::class_intro` gives the forward lifting law
//! `rel a b → mkInt a = mkInt b` — enough to *prove `int` equations* (most
//! of the ring axioms). The converse and the `int_rel`-is-an-equivalence
//! prerequisite are tracked in `SKELETONS.md`. Each postulate here will
//! unfold the relevant `int` op to its representative-pair body, lift the
//! `nat` fact through `class_intro`, and re-quotient.

use covalence_core::{Term, Thm, Type};

use crate::init::ext::TermExt;

// Re-export the `defs/int.rs` term catalogue (the operations; the
// `*_spec` handles stay in `covalence_core::defs`).
pub use covalence_core::defs::{
    int_abs, int_add, int_div, int_le, int_lt, int_mod, int_mul, int_neg, int_pred, int_sgn,
    int_sub, int_succ, int_zero,
};

// ============================================================================
// Small term helpers (private — the public surface is theorems)
// ============================================================================

fn int() -> Type {
    Type::int()
}

fn lit(n: i128) -> Term {
    Term::int_lit(n)
}

fn var(name: &str) -> Term {
    Term::free(name, int())
}

fn add(a: Term, b: Term) -> Term {
    Term::app(Term::app(int_add(), a), b)
}

fn mul(a: Term, b: Term) -> Term {
    Term::app(Term::app(int_mul(), a), b)
}

fn neg(a: Term) -> Term {
    Term::app(int_neg(), a)
}

fn lt(a: Term, b: Term) -> Term {
    Term::app(Term::app(int_lt(), a), b)
}

fn le(a: Term, b: Term) -> Term {
    Term::app(Term::app(int_le(), a), b)
}

/// Postulate an `int` axiom: `{t} ⊢ t`. The self-hypothesis is the audit
/// trail — every proof built on it carries it, flagging the unproved leaf
/// until the quotient derivation discharges it.
fn axiom(t: Term) -> Thm {
    Thm::assume(t).expect("init::int::axiom: term must be bool-typed")
}

/// Universally close `body` over the named `int` variables, **outermost
/// first** (so `forall_int(&["a", "b"], body)` is `∀a b. body`).
fn forall_int(vars: &[&str], body: Term) -> Term {
    let mut t = body;
    for name in vars.iter().rev() {
        t = t.forall(name, int()).expect("forall_int: bind variable");
    }
    t
}

// ============================================================================
// Commutative ring
// ============================================================================

/// `⊢ ∀a b. a + b = b + a`.
pub fn add_comm() -> Thm {
    let (a, b) = (var("a"), var("b"));
    let eq = add(a.clone(), b.clone())
        .equals(add(b, a))
        .expect("add_comm: a + b = b + a");
    axiom(forall_int(&["a", "b"], eq))
}

/// `⊢ ∀a b c. (a + b) + c = a + (b + c)`.
pub fn add_assoc() -> Thm {
    let (a, b, c) = (var("a"), var("b"), var("c"));
    let lhs = add(add(a.clone(), b.clone()), c.clone());
    let rhs = add(a, add(b, c));
    let eq = lhs.equals(rhs).expect("add_assoc");
    axiom(forall_int(&["a", "b", "c"], eq))
}

/// `⊢ ∀a. a + 0 = a`.
pub fn add_zero() -> Thm {
    let a = var("a");
    let eq = add(a.clone(), lit(0)).equals(a).expect("add_zero: a + 0 = a");
    axiom(forall_int(&["a"], eq))
}

/// `⊢ ∀a. a + (-a) = 0` — additive inverse.
pub fn add_neg() -> Thm {
    let a = var("a");
    let eq = add(a.clone(), neg(a))
        .equals(lit(0))
        .expect("add_neg: a + (-a) = 0");
    axiom(forall_int(&["a"], eq))
}

/// `⊢ ∀a b. a * b = b * a`.
pub fn mul_comm() -> Thm {
    let (a, b) = (var("a"), var("b"));
    let eq = mul(a.clone(), b.clone())
        .equals(mul(b, a))
        .expect("mul_comm");
    axiom(forall_int(&["a", "b"], eq))
}

/// `⊢ ∀a b c. (a * b) * c = a * (b * c)`.
pub fn mul_assoc() -> Thm {
    let (a, b, c) = (var("a"), var("b"), var("c"));
    let lhs = mul(mul(a.clone(), b.clone()), c.clone());
    let rhs = mul(a, mul(b, c));
    let eq = lhs.equals(rhs).expect("mul_assoc");
    axiom(forall_int(&["a", "b", "c"], eq))
}

/// `⊢ ∀a. a * 1 = a`.
pub fn mul_one() -> Thm {
    let a = var("a");
    let eq = mul(a.clone(), lit(1)).equals(a).expect("mul_one: a * 1 = a");
    axiom(forall_int(&["a"], eq))
}

/// `⊢ ∀a. a * 0 = 0`.
pub fn mul_zero() -> Thm {
    let a = var("a");
    let eq = mul(a, lit(0)).equals(lit(0)).expect("mul_zero: a * 0 = 0");
    axiom(forall_int(&["a"], eq))
}

/// `⊢ ∀a b c. a * (b + c) = a * b + a * c` — left distributivity.
pub fn distrib() -> Thm {
    let (a, b, c) = (var("a"), var("b"), var("c"));
    let lhs = mul(a.clone(), add(b.clone(), c.clone()));
    let rhs = add(mul(a.clone(), b), mul(a, c));
    let eq = lhs.equals(rhs).expect("distrib");
    axiom(forall_int(&["a", "b", "c"], eq))
}

/// `⊢ ∀a b. a - b = a + (-b)` — subtraction by negation.
pub fn sub_def() -> Thm {
    let (a, b) = (var("a"), var("b"));
    let sub = Term::app(Term::app(int_sub(), a.clone()), b.clone());
    let eq = sub.equals(add(a, neg(b))).expect("sub_def: a - b = a + (-b)");
    axiom(forall_int(&["a", "b"], eq))
}

// ============================================================================
// Linear order
// ============================================================================

/// `⊢ ∀a. ¬(a < a)` — irreflexivity.
pub fn lt_irrefl() -> Thm {
    let a = var("a");
    let body = lt(a.clone(), a).not().expect("lt_irrefl: ¬(a < a)");
    axiom(forall_int(&["a"], body))
}

/// `⊢ ∀a b c. a < b ⟹ b < c ⟹ a < c` — transitivity.
pub fn lt_trans() -> Thm {
    let (a, b, c) = (var("a"), var("b"), var("c"));
    let inner = lt(b.clone(), c.clone())
        .imp(lt(a.clone(), c))
        .expect("lt_trans inner");
    let body = lt(a, b).imp(inner).expect("lt_trans");
    axiom(forall_int(&["a", "b", "c"], body))
}

/// `⊢ ∀a b. a < b ∨ a = b ∨ b < a` — trichotomy (totality).
pub fn lt_trichotomy() -> Thm {
    let (a, b) = (var("a"), var("b"));
    let eq = a.clone().equals(b.clone()).expect("trichotomy: a = b");
    let tail = eq.or(lt(b.clone(), a.clone())).expect("trichotomy tail");
    let body = lt(a, b).or(tail).expect("trichotomy");
    axiom(forall_int(&["a", "b"], body))
}

/// `⊢ ∀a b. (a ≤ b) = (a < b ∨ a = b)` — `≤` in terms of `<`.
pub fn le_def() -> Thm {
    let (a, b) = (var("a"), var("b"));
    let rhs = lt(a.clone(), b.clone())
        .or(a.clone().equals(b.clone()).expect("le_def: a = b"))
        .expect("le_def rhs");
    let eq = le(a, b).equals(rhs).expect("le_def");
    axiom(forall_int(&["a", "b"], eq))
}

// ============================================================================
// Ordered-ring compatibility
// ============================================================================

/// `⊢ ∀a b c. a < b ⟹ a + c < b + c` — translation invariance of `<`.
pub fn lt_add_mono() -> Thm {
    let (a, b, c) = (var("a"), var("b"), var("c"));
    let concl = lt(add(a.clone(), c.clone()), add(b.clone(), c));
    let body = lt(a, b).imp(concl).expect("lt_add_mono");
    axiom(forall_int(&["a", "b", "c"], body))
}

/// `⊢ ∀a b c. 0 < c ⟹ a < b ⟹ a * c < b * c` — `<` preserved by a
/// positive multiplier.
pub fn lt_mul_pos() -> Thm {
    let (a, b, c) = (var("a"), var("b"), var("c"));
    let concl = lt(mul(a.clone(), c.clone()), mul(b.clone(), c.clone()));
    let inner = lt(a, b).imp(concl).expect("lt_mul_pos inner");
    let body = lt(lit(0), c).imp(inner).expect("lt_mul_pos");
    axiom(forall_int(&["a", "b", "c"], body))
}

// ============================================================================
// Discreteness — the integer-specific axiom
// ============================================================================

/// `⊢ ∀a b. (a < b) = (a + 1 ≤ b)` — the integers are discrete: strict
/// `<` is `+1`-shifted `≤`. The key fact the integer-specific Alethe
/// `la` rules (rounding rational bounds to integer ones) rest on.
pub fn lt_succ() -> Thm {
    let (a, b) = (var("a"), var("b"));
    let eq = lt(a.clone(), b.clone())
        .equals(le(add(a, lit(1)), b))
        .expect("lt_succ: (a < b) = (a + 1 ≤ b)");
    axiom(forall_int(&["a", "b"], eq))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The full postulate set — used to assert the audit-trail invariant.
    fn all() -> Vec<Thm> {
        vec![
            add_comm(),
            add_assoc(),
            add_zero(),
            add_neg(),
            mul_comm(),
            mul_assoc(),
            mul_one(),
            mul_zero(),
            distrib(),
            sub_def(),
            lt_irrefl(),
            lt_trans(),
            lt_trichotomy(),
            le_def(),
            lt_add_mono(),
            lt_mul_pos(),
            lt_succ(),
        ]
    }

    #[test]
    fn postulates_are_well_typed_and_self_flagged() {
        for ax in all() {
            assert!(
                ax.concl().type_of().unwrap().is_bool(),
                "an int postulate is a bool statement"
            );
            assert!(
                ax.hyps().iter().any(|h| h == ax.concl()),
                "a postulated axiom carries itself as a hypothesis"
            );
        }
    }

    #[test]
    fn add_comm_specialises() {
        // ∀a b. a + b = b + a  ⟹  (1 + 2) = (2 + 1).
        let inst = add_comm()
            .all_elim(lit(1))
            .and_then(|t| t.all_elim(lit(2)))
            .expect("specialize add_comm");
        let expected = add(lit(1), lit(2)).equals(add(lit(2), lit(1))).unwrap();
        assert_eq!(inst.concl(), &expected);
    }

    #[test]
    fn le_def_is_an_equation_at_bool() {
        let thm = le_def();
        // ∀-stripped twice, the body is a bool equation.
        let inst = thm
            .all_elim(lit(0))
            .and_then(|t| t.all_elim(lit(1)))
            .unwrap();
        assert!(inst.concl().as_eq().is_some(), "le_def body is `(≤) = (…)`");
    }
}
