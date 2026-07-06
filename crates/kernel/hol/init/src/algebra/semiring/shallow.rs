//! **Shallow** embeddings of the commutative-semiring theory into HOL: a
//! semiring term is the HOL carrier term, a semiring proof is a HOL [`Thm`].
//!
//! Two zero-sized carriers implement [`Semiring`]:
//!
//! - [`Nat`] over HOL `nat` — every axiom a genuine, hypothesis-free
//!   theorem proved by induction in [`crate::init::nat`].
//! - [`Int`] over HOL `int` — the axioms forward to [`crate::init::int`]
//!   (postulated for now; see `SKELETONS.md`). [`Int`] additionally
//!   implements [`Ring`](crate::algebra::ring::Ring).
//!
//! Both reuse the same generic HOL equational core (the private `eqn`
//! helpers): a semiring proof is just a HOL equational `Thm`, and the
//! reasoning rules forward straight to the kernel
//! ([`refl`](Semiring::refl) → `Thm::refl`,
//! [`trans`](Semiring::trans) → `Thm::trans`,
//! [`specialize`](Semiring::specialize) → `Thm::all_elim`,
//! [`cong_add`](Semiring::cong_add) → `cong_arg`/`cong_app`).

use covalence_core::{Error, Result, Term, Type};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::derived::DerivedRules;
use covalence_hol_eval::mk_int;

use crate::algebra::semiring::Semiring;
use crate::init::ext::{TermExt, ThmExt};
use crate::init::{int, nat};

// ============================================================================
// Generic HOL equational core — shared by every carrier
// ============================================================================
//
// A semiring `Prop` is a `bool`-typed HOL equation and a `Proof` is a HOL
// `Thm`; the only carrier-specific inputs are the sort `Type` (for `forall`
// / `generalize`) and the `+` / `·` operator terms (for the congruences).

mod eqn {
    use super::*;

    /// `a = b` as a HOL `bool` term.
    pub fn eq(a: Term, b: Term) -> Term {
        a.equals(b)
            .expect("semiring eq: carrier terms are well-typed")
    }

    /// `∀name:ty. body`.
    pub fn forall(name: &str, ty: Type, body: Term) -> Term {
        body.forall(name, ty)
            .expect("semiring forall: body is bool")
    }

    /// `⊢ op a₁ b₁ = op a₂ b₂` from `⊢ a₁ = a₂` and `⊢ b₁ = b₂`, for a
    /// binary operator term `op` (`+` or `·`).
    pub fn cong_bin(op: Term, a: Thm, b: Thm) -> Result<Thm> {
        a.cong_arg(op)?.cong_app(b)
    }
}

// ============================================================================
// `nat` — a genuine commutative semiring
// ============================================================================

/// Shallow semiring-over-`nat`: `Term = nat` HOL term, `Proof = Thm`.
/// Zero-sized. Every axiom is a hypothesis-free theorem of [`crate::init::nat`].
#[derive(Clone, Copy, Debug, Default)]
pub struct Nat;

impl Nat {
    /// Construct a handle. Free; no allocation.
    pub fn new() -> Self {
        Self
    }
}

impl Semiring for Nat {
    type Term = Term;
    type Prop = Term;
    type Proof = Thm;
    type Error = Error;

    fn var(&self, name: &str) -> Term {
        Term::free(name, Type::nat())
    }
    fn zero(&self) -> Term {
        Term::nat_lit(0u32)
    }
    fn one(&self) -> Term {
        Term::nat_lit(1u32)
    }
    fn add(&self, a: Term, b: Term) -> Term {
        Term::app(Term::app(nat::nat_add(), a), b)
    }
    fn mul(&self, a: Term, b: Term) -> Term {
        Term::app(Term::app(nat::nat_mul(), a), b)
    }

    fn eq(&self, a: Term, b: Term) -> Term {
        eqn::eq(a, b)
    }
    fn forall(&self, name: &str, body: Term) -> Term {
        eqn::forall(name, Type::nat(), body)
    }
    fn concl(&self, proof: &Thm) -> Term {
        proof.concl().clone()
    }

    fn add_comm(&self) -> Thm {
        nat::add_comm()
    }
    fn add_assoc(&self) -> Thm {
        nat::add_assoc()
    }
    fn add_zero(&self) -> Thm {
        nat::add_zero()
    }
    fn mul_comm(&self) -> Thm {
        nat::mul_comm()
    }
    fn mul_assoc(&self) -> Thm {
        nat::mul_assoc()
    }
    fn mul_one(&self) -> Thm {
        nat::mul_one()
    }
    fn mul_zero(&self) -> Thm {
        nat::mul_zero()
    }
    fn distrib(&self) -> Thm {
        nat::distrib()
    }

    fn refl(&self, a: Term) -> Result<Thm> {
        Thm::refl(a)
    }
    fn sym(&self, eq: Thm) -> Result<Thm> {
        eq.sym()
    }
    fn trans(&self, ab: Thm, bc: Thm) -> Result<Thm> {
        ab.trans(bc)
    }
    fn cong_add(&self, a: Thm, b: Thm) -> Result<Thm> {
        eqn::cong_bin(nat::nat_add(), a, b)
    }
    fn cong_mul(&self, a: Thm, b: Thm) -> Result<Thm> {
        eqn::cong_bin(nat::nat_mul(), a, b)
    }
    fn specialize(&self, univ: Thm, witness: Term) -> Result<Thm> {
        univ.all_elim(witness)
    }
    fn generalize(&self, proof: Thm, var: &str) -> Result<Thm> {
        proof.all_intro(var, Type::nat())
    }
}

// ============================================================================
// `int` — a commutative semiring (and, via `crate::algebra::ring`, a ring)
// ============================================================================

/// Shallow semiring-over-`int`: `Term = int` HOL term, `Proof = Thm`.
/// Zero-sized. The axioms forward to [`crate::init::int`] (postulated for
/// now). Also implements [`Ring`](crate::algebra::ring::Ring).
#[derive(Clone, Copy, Debug, Default)]
pub struct Int;

impl Int {
    /// Construct a handle. Free; no allocation.
    pub fn new() -> Self {
        Self
    }
}

impl Semiring for Int {
    type Term = Term;
    type Prop = Term;
    type Proof = Thm;
    type Error = Error;

    fn var(&self, name: &str) -> Term {
        Term::free(name, Type::int())
    }
    fn zero(&self) -> Term {
        mk_int(0)
    }
    fn one(&self) -> Term {
        mk_int(1)
    }
    fn add(&self, a: Term, b: Term) -> Term {
        Term::app(Term::app(int::int_add(), a), b)
    }
    fn mul(&self, a: Term, b: Term) -> Term {
        Term::app(Term::app(int::int_mul(), a), b)
    }

    fn eq(&self, a: Term, b: Term) -> Term {
        eqn::eq(a, b)
    }
    fn forall(&self, name: &str, body: Term) -> Term {
        eqn::forall(name, Type::int(), body)
    }
    fn concl(&self, proof: &Thm) -> Term {
        proof.concl().clone()
    }

    fn add_comm(&self) -> Thm {
        int::add_comm()
    }
    fn add_assoc(&self) -> Thm {
        int::add_assoc()
    }
    fn add_zero(&self) -> Thm {
        int::add_zero()
    }
    fn mul_comm(&self) -> Thm {
        int::mul_comm()
    }
    fn mul_assoc(&self) -> Thm {
        int::mul_assoc()
    }
    fn mul_one(&self) -> Thm {
        int::mul_one()
    }
    fn mul_zero(&self) -> Thm {
        int::mul_zero()
    }
    fn distrib(&self) -> Thm {
        int::distrib()
    }

    fn refl(&self, a: Term) -> Result<Thm> {
        Thm::refl(a)
    }
    fn sym(&self, eq: Thm) -> Result<Thm> {
        eq.sym()
    }
    fn trans(&self, ab: Thm, bc: Thm) -> Result<Thm> {
        ab.trans(bc)
    }
    fn cong_add(&self, a: Thm, b: Thm) -> Result<Thm> {
        eqn::cong_bin(int::int_add(), a, b)
    }
    fn cong_mul(&self, a: Thm, b: Thm) -> Result<Thm> {
        eqn::cong_bin(int::int_mul(), a, b)
    }
    fn specialize(&self, univ: Thm, witness: Term) -> Result<Thm> {
        univ.all_elim(witness)
    }
    fn generalize(&self, proof: Thm, var: &str) -> Result<Thm> {
        proof.all_intro(var, Type::int())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ---- nat ----

    #[test]
    fn nat_axioms_are_genuine_and_rebuild_through_the_prop_layer() {
        let s = Nat::new();
        // add_comm: ∀a b. a + b = b + a
        let (a, b) = (s.var("a"), s.var("b"));
        let add_comm_stmt = s.forall(
            "a",
            s.forall("b", s.eq(s.add(a.clone(), b.clone()), s.add(b, a))),
        );
        assert_eq!(s.concl(&s.add_comm()), add_comm_stmt);

        // distrib: ∀a b c. a · (b + c) = a · b + a · c
        let (a, b, c) = (s.var("a"), s.var("b"), s.var("c"));
        let distrib_body = s.eq(
            s.mul(a.clone(), s.add(b.clone(), c.clone())),
            s.add(s.mul(a.clone(), b.clone()), s.mul(a, c)),
        );
        let distrib_stmt = s.forall("a", s.forall("b", s.forall("c", distrib_body)));
        assert_eq!(s.concl(&s.distrib()), distrib_stmt);

        for ax in [
            s.add_comm(),
            s.add_assoc(),
            s.add_zero(),
            s.mul_comm(),
            s.mul_assoc(),
            s.mul_one(),
            s.mul_zero(),
            s.distrib(),
        ] {
            assert!(ax.hyps().is_empty(), "a nat semiring axiom is genuine");
        }
    }

    #[test]
    fn nat_derives_one_times_one_is_one() {
        // From mul_one: ∀a. a · 1 = 1, specialise a := 1 ⟹ ⊢ 1 · 1 = 1.
        let s = Nat::new();
        let inst = s.specialize(s.mul_one(), s.one()).unwrap();
        assert_eq!(s.concl(&inst), s.eq(s.mul(s.one(), s.one()), s.one()));
        assert!(inst.hyps().is_empty(), "derived from a genuine axiom");
    }

    #[test]
    fn nat_congruence_and_transitivity_compose() {
        // (a + 0) · 1 = a, via cong + axioms.  Build:
        //   add_zero a : ⊢ a + 0 = a
        //   cong_mul (add_zero a) (refl 1) : ⊢ (a+0)·1 = a·1
        //   trans with mul_one a : ⊢ (a+0)·1 = a
        let s = Nat::new();
        let a = s.var("a");
        let az = s.specialize(s.add_zero(), a.clone()).unwrap(); // a + 0 = a
        let one_refl = s.refl(s.one()).unwrap();
        let cm = s.cong_mul(az, one_refl).unwrap(); // (a+0)·1 = a·1
        let mo = s.specialize(s.mul_one(), a.clone()).unwrap(); // a·1 = a
        let proved = s.trans(cm, mo).unwrap(); // (a+0)·1 = a
        let lhs = s.mul(s.add(a.clone(), s.zero()), s.one());
        assert_eq!(s.concl(&proved), s.eq(lhs, a));
        assert!(proved.hyps().is_empty());
    }

    // ---- int ----

    #[test]
    fn int_axioms_rebuild_through_the_prop_layer() {
        let s = Int::new();
        // mul_comm: ∀a b. a · b = b · a
        let (a, b) = (s.var("a"), s.var("b"));
        let mul_comm_stmt = s.forall(
            "a",
            s.forall("b", s.eq(s.mul(a.clone(), b.clone()), s.mul(b, a))),
        );
        assert_eq!(s.concl(&s.mul_comm()), mul_comm_stmt);

        // The full commutative ring is now discharged in `init::int`, so the
        // semiring axioms are genuine theorems — hypothesis-free.
        for ax in [s.mul_one(), s.distrib(), s.mul_comm()] {
            assert!(
                ax.hyps().is_empty(),
                "the int semiring axioms are now proved (hypothesis-free)"
            );
        }
    }

    #[test]
    fn int_specialises_add_comm_to_literals() {
        // ∀a b. a + b = b + a  ⟹  (3 + 5) = (5 + 3).
        let s = Int::new();
        let p = s
            .specialize(s.add_comm(), mk_int(3))
            .and_then(|t| s.specialize(t, mk_int(5)))
            .unwrap();
        let expected = s.eq(s.add(mk_int(3), mk_int(5)), s.add(mk_int(5), mk_int(3)));
        assert_eq!(s.concl(&p), expected);
    }

    /// A *generic* semiring routine — proves `⊢ 1 · 1 = 1` against any
    /// carrier — runs against both `Nat` and `Int`.
    fn one_squared_is_one<S: Semiring>(s: &S) -> S::Proof
    where
        S::Error: std::fmt::Debug,
    {
        s.specialize(s.mul_one(), s.one())
            .expect("specialize mul_one")
    }

    #[test]
    fn generic_routine_runs_against_both_carriers() {
        let n = Nat::new();
        let i = Int::new();
        let pn = one_squared_is_one(&n);
        let pi = one_squared_is_one(&i);
        assert_eq!(n.concl(&pn), n.eq(n.mul(n.one(), n.one()), n.one()));
        assert_eq!(i.concl(&pi), i.eq(i.mul(i.one(), i.one()), i.one()));
    }
}
