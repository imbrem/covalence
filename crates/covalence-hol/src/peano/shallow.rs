//! The **shallow** embedding of Peano arithmetic into HOL: a PA term is
//! the HOL `nat` term, a PA proof is a HOL [`Thm`] about `nat`.
//!
//! [`Hol`] is the trivial implementation of [`Peano`] — "trivial"
//! because PA reasoning is *just* HOL reasoning over `nat`: a PA term is
//! a `nat` term, a PA formula is a `bool`-typed term built from the HOL
//! connectives, and a PA proof is a HOL [`Thm`]. The axioms are the
//! proved theorems in [`crate::init::nat`]; the inference rules forward
//! straight to the kernel ([`induct`](Peano::induct) → `Thm::nat_induct`,
//! [`specialize`](Peano::specialize) → `Thm::all_elim`,
//! [`mp`](Peano::mp) → `Thm::imp_elim`).
//!
//! Every PA axiom is a genuine, hypothesis-free HOL theorem (the four
//! `add`/`mul` recursion equations discharged by the recursion theorem
//! in [`crate::init::recursion`]), so a shallow PA proof is an outright
//! HOL theorem.

use covalence_core::{Error, Result, Term, Thm, Type, defs, subst};
use covalence_types::Nat;

use crate::HolLightCtx;
use crate::init::nat;
use crate::peano::Peano;

/// Shallow PA-in-HOL: `Term = nat` HOL term, `Proof = Thm`. Zero-sized.
#[derive(Clone, Copy, Debug, Default)]
pub struct Hol;

impl Hol {
    /// Construct a handle. Free; no allocation.
    pub fn new() -> Self {
        Self
    }
}

impl Peano for Hol {
    // Both a PA term and a PA formula are just HOL `Term`s (a formula is
    // a `bool`-typed one); a PA proof is a HOL `Thm`.
    type Term = Term;
    type Prop = Term;
    type Proof = Thm;
    type Error = Error;

    // ---- expression theory: term constructors ----

    fn var(&self, name: &str) -> Term {
        Term::free(name, Type::nat())
    }

    fn zero(&self) -> Term {
        Term::nat_lit(Nat::zero())
    }

    fn succ(&self, n: Term) -> Term {
        Term::app(defs::nat_succ(), n)
    }

    fn add(&self, a: Term, b: Term) -> Term {
        Term::app(Term::app(defs::nat_add(), a), b)
    }

    fn mul(&self, a: Term, b: Term) -> Term {
        Term::app(Term::app(defs::nat_mul(), a), b)
    }

    // ---- first-order logic: formula constructors (HOL connectives) ----

    fn eq(&self, a: Term, b: Term) -> Term {
        HolLightCtx::new().mk_eq(a, b).expect("eq: nat terms are well-typed")
    }
    fn not(&self, p: Term) -> Term {
        HolLightCtx::new().mk_not(p)
    }
    fn and(&self, p: Term, q: Term) -> Term {
        HolLightCtx::new().mk_and(p, q)
    }
    fn or(&self, p: Term, q: Term) -> Term {
        HolLightCtx::new().mk_or(p, q)
    }
    fn implies(&self, p: Term, q: Term) -> Term {
        HolLightCtx::new().mk_imp(p, q)
    }
    fn iff(&self, p: Term, q: Term) -> Term {
        HolLightCtx::new().mk_iff(p, q)
    }
    fn forall(&self, name: &str, body: Term) -> Term {
        HolLightCtx::new().mk_forall(name, Type::nat(), body)
    }
    fn exists(&self, name: &str, body: Term) -> Term {
        HolLightCtx::new().mk_exists(name, Type::nat(), body)
    }
    fn falsum(&self) -> Term {
        Term::bool_lit(false)
    }
    fn verum(&self) -> Term {
        Term::bool_lit(true)
    }

    fn concl(&self, proof: &Thm) -> Term {
        proof.concl().clone()
    }

    // ---- axioms (the proved theorems in `init::nat`) ----

    fn zero_ne_succ(&self) -> Thm {
        nat::zero_ne_succ()
    }
    fn succ_inj(&self) -> Thm {
        nat::succ_inj()
    }
    fn add_base(&self) -> Thm {
        nat::add_base()
    }
    fn add_step(&self) -> Thm {
        nat::add_step()
    }
    fn mul_base(&self) -> Thm {
        nat::mul_base()
    }
    fn mul_step(&self) -> Thm {
        nat::mul_step()
    }

    // ---- FOL rules: structural / classical (kernel forwarding) ----

    fn assume(&self, p: Term) -> Result<Thm> {
        Thm::assume(p)
    }

    fn refl(&self, a: Term) -> Result<Thm> {
        Thm::refl(a)
    }

    fn lem(&self, p: Term) -> Result<Thm> {
        Thm::lem(p)
    }

    // ---- FOL rules: connective intro / elim (kernel forwarding) ----

    fn implies_intro(&self, hyp: Term, proof: Thm) -> Result<Thm> {
        proof.imp_intro(&hyp)
    }

    fn mp(&self, implication: Thm, antecedent: Thm) -> Result<Thm> {
        implication.imp_elim(antecedent)
    }

    fn and_intro(&self, p: Thm, q: Thm) -> Result<Thm> {
        p.and_intro(q)
    }
    fn and_left(&self, conj: Thm) -> Result<Thm> {
        conj.and_elim_l()
    }
    fn and_right(&self, conj: Thm) -> Result<Thm> {
        conj.and_elim_r()
    }

    fn or_intro_left(&self, p: Thm, q: Term) -> Result<Thm> {
        p.or_intro_l(q)
    }
    fn or_intro_right(&self, p: Term, q: Thm) -> Result<Thm> {
        q.or_intro_r(p)
    }
    fn or_elim(&self, disj: Thm, left: Thm, right: Thm) -> Result<Thm> {
        disj.or_elim(left, right)
    }

    fn not_intro(&self, p_implies_false: Thm) -> Result<Thm> {
        p_implies_false.not_intro()
    }
    fn not_elim(&self, not_p: Thm, p: Thm) -> Result<Thm> {
        not_p.not_elim(p)
    }
    fn absurd(&self, falsity: Thm, p: Term) -> Result<Thm> {
        falsity.false_elim(p)
    }

    // ---- FOL rules: quantifier intro / elim ----

    fn generalize(&self, proof: Thm, var: &str) -> Result<Thm> {
        proof.all_intro(var, Type::nat())
    }

    fn specialize(&self, univ: Thm, witness: Term) -> Result<Thm> {
        univ.all_elim(witness)
    }

    fn exists_intro(&self, var: &str, body: Term, witness: Term, proof: Thm) -> Result<Thm> {
        // `init::logic::exists_intro` wants the predicate `λvar. body`
        // and a proof of `pred witness` (applied, *not* β-reduced).
        // The caller's `proof` proves the β-reduced `body[witness/var]`,
        // so β-expand it back to `⊢ pred witness` first.
        let pred = Term::abs(Type::nat(), subst::close(&body, var));
        let applied = Term::app(pred.clone(), witness.clone());
        let bridged = Thm::beta_conv(applied)?.sym()?.eq_mp(proof)?;
        crate::init::logic::exists_intro(pred, witness, bridged)
    }

    fn exists_elim(&self, ex: Thm, c: Term, step: Thm) -> Result<Thm> {
        // `init::logic::exists_elim` wants the step in the *applied*
        // form `⊢ ∀x. (pred x) ⟹ c`, but the caller naturally builds the
        // β-reduced `⊢ ∀x. body ⟹ c`. Bridge the one β step: strip the
        // ∀, rewrite the antecedent `body[x]` to `pred x` by congruence,
        // and re-generalise.
        let pred = ex
            .concl()
            .as_app()
            .ok_or_else(|| Error::ConnectiveRule("exists_elim: conclusion is not ∃".into()))?
            .1
            .clone();
        let xname = "__ee_x";
        let xv = Term::free(xname, Type::nat());
        let inst = step.all_elim(xv.clone())?; // ⊢ body[x] ⟹ c
        let beta = Thm::beta_conv(Term::app(pred, xv))?; // ⊢ pred x = body[x]
        // imp operator: head of `(imp body[x]) c`.
        let imp_op = inst
            .concl()
            .as_app()
            .and_then(|(f, _c)| f.as_app())
            .map(|(op, _ante)| op.clone())
            .ok_or_else(|| Error::ConnectiveRule("exists_elim: step is not an implication".into()))?;
        // ⊢ (body[x] ⟹ c) = (pred x ⟹ c), then transport `inst` across it.
        let cong = Thm::refl(imp_op)?
            .cong_app(beta.sym()?)? // ⊢ imp body[x] = imp (pred x)
            .cong_app(Thm::refl(c.clone())?)?; // ⊢ (body[x]⟹c) = (pred x⟹c)
        let applied = cong.eq_mp(inst)?.all_intro(xname, Type::nat())?;
        crate::init::logic::exists_elim(ex, c, applied)
    }

    // ---- the induction schema ----

    fn induct(&self, base: Thm, step: Thm) -> Result<Thm> {
        Thm::nat_induct(base, step)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hol() -> Hol {
        Hol::new()
    }

    #[test]
    fn specialize_then_mp_derives_zero_eq_zero() {
        // From succ_inj: ∀m n. S m = S n ⟹ m = n.
        // Specialize m,n := 0, MP with ⊢ S 0 = S 0, get ⊢ 0 = 0.
        let h = hol();
        let p1 = h.specialize(h.succ_inj(), h.zero()).unwrap();
        let p2 = h.specialize(p1, h.zero()).unwrap();
        let refl = Thm::refl(h.succ(h.zero())).unwrap(); // ⊢ S 0 = S 0
        let q = h.mp(p2, refl).unwrap();

        let expected = {
            use crate::init::ext::TermExt;
            h.zero().equals(h.zero()).unwrap()
        };
        assert_eq!(q.concl(), &expected);
        // succ_inj is genuine, so this derivation is hypothesis-free.
        assert!(q.hyps().is_empty(), "derived from proved axioms only");
    }

    #[test]
    fn axiom_statements_rebuild_through_the_fol_layer() {
        // The `Prop` layer reconstructs each axiom's statement exactly —
        // i.e. `concl(axiom)` equals the formula built from `eq` /
        // connectives / quantifiers.
        let h = hol();

        // add_base: ∀m. 0 + m = m
        let m = h.var("m");
        let add_base_stmt = h.forall("m", h.eq(h.add(h.zero(), m.clone()), m));
        assert_eq!(h.concl(&h.add_base()), add_base_stmt);

        // succ_inj: ∀m n. (S m = S n) ⟹ (m = n)
        let (m, n) = (h.var("m"), h.var("n"));
        let body = h.implies(
            h.eq(h.succ(m.clone()), h.succ(n.clone())),
            h.eq(m, n),
        );
        let succ_inj_stmt = h.forall("m", h.forall("n", body));
        assert_eq!(h.concl(&h.succ_inj()), succ_inj_stmt);

        // zero_ne_succ: ∀n. ¬(0 = S n)
        let n = h.var("n");
        let zns_stmt = h.forall("n", h.not(h.eq(h.zero(), h.succ(n))));
        assert_eq!(h.concl(&h.zero_ne_succ()), zns_stmt);
    }

    #[test]
    fn fol_constructors_build_bool_formulas() {
        // Every formula constructor yields a `bool`-typed HOL term.
        let h = hol();
        let (a, b) = (h.var("a"), h.var("b"));
        let p = h.eq(a.clone(), b.clone());
        let q = h.eq(h.succ(a), b);
        for prop in [
            p.clone(),
            h.not(p.clone()),
            h.and(p.clone(), q.clone()),
            h.or(p.clone(), q.clone()),
            h.implies(p.clone(), q.clone()),
            h.iff(p.clone(), q.clone()),
            h.forall("a", p.clone()),
            h.exists("a", p),
        ] {
            assert!(prop.type_of().unwrap().is_bool());
        }
    }

    #[test]
    fn generalize_over_refl_proves_forall_reflexivity() {
        // ⊢ n = n  ──generalize──▶  ⊢ ∀n. n = n
        let h = hol();
        let refl_n = h.refl(h.var("n")).unwrap();
        let all = h.generalize(refl_n, "n").unwrap();
        assert_eq!(h.concl(&all), h.forall("n", h.eq(h.var("n"), h.var("n"))));
        assert!(all.hyps().is_empty());
    }

    #[test]
    fn conjunction_commutes_via_intro_and_elim() {
        // ⊢ (p ∧ q) ⟹ (q ∧ p), using assume / and_left / and_right /
        // and_intro / implies_intro.
        let h = hol();
        let p = h.eq(h.zero(), h.zero());
        let q = h.eq(h.succ(h.zero()), h.succ(h.zero()));
        let pq = h.and(p.clone(), q.clone());

        let hyp = h.assume(pq.clone()).unwrap(); // {p∧q} ⊢ p∧q
        let pl = h.and_left(hyp.clone()).unwrap(); // {p∧q} ⊢ p
        let qr = h.and_right(hyp).unwrap(); // {p∧q} ⊢ q
        let qp = h.and_intro(qr, pl).unwrap(); // {p∧q} ⊢ q∧p
        let imp = h.implies_intro(pq.clone(), qp).unwrap(); // ⊢ (p∧q)⟹(q∧p)

        assert_eq!(h.concl(&imp), h.implies(pq, h.and(q, p)));
        assert!(imp.hyps().is_empty(), "the assumption was discharged");
    }

    #[test]
    fn excluded_middle_then_case_split() {
        // From LEM `⊢ p ∨ ¬p` and both branches proving `⊢ p ∨ ¬p`
        // (trivially, the disjunction itself), or_elim closes it. Mostly
        // a smoke test that lem + or_elim + implies_intro compose.
        let h = hol();
        let p = h.eq(h.zero(), h.zero());
        let goal = h.or(p.clone(), h.not(p.clone()));

        let lem = h.lem(p.clone()).unwrap(); // ⊢ p ∨ ¬p
        // p ⟹ (p ∨ ¬p)
        let left = {
            let assume_p = h.assume(p.clone()).unwrap();
            let disj = h.or_intro_left(assume_p, h.not(p.clone())).unwrap();
            h.implies_intro(p.clone(), disj).unwrap()
        };
        // ¬p ⟹ (p ∨ ¬p)
        let right = {
            let assume_np = h.assume(h.not(p.clone())).unwrap();
            let disj = h.or_intro_right(p.clone(), assume_np).unwrap();
            h.implies_intro(h.not(p.clone()), disj).unwrap()
        };
        let proved = h.or_elim(lem, left, right).unwrap();
        assert_eq!(h.concl(&proved), goal);
        assert!(proved.hyps().is_empty());
    }

    #[test]
    fn negation_elim_then_ex_falso() {
        // From `⊢ ¬p` (assumed) and `⊢ p` (assumed) derive `⊢ ⊥`, then
        // ex falso to any formula `q`.
        let h = hol();
        let p = h.eq(h.zero(), h.zero());
        let q = h.eq(h.succ(h.zero()), h.zero());

        let not_p = h.assume(h.not(p.clone())).unwrap();
        let p_thm = h.assume(p).unwrap();
        let bottom = h.not_elim(not_p, p_thm).unwrap(); // ⊢ ⊥
        assert_eq!(h.concl(&bottom), h.falsum());
        let anything = h.absurd(bottom, q.clone()).unwrap(); // ⊢ q
        assert_eq!(h.concl(&anything), q);
    }

    #[test]
    fn existential_intro_then_elim_roundtrip() {
        // ∃-intro: from ⊢ 0 = 0 conclude ⊢ ∃n. n = 0.
        // ∃-elim: feed it back through ∀n. (n = 0) ⟹ (0 = 0) to recover
        // ⊢ 0 = 0.
        let h = hol();
        let body = h.eq(h.var("n"), h.zero()); // n = 0
        let refl0 = h.refl(h.zero()).unwrap(); // ⊢ 0 = 0  (= body[0/n])
        let ex = h.exists_intro("n", body.clone(), h.zero(), refl0).unwrap();
        assert_eq!(h.concl(&ex), h.exists("n", body.clone()));
        assert!(ex.hyps().is_empty());

        // step: ⊢ ∀n. (n = 0) ⟹ (0 = 0)
        let c = h.eq(h.zero(), h.zero());
        let step = {
            let _assume_body = h.assume(body.clone()).unwrap();
            let refl0 = h.refl(h.zero()).unwrap(); // ⊢ 0 = 0
            let imp = h.implies_intro(body, refl0).unwrap(); // ⊢ (n=0)⟹(0=0)
            h.generalize(imp, "n").unwrap()
        };
        let recovered = h.exists_elim(ex, c.clone(), step).unwrap();
        assert_eq!(h.concl(&recovered), c);
        assert!(recovered.hyps().is_empty());
    }

    #[test]
    fn induction_is_genuine_and_axiom_free() {
        // Prove ⊢ ∀n. P n for the trivial motive P := λn. T.
        let h = hol();
        let t = Term::bool_lit(true);
        let p = Term::abs(Type::nat(), t.clone()); // λn. T

        let base = Thm::beta_conv(Term::app(p.clone(), h.zero()))
            .unwrap()
            .sym()
            .unwrap()
            .eq_mp(crate::init::logic::truth())
            .unwrap();

        let n = h.var("n");
        let p_n = Thm::beta_conv(Term::app(p.clone(), n.clone()))
            .unwrap()
            .sym()
            .unwrap()
            .eq_mp(crate::init::logic::truth())
            .unwrap();
        let p_succ_n = Thm::beta_conv(Term::app(p, h.succ(n)))
            .unwrap()
            .sym()
            .unwrap()
            .eq_mp(crate::init::logic::truth())
            .unwrap();
        let step = p_succ_n.imp_intro(p_n.concl()).unwrap();

        let all = h.induct(base, step).unwrap();
        assert!(all.hyps().is_empty(), "induction adds no PA postulates");
        let covalence_core::TermKind::App(_forall, lam) = all.concl().kind() else {
            panic!("expected a ∀ application");
        };
        assert!(lam.as_abs().map(|(ty, _)| ty == &Type::nat()).unwrap_or(false));
    }
}
