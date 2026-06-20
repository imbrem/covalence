//! `monoid` — the **theory of monoids** and a **model-generic monoid
//! normalizer**.
//!
//! A monoid is the canonical *theory with many models*: a carrier `μ`, a
//! binary operation `op : μ → μ → μ`, a `unit : μ`, and the three laws
//!
//! ```text
//!     ⊢ op (op a b) c = op a (op b c)   (assoc)
//!     ⊢ op unit a = a                   (left_id)
//!     ⊢ op a unit = a                   (right_id)
//! ```
//!
//! `(nat, +, 0)`, `(nat, ×, 1)`, `(list, append, nil)`, and the function
//! category's hom-monoid `(α→α, ∘, id)` are all *models* of this one theory.
//! The point of this module is that the **same normalizer** works for every
//! model: it is parameterized by a [`Monoid`] value carrying the model's `op`,
//! `unit`, and the three law theorems, so swapping the model swaps nothing in
//! the algorithm.
//!
//! # The rewriter
//!
//! [`Monoid::normalize`] is a *rewriter* in the sense the `.cov` language
//! discusses (`crate::script::tactic`): a thing that takes a term `a` and
//! returns a **proof** `⊢ a = b`, where `b` is the canonical form. Here `b` is
//! the **right-associated product with all identities dropped**:
//!
//! ```text
//!     op (op a unit) (op b (op unit c))   ↦   op a (op b c)
//!     op a unit                           ↦   a
//!     unit                                ↦   unit
//! ```
//!
//! Two such normal forms are `=`-equal iff their *leaf sequences* (the
//! non-unit factors, left to right) agree — so `normalize l |> trans
//! (normalize r |> sym)` decides any monoid-word equation. That decision
//! procedure is [`Monoid::prove_eq`].
//!
//! Every step is a genuine kernel rewrite built from the law theorems via
//! `trans` / `mk_comb` (congruence) — no oracle, no postulate. The normalizer
//! never inspects *why* `assoc`/`left_id`/`right_id` hold; it only consumes
//! them as `⊢ … = …` equalities, which is exactly what makes it model-generic.
//!
//! # Plugging into the script layer
//!
//! [`Monoid::rw_lemmas`] returns the three laws as `∀`-quantified theorems
//! suitable for registering in an [`Env`](crate::script::Env), so a `.cov`
//! proof can `(rw assoc)` / `(rw left_id)` / `(rw right_id)` against any model
//! the host installs. The Rust [`normalize`](Monoid::normalize) is the
//! *batched* form of those same rewrites — the seed for a future
//! `(monoid-normalize)` rewriter inference (see `SKELETONS.md`).

use covalence_core::{Result, Term, Thm};

use crate::init::ext::TermExt;

/// A concrete **model** of the monoid theory: the operation, the unit, and the
/// three laws as already-proved (`∀`-quantified) theorems. Build one with
/// [`Monoid::new`] (or a model constructor like [`nat_add_monoid`]) and feed it
/// to the generic [`normalize`](Monoid::normalize) / [`prove_eq`](Monoid::prove_eq).
///
/// The law theorems are stored in their universally-quantified form (the shape
/// `nat.cov` / `cat.rs` export); the normalizer `all_elim`s them at the
/// concrete subterms it meets.
#[derive(Clone)]
pub struct Monoid {
    /// The binary operation `op : μ → μ → μ` (an *unapplied* term).
    op: Term,
    /// The identity element `unit : μ`.
    unit: Term,
    /// `⊢ ∀a b c. op (op a b) c = op a (op b c)`.
    assoc: Thm,
    /// `⊢ ∀a. op unit a = a`.
    left_id: Thm,
    /// `⊢ ∀a. op a unit = a`.
    right_id: Thm,
}

impl Monoid {
    /// Assemble a model from its operation, unit, and the three law theorems.
    /// The theorems are trusted to have the documented shapes; the kernel
    /// re-checks every step the normalizer derives from them, so a *wrong*
    /// theorem can at worst make `normalize` fail, never forge an unsound proof.
    pub fn new(op: Term, unit: Term, assoc: Thm, left_id: Thm, right_id: Thm) -> Self {
        Monoid {
            op,
            unit,
            assoc,
            left_id,
            right_id,
        }
    }

    /// The operation term.
    pub fn op(&self) -> &Term {
        &self.op
    }
    /// The unit term.
    pub fn unit(&self) -> &Term {
        &self.unit
    }
    /// The three laws, in `(assoc, left_id, right_id)` order — ready to register
    /// as `.cov` rewrite lemmas.
    pub fn rw_lemmas(&self) -> (Thm, Thm, Thm) {
        (self.assoc.clone(), self.left_id.clone(), self.right_id.clone())
    }

    /// `op a b`, both arguments supplied.
    fn mk_op(&self, a: Term, b: Term) -> Result<Term> {
        self.op.clone().apply(a)?.apply(b)
    }

    /// If `t` is `op a b` for *this* monoid's `op`, return `(a, b)`. Matching is
    /// by structural equality of the head against `self.op` — so it is exact for
    /// the model's operation and ignores any other binary operator.
    fn dest_op(&self, t: &Term) -> Option<(Term, Term)> {
        let (f, b) = t.as_app()?;
        let (head, a) = f.as_app()?;
        (*head == self.op).then(|| (a.clone(), b.clone()))
    }

    /// Whether `t` is *this* monoid's unit (structural equality).
    fn is_unit(&self, t: &Term) -> bool {
        *t == self.unit
    }

    /// **The rewriter.** `⊢ t = nf`, where `nf` is `t`'s canonical monoid normal
    /// form: fully right-associated, with every `unit` factor dropped (unless
    /// the whole word *is* the unit). Genuine — built from the law theorems by
    /// congruence + transitivity.
    ///
    /// Algorithm (a normalization-by-rewriting pass):
    ///
    /// 1. Recursively normalize the two children of an `op` node first
    ///    (`⊢ a = a'`, `⊢ b = b'`), lift to `⊢ op a b = op a' b'` by congruence.
    /// 2. Drop a child that became `unit`: `op unit b' → b'` (`left_id`),
    ///    `op a' unit → a'` (`right_id`).
    /// 3. Re-associate: if the left child is itself `op p q`, rewrite
    ///    `op (op p q) b' → op p (op q b')` (`assoc`) and recurse on the new
    ///    right child, so the result is right-nested.
    /// 4. A non-`op` leaf (a variable, a literal, the unit) normalizes to
    ///    itself (`refl`).
    pub fn normalize(&self, t: &Term) -> Result<Thm> {
        // Leaf: nothing to do.
        let Some((a, b)) = self.dest_op(t) else {
            return Thm::refl(t.clone());
        };

        // 1. Normalize children.
        let a_eq = self.normalize(&a)?; // ⊢ a = a'
        let b_eq = self.normalize(&b)?; // ⊢ b = b'
        let (_, a_nf) = a_eq.concl().as_eq().expect("normalize yields an eq");
        let (_, b_nf) = b_eq.concl().as_eq().expect("normalize yields an eq");
        let (a_nf, b_nf) = (a_nf.clone(), b_nf.clone());

        // ⊢ op a b = op a' b'  (congruence on the op head).
        let cong = Thm::refl(self.op.clone())?.mk_comb(a_eq)?.mk_comb(b_eq)?;

        // 2a. op unit b' → b'   (left_id at b').
        if self.is_unit(&a_nf) {
            let li = self.left_id.clone().all_elim(b_nf.clone())?; // ⊢ op unit b' = b'
            return cong.trans(li);
        }
        // 2b. op a' unit → a'   (right_id at a').
        if self.is_unit(&b_nf) {
            let ri = self.right_id.clone().all_elim(a_nf.clone())?; // ⊢ op a' unit = a'
            return cong.trans(ri);
        }

        // 3. Re-associate a left-nested product: op (op p q) b' → op p (op q b').
        if let Some((p, q)) = self.dest_op(&a_nf) {
            // ⊢ op (op p q) b' = op p (op q b')
            let assoc = self
                .assoc
                .clone()
                .all_elim(p.clone())?
                .all_elim(q.clone())?
                .all_elim(b_nf.clone())?;
            // The new right child `op q b'` may itself be reducible; renormalize
            // the whole right-nested term `op p (op q b')` so the final form is
            // fully right-associated and identity-free.
            let inner = self.mk_op(q, b_nf)?;
            let inner_nf = self.normalize(&inner)?; // ⊢ op q b' = (op q b')'
            let (_, inner_t) = inner_nf.concl().as_eq().expect("eq");
            let right = Thm::refl(self.op.clone())?
                .mk_comb(Thm::refl(p)?)?
                .mk_comb(inner_nf.clone())?; // ⊢ op p (op q b') = op p (op q b')'
            let _ = inner_t;
            return cong.trans(assoc)?.trans(right);
        }

        // Already right-shaped (left child is a leaf, neither child is unit).
        Ok(cong)
    }

    /// **The decision procedure.** `⊢ lhs = rhs` when `lhs` and `rhs` are equal
    /// monoid words — i.e. they share a normal form. Errors (with a normal-form
    /// mismatch) otherwise. `normalize` each side, then bridge by `trans`/`sym`.
    pub fn prove_eq(&self, lhs: &Term, rhs: &Term) -> Result<Thm> {
        let l = self.normalize(lhs)?; // ⊢ lhs = nf_l
        let r = self.normalize(rhs)?; // ⊢ rhs = nf_r
        l.trans(r.sym()?) // ⊢ lhs = rhs   (fails in `trans` if nf_l ≠ nf_r)
    }
}

// ============================================================================
// Models
// ============================================================================

/// The additive monoid `(nat, +, 0)`.
///
/// `assoc = nat.add_assoc`, `left_id = nat.add_base` (`0 + a = a`),
/// `right_id = nat.add_zero` (`a + 0 = a`) — all genuine Peano theorems.
pub fn nat_add_monoid() -> Monoid {
    use crate::init::nat;
    Monoid::new(
        covalence_core::defs::nat_add(),
        Term::nat_lit(0u32),
        nat::add_assoc(),
        nat::add_base(),
        nat::add_zero(),
    )
}

/// The multiplicative monoid `(nat, ×, 1)`.
///
/// `assoc = nat.mul_assoc`, `right_id = nat.mul_one` (`a × 1 = a`). The left
/// identity `1 × a = a` is derived here from `mul_one` + `mul_comm` (`1 × a =
/// a × 1 = a`), so the model is built only from already-proved theorems.
pub fn nat_mul_monoid() -> Monoid {
    use crate::init::nat;
    let a = Term::free("a", covalence_core::Type::nat());
    let one = Term::nat_lit(1u32);
    // left_id: ⊢ ∀a. 1 × a = a.
    let one_mul = (|| -> Result<Thm> {
        // mul_comm @ 1 @ a : 1 × a = a × 1 ; mul_one @ a : a × 1 = a.
        let comm = nat::mul_comm().all_elim(one.clone())?.all_elim(a.clone())?;
        let mo = nat::mul_one().all_elim(a.clone())?;
        comm.trans(mo)?.all_intro("a", covalence_core::Type::nat())
    })()
    .expect("nat_mul_monoid: derive 1×a=a from mul_comm + mul_one");
    Monoid::new(
        covalence_core::defs::nat_mul(),
        one,
        nat::mul_assoc(),
        one_mul,
        nat::mul_one(),
    )
}

/// The **hom-monoid** of the function category at a single object: endomaps
/// `(α → α, ∘, id)`. `assoc = cat.comp_assoc`, `left_id = cat.id_left`
/// (`id ∘ f = f`), `right_id = cat.id_right` (`f ∘ id = f`) — the genuine
/// category laws from `init::cat`, specialized so every morphism is `α → α`.
///
/// This is the bridge between the monoid and categorical rewriters: an
/// endomorphism monoid is *literally* a one-object category, so the same
/// [`Monoid::normalize`] re-associates and id-eliminates composites
/// `(h ∘ g) ∘ f` exactly as the category-rewrite tactic does.
pub fn endo_monoid(alpha: covalence_core::Type) -> Result<Monoid> {
    use crate::init::cat;
    let endo = covalence_core::Type::fun(alpha.clone(), alpha.clone());
    // compose specialized to α→α→α (all three objects = α).
    let op = cat::compose(alpha.clone(), alpha.clone(), alpha.clone());
    let unit = cat::id(alpha.clone());

    // assoc: ⊢ ∀h g f. (h∘g)∘f = h∘(g∘f), all endomaps of α.
    let f = Term::free("f", endo.clone());
    let g = Term::free("g", endo.clone());
    let h = Term::free("h", endo.clone());
    let assoc = cat::comp_assoc(&h, &g, &f)?
        .all_intro("f", endo.clone())?
        .all_intro("g", endo.clone())?
        .all_intro("h", endo.clone())?;
    // left_id: ⊢ ∀f. id∘f = f.
    let left_id = cat::id_left(&f)?.all_intro("f", endo.clone())?;
    // right_id: ⊢ ∀f. f∘id = f.
    let right_id = cat::id_right(&f)?.all_intro("f", endo.clone())?;
    Ok(Monoid::new(op, unit, assoc, left_id, right_id))
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_core::Type;

    fn n(name: &str) -> Term {
        Term::free(name, Type::nat())
    }

    /// `add` of two terms.
    fn add(a: Term, b: Term) -> Term {
        Term::app(Term::app(covalence_core::defs::nat_add(), a), b)
    }
    fn mul(a: Term, b: Term) -> Term {
        Term::app(Term::app(covalence_core::defs::nat_mul(), a), b)
    }

    fn assert_genuine(thm: &Thm) {
        assert!(thm.hyps().is_empty(), "expected a hypothesis-free theorem");
        assert!(thm.has_no_obs(), "expected an oracle-free theorem");
    }

    // -- (nat, +, 0) ---------------------------------------------------------

    #[test]
    fn add_normalize_drops_units() {
        let m = nat_add_monoid();
        // (a + 0) + (0 + b)  normalizes to  a + b.
        let zero = Term::nat_lit(0u32);
        let expr = add(add(n("a"), zero.clone()), add(zero, n("b")));
        let thm = m.normalize(&expr).unwrap();
        assert_genuine(&thm);
        let (lhs, rhs) = thm.concl().as_eq().unwrap();
        assert_eq!(lhs, &expr);
        assert_eq!(rhs, &add(n("a"), n("b")));
    }

    #[test]
    fn add_normalize_right_associates() {
        let m = nat_add_monoid();
        // ((a + b) + c) + d  →  a + (b + (c + d)).
        let expr = add(add(add(n("a"), n("b")), n("c")), n("d"));
        let thm = m.normalize(&expr).unwrap();
        assert_genuine(&thm);
        let (_, rhs) = thm.concl().as_eq().unwrap();
        let expected = add(n("a"), add(n("b"), add(n("c"), n("d"))));
        assert_eq!(rhs, &expected);
    }

    #[test]
    fn add_prove_eq_reassociates_both_sides() {
        let m = nat_add_monoid();
        // (a + b) + c  =  a + (b + c)   — the assoc law, recovered as a word eq.
        let lhs = add(add(n("a"), n("b")), n("c"));
        let rhs = add(n("a"), add(n("b"), n("c")));
        let thm = m.prove_eq(&lhs, &rhs).unwrap();
        assert_genuine(&thm);
        assert_eq!(thm.concl().as_eq().unwrap(), (&lhs, &rhs));
    }

    #[test]
    fn add_prove_eq_through_identities() {
        let m = nat_add_monoid();
        let zero = Term::nat_lit(0u32);
        // ((a + 0) + b) + 0  =  0 + (a + (0 + b))  — both sides are the word a·b.
        let lhs = add(add(add(n("a"), zero.clone()), n("b")), zero.clone());
        let rhs = add(zero.clone(), add(n("a"), add(zero, n("b"))));
        let thm = m.prove_eq(&lhs, &rhs).unwrap();
        assert_genuine(&thm);
        assert_eq!(thm.concl().as_eq().unwrap(), (&lhs, &rhs));
    }

    #[test]
    fn add_prove_eq_rejects_distinct_words() {
        let m = nat_add_monoid();
        // a + b  ≠  b + a as *words* (the normalizer is not commutative).
        let lhs = add(n("a"), n("b"));
        let rhs = add(n("b"), n("a"));
        assert!(m.prove_eq(&lhs, &rhs).is_err());
    }

    // -- (nat, ×, 1) — the SAME normalizer, a different model ----------------

    #[test]
    fn mul_normalize_drops_units() {
        let m = nat_mul_monoid();
        let one = Term::nat_lit(1u32);
        // (a × 1) × (1 × b)  →  a × b.
        let expr = mul(mul(n("a"), one.clone()), mul(one, n("b")));
        let thm = m.normalize(&expr).unwrap();
        assert_genuine(&thm);
        let (_, rhs) = thm.concl().as_eq().unwrap();
        assert_eq!(rhs, &mul(n("a"), n("b")));
    }

    #[test]
    fn mul_prove_eq_reassociates() {
        let m = nat_mul_monoid();
        // ((a × b) × c) × d  =  a × (b × (c × d)).
        let lhs = mul(mul(mul(n("a"), n("b")), n("c")), n("d"));
        let rhs = mul(n("a"), mul(n("b"), mul(n("c"), n("d"))));
        let thm = m.prove_eq(&lhs, &rhs).unwrap();
        assert_genuine(&thm);
        assert_eq!(thm.concl().as_eq().unwrap(), (&lhs, &rhs));
    }

    // -- (α→α, ∘, id) — endomorphism monoid = one-object category ------------

    fn endo_var(name: &str, alpha: &Type) -> Term {
        Term::free(name, Type::fun(alpha.clone(), alpha.clone()))
    }
    fn comp(alpha: &Type, g: Term, f: Term) -> Term {
        Term::app(
            Term::app(
                crate::init::cat::compose(alpha.clone(), alpha.clone(), alpha.clone()),
                g,
            ),
            f,
        )
    }

    #[test]
    fn endo_normalize_drops_id_and_reassociates() {
        let alpha = Type::tfree("a");
        let m = endo_monoid(alpha.clone()).unwrap();
        let id = crate::init::cat::id(alpha.clone());
        let f = endo_var("f", &alpha);
        let g = endo_var("g", &alpha);
        let h = endo_var("h", &alpha);
        // (h ∘ (g ∘ id)) ∘ (id ∘ f)  →  h ∘ (g ∘ f).
        let expr = comp(
            &alpha,
            comp(&alpha, h.clone(), comp(&alpha, g.clone(), id.clone())),
            comp(&alpha, id, f.clone()),
        );
        let thm = m.normalize(&expr).unwrap();
        assert_genuine(&thm);
        let (_, rhs) = thm.concl().as_eq().unwrap();
        let expected = comp(&alpha, h, comp(&alpha, g, f));
        assert_eq!(rhs, &expected);
    }

    #[test]
    fn endo_prove_eq_comp_assoc() {
        let alpha = Type::tfree("a");
        let m = endo_monoid(alpha.clone()).unwrap();
        let f = endo_var("f", &alpha);
        let g = endo_var("g", &alpha);
        let h = endo_var("h", &alpha);
        // (h ∘ g) ∘ f = h ∘ (g ∘ f).
        let lhs = comp(&alpha, comp(&alpha, h.clone(), g.clone()), f.clone());
        let rhs = comp(&alpha, h, comp(&alpha, g, f));
        let thm = m.prove_eq(&lhs, &rhs).unwrap();
        assert_genuine(&thm);
        assert_eq!(thm.concl().as_eq().unwrap(), (&lhs, &rhs));
    }
}
