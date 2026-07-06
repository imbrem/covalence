//! A **general ring (semiring) rewrite tactic**: normalize a `(+, ·, 0, 1)`
//! expression to a canonical **sum-of-monomials** form, producing a
//! kernel-checked `⊢ e = nf`.
//!
//! Built on the AC tactic ([`crate::algebra::ac`]): `+` and `·` are each
//! associative-commutative, so once the expression is *expanded* (every product
//! distributed over every sum) it is a flat sum of monomials, and each layer is
//! AC-normalized. Two ring-equal expressions (in the deferred-coefficient
//! fragment below) reach the *same* normal form, so
//! [`RingNormalizer::prove_eq`] decides `⊢ e₁ = e₂`.
//!
//! ## The normal form
//!
//! A **monomial** is a product of *atoms* (leaves that are neither `+` nor `·`),
//! right-nested and AC-sorted: `a₁ · (a₂ · (⋯ · aₖ))`. A **polynomial** is a sum
//! of monomials, right-nested and AC-sorted: `m₁ + (m₂ + (⋯ + mₙ))`. Identity
//! cleanup folds `· 1` and `+ 0` away and collapses any `· 0` monomial to `0`.
//!
//! ## Scope (what is decided vs. deferred)
//!
//! **Decided:** distributivity, `+`/`·` associativity + commutativity, and the
//! `0`/`1` identities — i.e. any two expressions equal as *formal* sums of
//! monomials over the atoms.
//!
//! **Deferred** (see `crate::algebra::ring`'s `SKELETONS.md` entry):
//! - *coefficient collection* — `x + x` is left as `x + x`, not folded to
//!   `2 · x`; like monomials are **not** combined. So `x + x = x + x` is
//!   decided, but `x + x = 2·x` is not.
//! - *negation / subtraction* — `neg` / `sub` are not expanded; an expression
//!   mentioning them is normalized only down to its `+`/`·` structure.
//! - *literal coefficient arithmetic* in monomials.
//!
//! Every rewrite step is a genuine kernel equality (distrib / AC / identity
//! axioms instantiated and threaded through `trans` + congruence).

use covalence_core::{Error, Result, Term};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::derived::DerivedRules;

use crate::algebra::ac::{Ac, AcOp, HolAc};
use crate::init::ext::{TermExt, ThmExt};

/// The ring operators + axioms a [`RingNormalizer`] needs, as HOL terms / `Thm`s.
///
/// Mirrors [`AcOp`] but for the *two* operators together with distributivity
/// and the identities. Construct one with [`RingOps::new`] from a carrier's
/// catalogue (e.g. `nat` or `int`).
#[derive(Clone)]
pub struct RingOps {
    add: Term,
    mul: Term,
    zero: Term,
    one: Term,
    /// `⊢ ∀a b c. a·(b+c) = a·b + a·c`
    distrib_l: Thm,
    /// `⊢ ∀a b. a·b = b·a` — kept to *derive* right distributivity on demand.
    mul_comm: Thm,
    /// `⊢ ∀a. a·1 = a`
    mul_one: Thm,
    /// `⊢ ∀a. a·0 = 0`
    mul_zero: Thm,
    /// `⊢ ∀a. a+0 = a`
    add_zero: Thm,
    add_ac: HolAc,
    mul_ac: HolAc,
}

impl RingOps {
    /// Build a ring-normalizer descriptor from the operator terms and the
    /// `∀`-quantified axioms (the catalogue shape — `nat` / `int`).
    ///
    /// `distrib_l : ⊢ ∀a b c. a·(b+c) = a·b + a·c`, `mul_one / mul_zero /
    /// add_zero` the identity axioms, and `add_comm / add_assoc / mul_comm /
    /// mul_assoc` the AC axioms. The *right* distributivity
    /// `⊢ ∀a b c. (a+b)·c = a·c + b·c` is **derived** from `distrib_l` +
    /// `mul_comm` (so a carrier need not ship it separately).
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        add: Term,
        mul: Term,
        zero: Term,
        one: Term,
        add_assoc: Thm,
        add_comm: Thm,
        mul_assoc: Thm,
        mul_comm: Thm,
        distrib_l: Thm,
        mul_one: Thm,
        mul_zero: Thm,
        add_zero: Thm,
    ) -> Self {
        let add_ac = HolAc::from_forall(add.clone(), add_assoc, add_comm);
        let mul_ac = HolAc::from_forall(mul.clone(), mul_assoc, mul_comm.clone());
        Self {
            add,
            mul,
            zero,
            one,
            distrib_l,
            mul_comm,
            mul_one,
            mul_zero,
            add_zero,
            add_ac,
            mul_ac,
        }
    }

    fn add(&self, a: Term, b: Term) -> Result<Term> {
        self.add.clone().apply(a)?.apply(b)
    }
    fn mul(&self, a: Term, b: Term) -> Result<Term> {
        self.mul.clone().apply(a)?.apply(b)
    }
    fn as_add(&self, t: &Term) -> Option<(Term, Term)> {
        self.add_ac.dest(t)
    }
    fn as_mul(&self, t: &Term) -> Option<(Term, Term)> {
        self.mul_ac.dest(t)
    }
}

/// The general ring rewriter. See the [module docs](self).
pub struct RingNormalizer {
    ops: RingOps,
    add_engine: Ac<HolAc, fn(&Term) -> String, String>,
    mul_engine: Ac<HolAc, fn(&Term) -> String, String>,
}

impl RingNormalizer {
    /// Build a normalizer from a [`RingOps`].
    pub fn new(ops: RingOps) -> Self {
        let add_engine = Ac::new(ops.add_ac.clone(), Term::to_string as fn(&Term) -> String);
        let mul_engine = Ac::new(ops.mul_ac.clone(), Term::to_string as fn(&Term) -> String);
        Self {
            ops,
            add_engine,
            mul_engine,
        }
    }

    /// `⊢ e = nf`: the sum-of-monomials normal form of ring expression `e`.
    pub fn normalize(&self, e: &Term) -> Result<Thm> {
        // 1. Expand: distribute every product over every sum → flat sum of
        //    monomials (each monomial a pure product, no `+` inside).
        let expanded = self.expand(e)?; // ⊢ e = sum-of-products
        let se = rhs(&expanded)?;
        // 2. AC-normalize the sum (and each monomial), dropping identities.
        let sorted = self.normalize_sum(&se)?; // ⊢ se = nf
        expanded.trans(sorted)
    }

    /// `⊢ e₁ = e₂` for ring-equal `e₁`, `e₂` (in the decided fragment). Errors —
    /// minting nothing — when their normal forms differ.
    pub fn prove_eq(&self, e1: &Term, e2: &Term) -> Result<Thm> {
        let n1 = self.normalize(e1)?;
        let n2 = self.normalize(e2)?;
        let (nf1, nf2) = (rhs(&n1)?, rhs(&n2)?);
        if nf1 != nf2 {
            return Err(Error::ConnectiveRule(format!(
                "ring::prove_eq: `{e1}` and `{e2}` differ as polynomials (`{nf1}` vs `{nf2}`)"
            )));
        }
        n1.trans(n2.sym()?)
    }

    // ---- phase 1: expand (distribute) ----

    /// `⊢ e = e'` where `e'` is `e` with every product distributed over every
    /// sum, so no `·` node has a `+`-headed argument. The result is a sum (via
    /// `+`) of pure-product monomials.
    fn expand(&self, e: &Term) -> Result<Thm> {
        if let Some((a, b)) = self.ops.as_add(e) {
            // (expand a) + (expand b)
            let ea = self.expand(&a)?;
            let eb = self.expand(&b)?;
            return self.cong_add(ea, eb);
        }
        if let Some((a, b)) = self.ops.as_mul(e) {
            // Expand the factors first, then multiply the two sums out.
            let ea = self.expand(&a)?; // ⊢ a = A (a sum of monomials)
            let eb = self.expand(&b)?; // ⊢ b = B
            let cong = self.cong_mul(ea, eb)?; // ⊢ a·b = A·B
            let ab = rhs(&cong)?;
            let (big_a, big_b) = self.ops.as_mul(&ab).expect("A·B is a product");
            // `A`, `B` are already sums of *pure* products (from the recursive
            // `expand` on the factors), so `mul_sum` fully distributes into a sum
            // of pure-product cross-terms — no further expansion is needed.
            let dist = self.mul_sum(&big_a, &big_b)?; // ⊢ A·B = expanded
            return cong.trans(dist);
        }
        // A leaf (atom, 0, or 1): nothing to distribute.
        Thm::refl(e.clone())
    }

    /// `⊢ A·B = Σ` where `A`, `B` are sums of monomials and `Σ` distributes the
    /// product into the sum of all pairwise products `mₐ·m_b`.
    fn mul_sum(&self, a: &Term, b: &Term) -> Result<Thm> {
        // Split `A` on its leading `+`: A = a0 + A'. Then
        //   (a0 + A')·B = a0·B + A'·B    [distrib_r]
        // recurse on A'·B; a0·B distributes by `mul_mono_sum`.
        if let Some((a0, a_rest)) = self.ops.as_add(a) {
            let dr = self.distrib_r_at(&a0, &a_rest, b)?; // ⊢ (a0+A')·B = a0·B + A'·B
            let left = self.mul_mono_sum(&a0, b)?; // ⊢ a0·B = Σ_b a0·m_b
            let right = self.mul_sum(&a_rest, b)?; // ⊢ A'·B = …
            let cong = self.cong_add(left, right)?;
            return dr.trans(cong);
        }
        // `A` is a single monomial: distribute it over `B`.
        self.mul_mono_sum(a, b)
    }

    /// `⊢ m·B = Σ_b m·m_b` — a single monomial `m` times a sum `B`.
    fn mul_mono_sum(&self, m: &Term, b: &Term) -> Result<Thm> {
        if let Some((b0, b_rest)) = self.ops.as_add(b) {
            let dl = self.distrib_l_at(m, &b0, &b_rest)?; // ⊢ m·(b0+B') = m·b0 + m·B'
            let right = self.mul_mono_sum(m, &b_rest)?; // ⊢ m·B' = …
            let cong = self.cong_add(Thm::refl(self.ops.mul(m.clone(), b0.clone())?)?, right)?;
            return dl.trans(cong);
        }
        // `B` is a single monomial: `m·b` is already a pure product.
        Thm::refl(self.ops.mul(m.clone(), b.clone())?)
    }

    // ---- phase 2: AC-normalize + identity cleanup ----

    /// `⊢ s = nf`: AC-normalize a sum-of-monomials `s` — normalize each monomial
    /// (product) by the `·` AC engine + identity cleanup, then AC-normalize the
    /// whole `+`-sum and drop `+0` terms.
    fn normalize_sum(&self, s: &Term) -> Result<Thm> {
        // First, normalize every monomial in place (congruence over `+`).
        let monos = self.normalize_each_mono(s)?; // ⊢ s = s'
        let s1 = rhs(&monos)?;
        // Then AC-sort the `+`-sum.
        let ac = self.add_engine.normalize(&s1)?; // ⊢ s' = s''
        let s2 = rhs(&ac)?;
        // Finally, drop `+0` terms.
        let z = self.drop_add_zeros(&s2)?; // ⊢ s'' = nf
        monos.trans(ac)?.trans(z)
    }

    /// `⊢ s = s'` normalizing each monomial of the `+`-sum `s` (congruence on the
    /// `+`-spine; each leaf monomial is run through [`Self::normalize_mono`]).
    fn normalize_each_mono(&self, s: &Term) -> Result<Thm> {
        if let Some((m, rest)) = self.ops.as_add(s) {
            let lm = self.normalize_mono(&m)?;
            let lr = self.normalize_each_mono(&rest)?;
            return self.cong_add(lm, lr);
        }
        self.normalize_mono(s)
    }

    /// `⊢ m = m'`: normalize a single monomial (a pure product) — AC-sort the
    /// `·`-factors, then drop `·1` factors and collapse a `·0` to `0`.
    fn normalize_mono(&self, m: &Term) -> Result<Thm> {
        // If the monomial contains a `0` factor it is `0` (annihilation).
        if self.mono_has_zero(m) {
            return self.mono_to_zero(m);
        }
        // AC-sort the product.
        let ac = self.mul_engine.normalize(m)?; // ⊢ m = m'
        let m1 = rhs(&ac)?;
        // Drop `·1` factors.
        let ones = self.drop_mul_ones(&m1)?; // ⊢ m' = m''
        ac.trans(ones)
    }

    /// Whether monomial `m` (a product spine) has a `0` factor.
    fn mono_has_zero(&self, m: &Term) -> bool {
        self.mul_engine
            .leaves(m)
            .iter()
            .any(|f| f == &self.ops.zero)
    }

    /// `⊢ m = 0` for a monomial containing a `0` factor (by `mul_zero` after
    /// AC-pulling the `0` to the front).
    fn mono_to_zero(&self, m: &Term) -> Result<Thm> {
        // Base case: `m` is itself the `0` leaf.
        if m == &self.ops.zero {
            return Thm::refl(m.clone());
        }
        // Sort so a `0` factor leads, then `0 · rest`; `mul_zero`/`mul_comm`
        // collapse it. We reduce to: AC-normal `m = 0·rest`, then mul_zero.
        let ac = self.mul_engine.normalize(m)?; // ⊢ m = m'
        let m1 = rhs(&ac)?;
        // `m'` is sorted; `0` sorts as a leaf among the factors. Pull it to the
        // head if needed, then apply `0 · rest = 0`.
        let (head, rest) = self
            .ops
            .as_mul(&m1)
            .ok_or_else(|| Error::ConnectiveRule("mono_to_zero: m' is not a product".into()))?;
        if head == self.ops.zero {
            // 0 · rest = 0  via  mul_comm then mul_zero, or mul_zero on the left:
            // mul_zero is `a·0 = 0`; we have `0·rest`. Use comm to `rest·0`.
            let comm = self.mul_engine.op().comm_at(&head, &rest)?; // ⊢ 0·rest = rest·0
            let mz = self.mul_zero_at(&rest)?; // ⊢ rest·0 = 0
            return ac.trans(comm)?.trans(mz);
        }
        // Otherwise the `0` is somewhere in `rest`; recurse to turn `rest` into
        // `0`, then `head · 0 = 0`.
        let rest_zero = self.mono_to_zero(&rest)?; // ⊢ rest = 0
        let cong = self.cong_mul(Thm::refl(head.clone())?, rest_zero)?; // ⊢ head·rest = head·0
        let mz = self.mul_zero_at(&head)?; // ⊢ head·0 = 0
        ac.trans(cong)?.trans(mz)
    }

    /// `⊢ m = m'` dropping every `·1` factor from a (sorted) product `m`.
    fn drop_mul_ones(&self, m: &Term) -> Result<Thm> {
        let Some((head, rest)) = self.ops.as_mul(m) else {
            return Thm::refl(m.clone());
        };
        // Normalize the tail first.
        let rest_eq = self.drop_mul_ones(&rest)?; // ⊢ rest = rest'
        let rest1 = rhs(&rest_eq)?;
        if head == self.ops.one {
            // 1 · rest' = rest'  via mul_one after comm (mul_one is `a·1 = a`).
            let cong = self.cong_mul(Thm::refl(head.clone())?, rest_eq)?; // ⊢ head·rest = 1·rest'
            let comm = self.mul_engine.op().comm_at(&head, &rest1)?; // ⊢ 1·rest' = rest'·1
            let mo = self.mul_one_at(&rest1)?; // ⊢ rest'·1 = rest'
            return cong.trans(comm)?.trans(mo);
        }
        if rest1 == self.ops.one {
            // head · 1 = head
            let cong = self.cong_mul(Thm::refl(head.clone())?, rest_eq)?; // ⊢ head·rest = head·1
            let mo = self.mul_one_at(&head)?; // ⊢ head·1 = head
            return cong.trans(mo);
        }
        self.cong_mul(Thm::refl(head.clone())?, rest_eq)
    }

    /// `⊢ s = s'` dropping every `+0` term from a (sorted) sum `s`.
    fn drop_add_zeros(&self, s: &Term) -> Result<Thm> {
        let Some((head, rest)) = self.ops.as_add(s) else {
            return Thm::refl(s.clone());
        };
        let rest_eq = self.drop_add_zeros(&rest)?; // ⊢ rest = rest'
        let rest1 = rhs(&rest_eq)?;
        if head == self.ops.zero {
            // 0 + rest' = rest'  via comm + add_zero (add_zero is `a+0 = a`).
            let cong = self.cong_add(Thm::refl(head.clone())?, rest_eq)?; // ⊢ 0+rest = 0+rest'
            let comm = self.ops.add_ac.comm_at(&head, &rest1)?; // ⊢ 0+rest' = rest'+0
            let az = self.add_zero_at(&rest1)?; // ⊢ rest'+0 = rest'
            return cong.trans(comm)?.trans(az);
        }
        if rest1 == self.ops.zero {
            // head + 0 = head
            let cong = self.cong_add(Thm::refl(head.clone())?, rest_eq)?; // ⊢ head+rest = head+0
            let az = self.add_zero_at(&head)?; // ⊢ head+0 = head
            return cong.trans(az);
        }
        self.cong_add(Thm::refl(head.clone())?, rest_eq)
    }

    // ---- axiom instantiation ----

    fn distrib_l_at(&self, a: &Term, b: &Term, c: &Term) -> Result<Thm> {
        self.ops
            .distrib_l
            .clone()
            .all_elim(a.clone())?
            .all_elim(b.clone())?
            .all_elim(c.clone())
    }
    /// `⊢ (a+b)·c = a·c + b·c` — right distributivity, **derived** on demand
    /// from left distributivity + `mul_comm`:
    /// `(a+b)·c =⟨comm⟩ c·(a+b) =⟨distrib_l⟩ c·a + c·b =⟨comm,comm⟩ a·c + b·c`.
    fn distrib_r_at(&self, a: &Term, b: &Term, c: &Term) -> Result<Thm> {
        let ab = self.ops.add(a.clone(), b.clone())?;
        let s1 = self.mul_comm_at(&ab, c)?; // (a+b)·c = c·(a+b)
        let s2 = self
            .ops
            .distrib_l
            .clone()
            .all_elim(c.clone())?
            .all_elim(a.clone())?
            .all_elim(b.clone())?; // c·(a+b) = c·a + c·b
        let ca = self.mul_comm_at(c, a)?; // c·a = a·c
        let cb = self.mul_comm_at(c, b)?; // c·b = b·c
        let s3 = self.cong_add(ca, cb)?; // c·a + c·b = a·c + b·c
        s1.trans(s2)?.trans(s3)
    }

    fn mul_comm_at(&self, a: &Term, b: &Term) -> Result<Thm> {
        self.ops
            .mul_comm
            .clone()
            .all_elim(a.clone())?
            .all_elim(b.clone())
    }
    fn mul_one_at(&self, a: &Term) -> Result<Thm> {
        self.ops.mul_one.clone().all_elim(a.clone())
    }
    fn mul_zero_at(&self, a: &Term) -> Result<Thm> {
        self.ops.mul_zero.clone().all_elim(a.clone())
    }
    fn add_zero_at(&self, a: &Term) -> Result<Thm> {
        self.ops.add_zero.clone().all_elim(a.clone())
    }

    // ---- congruence ----

    /// `⊢ a₁+b₁ = a₂+b₂` from `⊢ a₁=a₂` and `⊢ b₁=b₂`.
    fn cong_add(&self, a: Thm, b: Thm) -> Result<Thm> {
        a.cong_arg(self.ops.add.clone())?.cong_app(b)
    }
    /// `⊢ a₁·b₁ = a₂·b₂` from `⊢ a₁=a₂` and `⊢ b₁=b₂`.
    fn cong_mul(&self, a: Thm, b: Thm) -> Result<Thm> {
        a.cong_arg(self.ops.mul.clone())?.cong_app(b)
    }
}

/// The RHS of an equational theorem.
fn rhs(thm: &Thm) -> Result<Term> {
    Ok(thm.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone())
}

#[cfg(test)]
mod tests {
    use covalence_hol_eval::mk_int;

    use super::*;
    use crate::init::{int, nat};
    use covalence_core::Type;

    fn nat_ops() -> RingOps {
        RingOps::new(
            nat::nat_add(),
            nat::nat_mul(),
            Term::nat_lit(0u32),
            Term::nat_lit(1u32),
            nat::add_assoc(),
            nat::add_comm(),
            nat::mul_assoc(),
            nat::mul_comm(),
            nat::distrib(),
            nat::mul_one(),
            nat::mul_zero(),
            nat::add_zero(),
        )
    }

    fn v(n: &str) -> Term {
        Term::free(n, Type::nat())
    }
    fn add(a: Term, b: Term) -> Term {
        nat::nat_add().apply(a).unwrap().apply(b).unwrap()
    }
    fn mul(a: Term, b: Term) -> Term {
        nat::nat_mul().apply(a).unwrap().apply(b).unwrap()
    }

    #[test]
    fn distributes_a_product_over_a_sum() {
        let rn = RingNormalizer::new(nat_ops());
        // a·(b + c)  →  a·b + a·c  (as a sorted sum of monomials)
        let e = mul(v("a"), add(v("b"), v("c")));
        let thm = rn.normalize(&e).unwrap();
        let (lhs, _rhs) = thm.concl().as_eq().unwrap();
        assert_eq!(lhs, &e);
        assert!(thm.hyps().is_empty());
        // It must be provably equal to the hand-distributed form.
        let want = add(mul(v("a"), v("b")), mul(v("a"), v("c")));
        assert!(rn.prove_eq(&e, &want).unwrap().hyps().is_empty());
    }

    #[test]
    fn decides_full_distributivity() {
        let rn = RingNormalizer::new(nat_ops());
        // (a + b)·(c + d)  =  a·c + a·d + b·c + b·d
        let lhs = mul(add(v("a"), v("b")), add(v("c"), v("d")));
        let rhs = add(
            add(mul(v("a"), v("c")), mul(v("a"), v("d"))),
            add(mul(v("b"), v("c")), mul(v("b"), v("d"))),
        );
        let thm = rn.prove_eq(&lhs, &rhs).unwrap();
        let (l, r) = thm.concl().as_eq().unwrap();
        assert_eq!(l, &lhs);
        assert_eq!(r, &rhs);
        assert!(thm.hyps().is_empty());
    }

    #[test]
    fn commutativity_and_associativity_are_decided() {
        let rn = RingNormalizer::new(nat_ops());
        // a·b + c   =   c + b·a   (AC of both layers)
        let e1 = add(mul(v("a"), v("b")), v("c"));
        let e2 = add(v("c"), mul(v("b"), v("a")));
        assert!(rn.prove_eq(&e1, &e2).unwrap().hyps().is_empty());
    }

    #[test]
    fn identities_are_simplified() {
        let rn = RingNormalizer::new(nat_ops());
        let one = Term::nat_lit(1u32);
        let zero = Term::nat_lit(0u32);
        // a·1 + 0  =  a
        let e = add(mul(v("a"), one.clone()), zero.clone());
        let thm = rn.normalize(&e).unwrap();
        assert_eq!(thm.concl().as_eq().unwrap().1, &v("a"));
        // 0·a + b  =  b  (annihilation + drop)
        let e2 = add(mul(zero, v("a")), v("b"));
        let thm2 = rn.normalize(&e2).unwrap();
        assert_eq!(thm2.concl().as_eq().unwrap().1, &v("b"));
    }

    #[test]
    fn rejects_non_ring_equal() {
        let rn = RingNormalizer::new(nat_ops());
        // a·(b+c)  ≠  a·b   (missing a·c)
        let e1 = mul(v("a"), add(v("b"), v("c")));
        let e2 = mul(v("a"), v("b"));
        assert!(rn.prove_eq(&e1, &e2).is_err());
    }

    #[test]
    fn runs_against_int_carrier() {
        // The same normalizer over `int` (its ring axioms are genuine theorems).
        let ops = RingOps::new(
            int::int_add(),
            int::int_mul(),
            mk_int(0),
            mk_int(1),
            int::add_assoc(),
            int::add_comm(),
            int::mul_assoc(),
            int::mul_comm(),
            int::distrib(),
            int::mul_one(),
            int::mul_zero(),
            int::add_zero(),
        );
        let rn = RingNormalizer::new(ops);
        let iv = |n: &str| Term::free(n, Type::int());
        let iadd = |a: Term, b: Term| int::int_add().apply(a).unwrap().apply(b).unwrap();
        let imul = |a: Term, b: Term| int::int_mul().apply(a).unwrap().apply(b).unwrap();
        // x·(y + z) = x·y + x·z
        let e1 = imul(iv("x"), iadd(iv("y"), iv("z")));
        let e2 = iadd(imul(iv("x"), iv("y")), imul(iv("x"), iv("z")));
        assert!(rn.prove_eq(&e1, &e2).unwrap().hyps().is_empty());
    }
}
