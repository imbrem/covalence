//! **Derived** point-free theorems — proved generically against the
//! [`Monoidal`] trait, using *only* its axioms and inference rules.
//!
//! This is the payoff of the abstraction: a routine written here runs
//! against *any* [`Monoidal`] model (the shallow HOL one today, a deep
//! proof-term one later), and never touches HOL internals. It is the
//! coproduct analogue of writing generic PA derivations against
//! [`Peano`](crate::peano::Peano).
//!
//! The headline results — [`copair_unique`] (extensionality for maps out
//! of `⊕`) and [`swap_involution`] (`σ ∘ σ = id`, the symmetry is its own
//! inverse) — show that the symmetric-monoidal coherence facts follow
//! from the β/η laws plus the category laws alone.

use crate::monoidal::{Category, Monoidal};

type P<M> = Result<<M as Category>::Proof, <M as Category>::Error>;

/// **Extensionality / uniqueness for the copairing.** Given `lhs`, `rhs :
/// a ⊕ b → c` that agree after pre-composition with each injection —
/// `on_inl : ⊢ lhs ∘ inl = rhs ∘ inl` and `on_inr : ⊢ lhs ∘ inr = rhs ∘
/// inr` — conclude `⊢ lhs = rhs`.
///
/// This is the most useful *derived* rule: it reduces any equation
/// between maps out of a coproduct to two equations on the summands.
/// Proof: fuse both sides (`m = [m∘inl, m∘inr]`) and rewrite the
/// copairing with the two hypotheses.
pub fn copair_unique<M: Monoidal>(
    m: &M,
    lhs: M::Hom,
    rhs: M::Hom,
    on_inl: M::Proof,
    on_inr: M::Proof,
) -> P<M> {
    let fl = m.fusion(lhs)?; // ⊢ lhs = [lhs∘inl, lhs∘inr]
    let fr = m.fusion(rhs)?; // ⊢ rhs = [rhs∘inl, rhs∘inr]
    let mid = m.copair_cong(on_inl, on_inr)?; // ⊢ [lhs∘inl,…] = [rhs∘inl,…]
    m.trans(m.trans(fl, mid)?, m.sym(fr)?)
}

/// `⊢ σ ∘ inl = inr` — the symmetry sends the left injection to the right
/// one. (`σ = [inr, inl]`, so this is just the left β-law.)
pub fn swap_inl<M: Monoidal>(m: &M, a: M::Obj, b: M::Obj) -> P<M> {
    m.copair_inl(m.inr(b.clone(), a.clone()), m.inl(b, a))
}

/// `⊢ σ ∘ inr = inl` — the symmetry sends the right injection to the left
/// one.
pub fn swap_inr<M: Monoidal>(m: &M, a: M::Obj, b: M::Obj) -> P<M> {
    m.copair_inr(m.inr(b.clone(), a.clone()), m.inl(b, a))
}

/// `⊢ ∇ ∘ inl = id` — the codiagonal collapses the left injection.
/// (`∇ = [id, id]`, so again the left β-law.)
pub fn codiag_inl<M: Monoidal>(m: &M, a: M::Obj) -> P<M> {
    m.copair_inl(m.id(a.clone()), m.id(a))
}

/// **The symmetry is an involution:** `⊢ σ_{b,a} ∘ σ_{a,b} = id_{a⊕b}`.
///
/// Proved point-free from the structure alone: by [`copair_unique`] it
/// suffices to check both injections, and on each the chain
/// `(σ' ∘ σ) ∘ inl = σ' ∘ (σ ∘ inl) = σ' ∘ inr = inl = id ∘ inl`
/// is just associativity + the swap β-laws + the left identity.
pub fn swap_involution<M: Monoidal>(m: &M, a: M::Obj, b: M::Obj) -> P<M> {
    let swap1 = m.swap(a.clone(), b.clone())?; // a⊕b → b⊕a
    let swap2 = m.swap(b.clone(), a.clone())?; // b⊕a → a⊕b
    let comp = m.comp(swap2.clone(), swap1.clone())?; // a⊕b → a⊕b
    let id = m.id(m.oplus(a.clone(), b.clone()));

    // on_inl: ⊢ (σ'∘σ)∘inl = id∘inl.
    let on_inl = {
        let inl_ab = m.inl(a.clone(), b.clone());
        let assoc = m.assoc(swap2.clone(), swap1.clone(), inl_ab.clone())?;
        let cong = m.comp_cong(m.refl(swap2.clone())?, swap_inl(m, a.clone(), b.clone())?)?;
        let s2_inr = swap_inr(m, b.clone(), a.clone())?; // σ'∘inr = inl_ab
        let chain = m.trans(m.trans(assoc, cong)?, s2_inr)?; // (σ'∘σ)∘inl = inl_ab
        m.trans(chain, m.sym(m.id_left(inl_ab)?)?)?
    };
    // on_inr: ⊢ (σ'∘σ)∘inr = id∘inr.
    let on_inr = {
        let inr_ab = m.inr(a.clone(), b.clone());
        let assoc = m.assoc(swap2.clone(), swap1.clone(), inr_ab.clone())?;
        let cong = m.comp_cong(m.refl(swap2.clone())?, swap_inr(m, a.clone(), b.clone())?)?;
        let s2_inl = swap_inl(m, b.clone(), a.clone())?; // σ'∘inl = inr_ab
        let chain = m.trans(m.trans(assoc, cong)?, s2_inl)?; // (σ'∘σ)∘inr = inr_ab
        m.trans(chain, m.sym(m.id_left(inr_ab)?)?)?
    };
    copair_unique(m, comp, id, on_inl, on_inr)
}
