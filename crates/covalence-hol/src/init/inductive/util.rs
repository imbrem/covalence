//! Shared conjunction-proof plumbing for the engine's proof layers
//! ([`super::existence`], [`super::uniqueness`]).

use covalence_core::{Result, Term, TermKind, Thm};

use super::graph;

/// The binder name carried by a free-variable term (e.g. an image var);
/// falls back to `"__a"` for a non-variable.
pub(super) fn var_name(v: &Term) -> &str {
    match v.kind() {
        TermKind::Free(n, _) => n.as_str(),
        _ => "__a",
    }
}

/// Project conjunct `i` out of a proof of a right-associated conjunction
/// `c₀ ∧ (c₁ ∧ … ∧ c_{k-1})`.
pub(super) fn project(conj: Thm, i: usize, k: usize) -> Result<Thm> {
    let mut t = conj;
    for _ in 0..i {
        t = t.and_elim_r()?;
    }
    if i + 1 < k { t.and_elim_l() } else { Ok(t) }
}

/// `⊢ ⋀ thms` — the right-associated conjunction of the given proofs.
/// Caller guarantees a non-empty slice.
pub(super) fn and_all(thms: &[Thm]) -> Result<Thm> {
    let mut acc = thms[thms.len() - 1].clone();
    for t in thms[..thms.len() - 1].iter().rev() {
        acc = t.clone().and_intro(acc)?;
    }
    Ok(acc)
}

/// Discharge hypotheses `hyps` from `thm` as a single conjunctive
/// antecedent: `{h₀,…,hₙ} ⊢ c` ↦ `⊢ (⋀ hᵢ) ⟹ c`. Empty → unchanged;
/// singleton → a plain `imp_intro`.
pub(super) fn discharge_conj(thm: Thm, hyps: &[Term]) -> Result<Thm> {
    match hyps {
        [] => Ok(thm),
        [h] => thm.imp_intro(h),
        _ => {
            // `⊢ hₙ ⟹ … ⟹ h₀ ⟹ c` (all hyps curried off), then cut each
            // back against its projection out of the assumed `⋀ hᵢ`.
            let mut curried = thm;
            for h in hyps {
                curried = curried.imp_intro(h)?;
            }
            let conj_term = graph::conj(hyps)?;
            let assumed = Thm::assume(conj_term.clone())?;
            let mut cut = curried;
            for i in (0..hyps.len()).rev() {
                cut = cut.imp_elim(project(assumed.clone(), i, hyps.len())?)?;
            }
            cut.imp_intro(&conj_term)
        }
    }
}
