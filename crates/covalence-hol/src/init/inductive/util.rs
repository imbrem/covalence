//! Shared conjunction-proof plumbing for the engine's proof layers
//! ([`super::existence`], [`super::uniqueness`], …).
//!
//! The proofs now live generically over [`super::hol::Hol`]; the functions
//! here are thin [`NativeHol`](super::hol::NativeHol) shims so existing
//! call sites stay unchanged while the engine ports module-by-module. See
//! [`super::hol`].

use covalence_core::{Result, Term, TermKind, Thm};

use super::hol::{self, NativeHol};

/// The binder name carried by a free-variable term (e.g. an image var);
/// falls back to `"__a"` for a non-variable. (Still concrete — a `Term`
/// query, ported when the engine's term-query layer lands.)
pub(super) fn var_name(v: &Term) -> &str {
    match v.kind() {
        TermKind::Free(n, _) => n.as_str(),
        _ => "__a",
    }
}

/// Project conjunct `i` out of a proof of a right-associated conjunction
/// `c₀ ∧ (c₁ ∧ … ∧ c_{k-1})`. [`hol::project`] at [`NativeHol`].
pub(super) fn project(conj: Thm, i: usize, k: usize) -> Result<Thm> {
    hol::project(&NativeHol, conj, i, k)
}

/// `⊢ ⋀ thms` — the right-associated conjunction of the given proofs.
/// [`hol::and_all`] at [`NativeHol`].
pub(super) fn and_all(thms: &[Thm]) -> Result<Thm> {
    hol::and_all(&NativeHol, thms)
}

/// Discharge hypotheses `hyps` from `thm` as a single conjunctive
/// antecedent: `{h₀,…,hₙ} ⊢ c` ↦ `⊢ (⋀ hᵢ) ⟹ c`. [`hol::discharge_conj`]
/// at [`NativeHol`].
pub(super) fn discharge_conj(thm: Thm, hyps: &[Term]) -> Result<Thm> {
    hol::discharge_conj(&NativeHol, thm, hyps)
}
