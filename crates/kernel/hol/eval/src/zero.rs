//! The EG3a `zero` ↔ `Nat(0)`-literal bridge drivers (untrusted).
//!
//! Stage EG3a of the literal endgame
//! (`notes/vibes/literal-endgame-design.md` § 6,
//! `notes/vibes/tcb-holomega-roadmap.md` Front A) adds the primitive `nat`
//! zero constructor `TermKind::Zero` while the `Nat(0)` literal still
//! exists. The two zeros are distinct `Term`s bridged by ONE transitional
//! eval-tier admitted rule ([`crate::rules::ZeroLitCert`], `⊢ zero = ⌜0⌝`);
//! everything in this module is *derivation* over that bridge plus the
//! ordinary admitted kernel rules — zero additional TCB, it can fail but
//! cannot forge.
//!
//! The core freeness rules keep their literal-stated conclusions until the
//! maintainer-gated EG5 flip (`⊢ ¬(⌜0⌝ = succ n)` for
//! [`covalence_core::Thm::zero_ne_succ`], base instance `p[⌜0⌝/x]` for
//! [`covalence_core::Thm::nat_induct`]): switching them today would break
//! every literal-based induction in `covalence-init`. The `zero`-form facts
//! are DERIVED through the bridge instead — see [`zero_ne_succ_zero`].

use covalence_core::{Error, Result, Term, Type};

use crate::derived::DerivedRules;
use crate::{EvalThm, defs, rules};

/// The bridge equation `⊢ zero = ⌜0⌝` — the primitive `TermKind::Zero`
/// constructor equals the transitional `Nat(0)` literal, as an object-level
/// HOL theorem at the eval tier (one [`rules::ZeroLitCert`] mint).
pub fn zero_eq_lit() -> Result<EvalThm> {
    crate::mint(rules::ZeroLitCert, ()).ok_or(Error::NotReducible)
}

/// `⊢ ¬(zero = succ n)` — the `zero`-form of the kernel freeness rule
/// [`covalence_core::Thm::zero_ne_succ`], derived (zero TCB) by
/// transporting the literal-form conclusion along the bridge:
///
/// 1. `⊢ ¬(⌜0⌝ = succ n)`                          (`zero_ne_succ`)
/// 2. `⊢ ⌜0⌝ = zero`                                (bridge, `sym`)
/// 3. `⊢ (⌜0⌝ = succ n) = (zero = succ n)`          (`refl(=)`/`refl(succ n)`
///    + `mk_comb` congruence over 2)
/// 4. `⊢ ¬(⌜0⌝ = succ n) = ¬(zero = succ n)`        (`refl(¬)` + `mk_comb`)
/// 5. `⊢ ¬(zero = succ n)`                          (`eq_mp` 4, 1)
pub fn zero_ne_succ_zero(n: &Term) -> Result<EvalThm> {
    let lit_form = EvalThm::zero_ne_succ(n.clone())?; // ⊢ ¬(⌜0⌝ = succ n)
    let bridge = zero_eq_lit()?.sym()?; // ⊢ ⌜0⌝ = zero
    let succ_n = Term::app(Term::succ(), n.clone());
    let eq_cong = EvalThm::refl(Term::eq_op(Type::nat()))?
        .mk_comb(bridge)? // ⊢ (= ⌜0⌝) = (= zero)
        .mk_comb(EvalThm::refl(succ_n)?)?; // ⊢ (⌜0⌝ = succ n) = (zero = succ n)
    let not_cong = EvalThm::refl(defs::not())?.mk_comb(eq_cong)?; // ⊢ ¬(…lit…) = ¬(…zero…)
    not_cong.eq_mp(lit_form)
}
