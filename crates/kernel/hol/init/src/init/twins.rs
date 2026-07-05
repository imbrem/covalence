//! The dual-representation bridge for the `defs/` catalogue (toHOL purge S9a).
//!
//! The endgame of the toHOL purge deletes `TermKind::Spec` and the kernel's
//! δ-unfold rule: every catalogue constant becomes an ordinary HOL
//! Light *defined constant* (a `Def` leaf minted by [`Thm::define`]) carrying a
//! stored definitional theorem `⊢ const = body`. This module builds that target
//! representation **alongside** the current `Spec` leaves — the *reversible
//! bridge* — so the flip (S10/S11, maintainer-gated) is a representation swap
//! with no consumer churn.
//!
//! ## What a twin is
//!
//! For each **monomorphic let-style** [`TermSpec`] (a `defs/` entry defined by a
//! direct body — the connectives, the closed nat/int ops, …), [`twin_for`]
//! lazily builds a [`Twin`]:
//!
//! - `const_tm` — a fresh `Def` twin equal to the body, from [`Thm::define`]
//!   (a conservative extension: the `Def`'s only equation is `⊢ const = body`).
//! - `def_thm` — the stored `⊢ const = body`, the *permanent* artifact the flip
//!   hands `delta` once `Spec` leaves are gone.
//! - `spec_eq` — `⊢ Spec(spec, []) = body`, minted **once** through the kernel
//!   δ-unfold rule ([`Thm::unfold_term_spec`]) and cached. This is the *transitional*
//!   artifact `delta` uses while `Spec` leaves still exist; it dies at the flip.
//!
//! The two representations are definitionally interchangeable: `⊢ spec = const`
//! is derivable (`spec_eq.trans(def_thm.sym())`), asserted at build time — the
//! *reversibility* of the bridge.
//!
//! ## Why `delta` routes through here
//!
//! Every δ-unfold consumer ([`TermExt::delta`](super::ext::TermExt::delta),
//! `delta_all`, [`unfold_at_1`](crate::proofs::rewrite::unfold_at_1), the
//! `rel` head-unfold, the `delta` / `unfold-term-spec` script rules) now calls
//! [`unfold_spec`] instead of the kernel δ-unfold rule directly. For a twinned
//! spec it returns the cached `spec_eq`; for anything not yet twinned
//! (polymorphic, def-style ε-selector, or a user-built spec) it falls back to
//! the kernel rule, so nothing breaks. The single kernel-rule
//! call site moves *into* this module (build + fallback); at the flip the
//! twinned path already yields the definitional equation with the consumers
//! unchanged.
//!
//! See [`notes/vibes/defs-rehome-design.md`](../../../../../../notes/vibes/defs-rehome-design.md)
//! for the design decisions (name-collision handling, the def-style plan, and
//! the `TypeSpec` re-home route prototyped by [`unit_typedef`]).

use std::collections::HashMap;
use std::sync::{LazyLock, Mutex};

use covalence_core::defs::TermSpec;
use covalence_core::{Error, Result, Term, Thm, TypeDef};

/// A let-style spec's dual representation: the ordinary-constant twin plus the
/// two stored theorems (the permanent `⊢ const = body` and the transitional
/// `⊢ spec = body`). Cheap to clone (`Arc`-backed kernel data).
#[derive(Clone)]
pub struct Twin {
    /// The fresh ordinary defined-constant twin — a `Def` leaf from
    /// [`Thm::define`], equal to the spec's body.
    pub const_tm: Term,
    /// `⊢ const_tm = body` — the stored definitional theorem (permanent).
    pub def_thm: Thm,
    /// `⊢ Spec(spec, []) = body` — the stored spec-unfolding equation used by
    /// `delta` while `Spec` leaves exist (transitional; dies at the flip).
    pub spec_eq: Thm,
}

/// Process-global twin cache, keyed by the `TermSpec`'s `Arc` pointer identity
/// (stable — the catalogue specs live in `LazyLock`s). Populated lazily at
/// unfold time; the `LazyLock` only builds an empty map, so it cannot re-enter
/// any `defs/` `LazyLock` at init.
static TWINS: LazyLock<Mutex<HashMap<usize, Twin>>> = LazyLock::new(|| Mutex::new(HashMap::new()));

/// Build-or-fetch the [`Twin`] for a **monomorphic let-style** [`TermSpec`].
///
/// Returns `None` — so the caller falls back to the kernel rule — for any spec
/// that is not a monomorphic let-style body: a def-style (ε-selector) spec, a
/// declaration-only spec, or a polymorphic one (its unfolding depends on the
/// type arguments; instantiating the cached equation is deferred, see
/// `SKELETONS.md`).
pub fn twin_for(spec: &TermSpec) -> Result<Option<Twin>> {
    let (Some(ty), Some(body)) = (spec.ty(), spec.tm()) else {
        return Ok(None); // declaration-only spec
    };
    // Polymorphic specs are always used *with* type args (the `spec_eq` below is
    // built at empty args); defer their bridge.
    if !ty.free_tvars().is_empty() {
        return Ok(None);
    }
    // Let-style discriminator — mirrors the kernel `UnfoldTermSpec` rule: the
    // body has the spec's declared type (a def-style `tm` is a `ty → bool`
    // selector predicate instead).
    if body.type_of()? != *ty {
        return Ok(None);
    }

    let key = spec.ptr_id();
    if let Some(twin) = TWINS.lock().unwrap().get(&key) {
        return Ok(Some(twin.clone()));
    }

    // Const twin: a fresh `Def` equal to the body (conservative extension).
    let def_thm = Thm::define(spec.symbol().label(), body.clone())?;
    let const_tm = def_thm
        .concl()
        .as_eq()
        .ok_or(Error::NotAnEquation)?
        .0
        .clone();

    // Transitional spec-unfolding equation, minted once through the kernel rule.
    let spec_leaf = Term::term_spec(spec.clone(), Vec::new());
    let spec_eq = Thm::unfold_term_spec(spec_leaf)?;

    // Reversibility: `⊢ spec = const` is derivable, so the two representations
    // are definitionally interchangeable. (`spec_eq : ⊢ spec = body`,
    // `def_thm.sym() : ⊢ body = const`.)
    spec_eq.clone().trans(def_thm.clone().sym()?)?;

    let twin = Twin {
        const_tm,
        def_thm,
        spec_eq,
    };
    TWINS.lock().unwrap().insert(key, twin.clone());
    Ok(Some(twin))
}

/// δ-unfold a `Spec` leaf's head definition, routed through the [twin
/// registry](twin_for) when the spec is a monomorphic let-style catalogue
/// entry: returns the stored `⊢ t = body` equation. For any spec not yet
/// twinned — polymorphic, def-style, declaration-only, or a non-catalogue user
/// spec — falls back to the kernel δ-unfold rule, so behaviour
/// is unchanged for everything the bridge does not yet cover.
pub fn unfold_spec(t: &Term) -> Result<Thm> {
    if let Some((spec, args)) = t.as_spec()
        && args.is_empty()
        && let Some(twin) = twin_for(spec)?
    {
        return Ok(twin.spec_eq);
    }
    Thm::unfold_term_spec(t.clone())
}

/// **Prototype (S9a):** introduce `unit`'s carrier subtype through the
/// conservative-extension route [`Thm::new_type_definition`] rather than the
/// `TypeSpec` abs/rep laws — the `TypeSpec` analogue of the const-twin bridge
/// above. `unit = { b : bool | b = T }`, witnessed by `⊢ (λb. b = T) T`.
///
/// This is the re-home template for `defs/`'s derived `TypeSpec`s (a fresh τ
/// with `abs`/`rep` and the three bijection theorems, all freshness allocated
/// inside the kernel rule). It is exercised by the test below, not yet wired
/// into the catalogue — that swap is the maintainer-gated flip.
pub fn unit_typedef() -> Result<TypeDef> {
    // P = `λb. b = T` (the unit selector predicate) and the witness `x = T`.
    let p = covalence_core::defs::unit_spec()
        .tm()
        .ok_or(Error::NotAnEquation)?
        .clone();
    let t_lit = Term::bool_lit(true);

    // Build `⊢ (λb. b = T) T` from `⊢ T = T` and the β-equation
    // `⊢ (λb. b = T) T = (T = T)`.
    let redex = Term::app(p, t_lit.clone());
    let beta = Thm::beta_conv(redex)?; // ⊢ (λb. b = T) T = (T = T)
    let refl_tt = Thm::refl(t_lit)?; // ⊢ T = T
    let witness = beta.sym()?.eq_mp(refl_tt)?; // ⊢ (λb. b = T) T

    Thm::new_type_definition("unit", "unit.abs", "unit.rep", witness)
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_core::TermKind;

    /// The monomorphic connectives get a twin whose stored `def_thm` and
    /// transitional `spec_eq` agree on the body, and the bridge `⊢ spec = const`
    /// is derivable (reversibility).
    #[test]
    fn connective_twins_bridge_reversibly() {
        for spec in [
            covalence_core::defs::and_spec(),
            covalence_core::defs::or_spec(),
            covalence_core::defs::imp_spec(),
            covalence_core::defs::not_spec(),
            covalence_core::defs::iff_spec(),
        ] {
            let twin = twin_for(&spec).unwrap().expect("connective is let-style");
            // def_thm : ⊢ const = body ; spec_eq : ⊢ spec = body — same RHS.
            let (const_lhs, def_body) = twin.def_thm.concl().as_eq().unwrap();
            let (spec_lhs, spec_body) = twin.spec_eq.concl().as_eq().unwrap();
            assert_eq!(def_body, spec_body, "twin and spec must share the body");
            assert_eq!(const_lhs, &twin.const_tm);
            // const twin is a fresh Def leaf; spec side is the Spec leaf.
            assert!(matches!(twin.const_tm.kind(), TermKind::Def(_)));
            assert!(matches!(spec_lhs.kind(), TermKind::Spec(_, _)));
            // ⊢ spec = const : the reversible bridge.
            let bridge = twin
                .spec_eq
                .clone()
                .trans(twin.def_thm.sym().unwrap())
                .unwrap();
            let (b_l, b_r) = bridge.concl().as_eq().unwrap();
            assert_eq!(b_l, spec_lhs);
            assert_eq!(b_r, &twin.const_tm);
        }
    }

    /// `unfold_spec` on a twinned spec returns the same equation the kernel rule
    /// would (`⊢ op = body`), so `delta` is behaviourally unchanged.
    #[test]
    fn unfold_spec_matches_kernel_rule() {
        let op = covalence_core::defs::and();
        let via_twin = unfold_spec(&op).unwrap();
        let via_kernel = Thm::unfold_term_spec(op.clone()).unwrap();
        assert_eq!(via_twin.concl(), via_kernel.concl());
    }

    /// A polymorphic spec falls back to the kernel rule (not yet twinned).
    #[test]
    fn polymorphic_spec_falls_back() {
        let spec = covalence_core::defs::forall_spec();
        assert!(twin_for(&spec).unwrap().is_none());
    }

    /// The `unit` TypeSpec re-home prototype: `new_type_definition` yields a
    /// fresh subtype with working bijection theorems.
    #[test]
    fn unit_typedef_prototype() {
        let td = unit_typedef().expect("unit introduced via new_type_definition");
        // abs_rep : ⊢ ∀a:τ. abs (rep a) = a — hypothesis-free (closed witness).
        assert!(td.abs_rep.hyps().is_empty());
        assert!(td.rep_abs_fwd.hyps().is_empty());
        assert!(td.rep_abs_back.hyps().is_empty());
        // τ is a fresh type constructor, distinct from the `defs/` unit spec type.
        assert_ne!(td.tau, covalence_core::Type::unit());
    }
}
