//! First-order **matching** — the basic unification behind lemma application
//! (`apply`). One-sided: a `pattern` whose named free variables (the
//! `schematics`) are holes is matched against a ground `target`, yielding the
//! term + type substitutions that make `pattern` equal `target`. Untrusted —
//! every instantiation it suggests is re-checked downstream by `all_elim` /
//! `inst_tfree`, so a wrong match can only fail to apply, never forge a `Thm`.
//!
//! This is deliberately a plain function, reached through [`super::Env`]
//! methods (`apply_unify`), so a richer/pluggable unifier can be registered
//! there later without touching the rules that call it.

use std::collections::{BTreeMap, BTreeSet};

use covalence_core::{Term, TermKind, Type, subst};
use smol_str::SmolStr;

/// A successful match: hole name → witness term, and pattern type-var → type.
#[derive(Default)]
pub(super) struct Subst {
    pub terms: BTreeMap<SmolStr, Term>,
    pub types: BTreeMap<SmolStr, Type>,
}

/// First-order match `pattern` against `target`, extending `out`. `schematics`
/// are the pattern's hole variables (free vars allowed to bind). `Err(())` on
/// mismatch — including an inconsistent re-binding of a hole or type-var.
pub(super) fn match_term(
    pattern: &Term,
    target: &Term,
    schematics: &BTreeSet<SmolStr>,
    out: &mut Subst,
) -> Result<(), ()> {
    use TermKind::*;
    match (pattern.kind(), target.kind()) {
        // A hole — bind it (and its type), or check consistency with a prior binding.
        (Free(v), _) if schematics.contains(v.name()) => {
            subst::match_types(v.ty(), &target.type_of().map_err(|_| ())?, &mut out.types)?;
            match out.terms.get(v.name()) {
                Some(prev) => (prev == target).then_some(()).ok_or(()),
                None => {
                    out.terms.insert(v.name().into(), target.clone());
                    Ok(())
                }
            }
        }
        (App(pf, pa), App(tf, ta)) => {
            match_term(pf, tf, schematics, out)?;
            match_term(pa, ta, schematics, out)
        }
        (Abs(pty, pb), Abs(tty, tb)) => {
            subst::match_types(pty, tty, &mut out.types)?;
            match_term(pb, tb, schematics, out)
        }
        // Typed leaves — names/handles must agree; their types may carry tvars.
        (Free(pv), Free(tv)) if pv.name() == tv.name() => {
            subst::match_types(pv.ty(), tv.ty(), &mut out.types)
        }
        (Const(pn, pty), Const(tn, tty)) if pn == tn => {
            subst::match_types(pty, tty, &mut out.types)
        }
        (Eq(p), Eq(t)) | (Select(p), Select(t)) => subst::match_types(p, t, &mut out.types),
        (Spec(ph, pa), Spec(th, ta)) if ph == th && pa.len() == ta.len() => {
            match_type_args(pa.iter(), ta.iter(), &mut out.types)
        }
        (SpecAbs(ph, pa), SpecAbs(th, ta)) | (SpecRep(ph, pa), SpecRep(th, ta))
            if ph == th && pa.len() == ta.len() =>
        {
            match_type_args(pa.iter(), ta.iter(), &mut out.types)
        }
        // Type-free leaves (Bound, Succ, Bool, Nat/Int/SmallInt/Blob, Obs, Def):
        // require structural equality.
        _ => (pattern == target).then_some(()).ok_or(()),
    }
}

/// Search `target` for the first subterm `pattern` matches — the root, then
/// left-to-right `App` children, **not** under binders (mirroring
/// `rewrite_conv`, which does not descend into `Abs`). Returns the binding that
/// makes them equal. Used by rw-unification to locate where to instantiate an
/// equation's LHS.
pub(super) fn find_match(
    pattern: &Term,
    target: &Term,
    schematics: &BTreeSet<SmolStr>,
) -> Option<Subst> {
    let mut sub = Subst::default();
    if match_term(pattern, target, schematics, &mut sub).is_ok() {
        return Some(sub);
    }
    match target.kind() {
        TermKind::App(f, a) => {
            find_match(pattern, f, schematics).or_else(|| find_match(pattern, a, schematics))
        }
        _ => None,
    }
}

fn match_type_args<'a>(
    p: impl Iterator<Item = &'a Type>,
    t: impl Iterator<Item = &'a Type>,
    sub: &mut BTreeMap<SmolStr, Type>,
) -> Result<(), ()> {
    for (a, b) in p.zip(t) {
        subst::match_types(a, b, sub)?;
    }
    Ok(())
}
