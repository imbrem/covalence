//! The base language `()` — the root every language conceptually inherits.
//!
//! `impl Language for ()` bundles what you get "for free": the **equality
//! calculus** (`refl`/`sym`/`trans`/`cong_*`, which are framework-level and
//! ungated, but enumerated here so they show up in every tree's TCB) and
//! **propositional logic** (`And`/`Or`/`Not`/`Imp` as ops-that-are-`CanonRule`s).
//!
//! Quantifiers bind variables, so they are *not* here — they arrive with HOL.

use std::any::TypeId;

use crate::eqn::TeqRule;
use crate::lang::{CanonRule, LangMeta, Language, Manifest, RuleMeta, RuleRecord};
use crate::op::Op;
use crate::teq::TrustedEq;

// ---- Equality-calculus markers (ungated framework rules; enumerated for TCB) ----

/// Reflexivity marker (`Eqn::refl`).
pub struct Refl;
/// Symmetry marker (`Eqn::sym`).
pub struct Sym;
/// Transitivity marker (`Eqn::trans`).
pub struct Trans;
/// Congruence marker (`Eqn::cong_app` / `Eqn::cong_pair`).
pub struct Cong;

// ---- Propositional connectives: ops that are also their own canonical rule ----

macro_rules! zst_op {
    ($(#[$m:meta])* $name:ident, $in:ty, $out:ty) => {
        $(#[$m])*
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub struct $name;
        impl Op for $name { type In = $in; type Out = $out; }
        // ZST carries no data ⇒ same type ⟹ same operator (sound, complete).
        impl TrustedEq for $name { fn teq(&self, _other: &Self) -> bool { true } }
    };
}

zst_op!(
    /// Conjunction `(bool, bool) → bool`.
    And, (bool, bool), bool
);
zst_op!(
    /// Disjunction `(bool, bool) → bool`.
    Or, (bool, bool), bool
);
zst_op!(
    /// Implication `(bool, bool) → bool`.
    Imp, (bool, bool), bool
);
zst_op!(
    /// Negation `bool → bool`.
    Not, bool, bool
);

impl CanonRule for And {
    fn eval(&self, arg: &(bool, bool)) -> bool {
        arg.0 && arg.1
    }
}
impl CanonRule for Or {
    fn eval(&self, arg: &(bool, bool)) -> bool {
        arg.0 || arg.1
    }
}
impl CanonRule for Imp {
    fn eval(&self, arg: &(bool, bool)) -> bool {
        !arg.0 || arg.1
    }
}
impl CanonRule for Not {
    fn eval(&self, arg: &bool) -> bool {
        !arg
    }
}

// ---- The base language `()` ----

/// `()`'s static TCB manifest. Lists the (framework-level) equality calculus, the
/// propositional connectives, and the trusted-equality leaf for `bool`. The
/// `admits`/`extends` impls are derived from these same lists so they cannot drift.
static BASE_MANIFEST: Manifest = Manifest {
    ty: TypeId::of::<()>(),
    extends: &[],
    admits: &[
        RuleRecord {
            ty: TypeId::of::<Refl>(),
            metadata: RuleMeta,
        },
        RuleRecord {
            ty: TypeId::of::<Sym>(),
            metadata: RuleMeta,
        },
        RuleRecord {
            ty: TypeId::of::<Trans>(),
            metadata: RuleMeta,
        },
        RuleRecord {
            ty: TypeId::of::<Cong>(),
            metadata: RuleMeta,
        },
        RuleRecord {
            ty: TypeId::of::<And>(),
            metadata: RuleMeta,
        },
        RuleRecord {
            ty: TypeId::of::<Or>(),
            metadata: RuleMeta,
        },
        RuleRecord {
            ty: TypeId::of::<Imp>(),
            metadata: RuleMeta,
        },
        RuleRecord {
            ty: TypeId::of::<Not>(),
            metadata: RuleMeta,
        },
        RuleRecord {
            ty: TypeId::of::<TeqRule<bool>>(),
            metadata: RuleMeta,
        },
    ],
    metadata: LangMeta,
};

impl Language for () {
    fn admits(&self, rule: TypeId) -> bool {
        BASE_MANIFEST.admits.iter().any(|r| r.ty == rule)
    }
    fn extends(&self, _parent: TypeId) -> bool {
        // The base has no parents.
        false
    }
    const MANIFEST: Option<&'static Manifest> = Some(&BASE_MANIFEST);
}
