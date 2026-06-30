//! The base language `()` and the first real layer `Bool`.
//!
//! **`()` is the trivial, empty theory** every language inherits: its manifest is
//! **empty** (it admits no gated rules). The "trivial rules" — the equality
//! calculus `refl`/`sym`/`trans`/`cong` — are always-available **methods on
//! [`Eqn`](crate::Eqn)** (ungated framework TCB), *not* manifest entries; so `()`
//! is what every user implicitly trusts, with nothing per-language to audit.
//!
//! **`Bool`** is the first non-trivial layer: the theory of the boolean sort —
//! the connectives `And`/`Or`/`Imp`/`Not` as ops-that-are-[`CanonRule`]s, plus the
//! trusted equality on `bool`. It inherits `()` and has a non-empty manifest.
//! (Quantifiers bind variables, so they are not here — they arrive with HOL.)

use std::any::TypeId;

use crate::eqn::TeqRule;
use crate::lang::{CanonRule, LangMeta, Language, Manifest, RuleMeta, RuleRecord};
use crate::op::Op;
use crate::teq::TrustedEq;

// ---- The base language `()`: empty, trivial, implicitly trusted ----

static UNIT_MANIFEST: Manifest = Manifest {
    ty: TypeId::of::<()>(),
    extends: &[],
    // EMPTY: the equality calculus is ungated `Eqn` methods, not admitted rules.
    admits: &[],
    metadata: LangMeta,
};

impl Language for () {
    fn admits(&self, _rule: TypeId) -> bool {
        false
    }
    fn extends(&self, _parent: TypeId) -> bool {
        false
    }
    const MANIFEST: Option<&'static Manifest> = Some(&UNIT_MANIFEST);
}

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

// ---- `Bool`: the theory of the boolean sort (inherits `()`) ----

/// The theory of the `bool` sort: the propositional connectives as canonical-eval
/// rules, plus native `bool` equality. The first language with a non-empty
/// manifest; everything that reasons about booleans inherits it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Bool;

/// `Bool` is a stateless (ZST) language value ⇒ all values equal (for the `trans`
/// "same context" check).
impl TrustedEq for Bool {
    fn teq(&self, _other: &Self) -> bool {
        true
    }
}

static BOOL_MANIFEST: Manifest = Manifest {
    ty: TypeId::of::<Bool>(),
    // Parent `()`'s manifest is empty; embedding it by value is the macro's job.
    // `extends()` (the function) is the authoritative `lift` gate and names `()`.
    extends: &[],
    admits: &[
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

impl Language for Bool {
    fn admits(&self, rule: TypeId) -> bool {
        BOOL_MANIFEST.admits.iter().any(|r| r.ty == rule)
    }
    fn extends(&self, parent: TypeId) -> bool {
        parent == TypeId::of::<()>()
    }
    const MANIFEST: Option<&'static Manifest> = Some(&BOOL_MANIFEST);
}
