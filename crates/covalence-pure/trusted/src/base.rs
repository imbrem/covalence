//! The base language `()` — the trivial, empty theory every language inherits.
//!
//! Its manifest is **empty**: it admits no gated rules. What you get "for free" is
//! the always-available builtin `Eqn` methods — the equality calculus
//! (`refl`/`sym`/`trans`/`cong`) and the [bool theory](crate::prop)
//! (`and_*`/`or_*`/`mp`/`internalize`) — none of which are manifest rules. So `()`
//! is what every user implicitly trusts, with nothing per-language to audit.

use std::any::TypeId;

use crate::lang::{LangMeta, Language, Manifest};

static UNIT_MANIFEST: Manifest = Manifest {
    ty: TypeId::of::<()>(),
    extends: &[],
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
    fn union(self, _other: Self) -> Option<Self> {
        Some(())
    }
    const MANIFEST: Option<&'static Manifest> = Some(&UNIT_MANIFEST);
}
