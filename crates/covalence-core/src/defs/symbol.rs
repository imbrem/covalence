//! `Symbol` trait + `Opacity`.
//!
//! A symbol is the *name* attached to a `TypeSpec` or `TermSpec`.
//! Every symbol type has a fixed [`Opacity`] that decides whether
//! structural equality on the wrapping spec considers the symbol:
//!
//! - **Transparent**: structural equality on a spec considers only
//!   `ty` and `tm`; two specs with different transparent symbols but
//!   identical definitions compare equal. Use for the kernel's own
//!   derived catalogue ([`Canonical`]) where the symbol is purely
//!   display-side.
//! - **Opaque**: structural equality includes the symbol. Two specs
//!   with the same `ty` / `tm` but different opaque symbols compare
//!   *unequal*. Use for user-named definitions where the name is
//!   meaning-bearing.
//!
//! `Symbol` is **object-safe** — `TypeSpec`/`TermSpec` store an
//! `Arc<dyn Symbol>`, so a single spec type can carry either a
//! kernel [`Canonical`] symbol or a user-supplied opaque name.
//!
//! [`Canonical`]: super::canonical::Canonical

use std::fmt;
use std::hash::Hash;

/// Object-safe trait for things that can name a spec.
pub trait Symbol: fmt::Debug + Send + Sync + 'static {
    /// Human-readable label, used by `Display`, S-exp serialisation,
    /// and content hashing.
    fn label(&self) -> &str;
}

impl Symbol for smol_str::SmolStr {
    fn label(&self) -> &str {
        self.as_str()
    }
}

// ============================================================================
// Symbol comparison / hash helpers (shared by `TypeSpec` / `TermSpec`)
// ============================================================================

/// Structural equality of two `dyn Symbol`s.
pub(crate) fn symbol_eq(a: &dyn Symbol, b: &dyn Symbol) -> bool {
    // TODO: generalize
    std::ptr::addr_eq(a, b)
}

pub(crate) fn symbol_cmp(a: &dyn Symbol, b: &dyn Symbol) -> std::cmp::Ordering {
    // TODO: generalize
    (a as *const dyn Symbol)
        .cast::<()>()
        .cmp(&(b as *const dyn Symbol).cast::<()>())
}

pub(crate) fn symbol_hash<H: std::hash::Hasher>(s: &dyn Symbol, state: &mut H) {
    // TODO: generalize
    s.label().hash(state)
}
