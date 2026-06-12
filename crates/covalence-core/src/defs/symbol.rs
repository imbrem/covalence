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

/// Whether a symbol's name participates in structural equality on
/// the wrapping `TypeSpec` / `TermSpec`.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Opacity {
    /// Structural equality ignores the symbol.
    Transparent,
    /// Structural equality includes the symbol (compared by label
    /// and `Arc` identity).
    Opaque,
}

/// Object-safe trait for things that can name a spec.
///
/// Implementors supply (a) the opacity of the *type* — same value
/// for every instance — and (b) a display/serialisation label. The
/// kernel never relies on user-supplied `Hash`/`Eq`/`Ord` for
/// soundness; for structural equality on specs we hash on the label
/// (opaque) or skip the symbol entirely (transparent).
pub trait Symbol: fmt::Debug + Send + Sync + 'static {
    /// The opacity of this symbol type. Implementors should return
    /// the same value for every instance.
    fn opacity(&self) -> Opacity;
    /// Human-readable label, used by `Display`, S-exp serialisation,
    /// and content hashing.
    fn label(&self) -> &str;
}

impl Symbol for smol_str::SmolStr {
    fn opacity(&self) -> Opacity {
        Opacity::Opaque
    }
    fn label(&self) -> &str {
        self.as_str()
    }
}
