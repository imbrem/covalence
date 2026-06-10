//! `Symbol` trait + `Opacity`.
//!
//! A symbol is the *name* attached to a `TypeSpec` or `TermSpec`.
//! Every symbol has a fixed [`Opacity`] — a Rust-level constant —
//! that decides whether structural equality on specs is allowed
//! to ignore the symbol:
//!
//! - **Transparent**: structural equality on a spec considers only
//!   `ty` and `tm`; two specs with different transparent symbols
//!   but identical definitions compare equal. Use for the kernel's
//!   own derived catalogue ([`Canonical`]) where the symbol is
//!   purely display-side.
//! - **Opaque**: structural equality includes the symbol. Two specs
//!   with the same `ty` / `tm` but different opaque symbols compare
//!   *unequal*. Use for user-named definitions where the name is
//!   meaning-bearing.
//!
//! Opaque symbols compared structurally also fall back to **pointer
//! equality** if the underlying `Symbol::eq` is unsupported or
//! suspect — see the impls. The kernel never calls user-supplied
//! `Eq` / `Hash` / `Ord` impls on a symbol where that would affect
//! soundness; those impls are only used by display + `BTreeSet`
//! internals.
//!
//! [`Canonical`]: super::canonical::Canonical

use std::fmt;
use std::hash::Hash;

/// Whether a symbol's name participates in structural equality on
/// the wrapping `TypeSpec` / `TermSpec`.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Opacity {
    /// Structural equality ignores the symbol — two specs with
    /// equal definitions compare equal regardless of their symbol.
    Transparent,
    /// Structural equality includes the symbol — distinct opaque
    /// symbols make their specs structurally distinct even when
    /// `ty` / `tm` agree.
    Opaque,
}

/// Marker trait for types that can name a `TypeSpec` / `TermSpec`.
///
/// Implementors must:
/// - Be cheap to clone (typically `Arc`-backed or atomic primitive).
/// - Implement `Hash + Eq + Ord` consistently (Rust hash/eq contract).
/// - Pick an [`Opacity`] that's a *constant for the type*, not
///   per-instance — this is enforced by the trait surface
///   (`OPACITY` is an associated const).
///
/// Two builtin impls ship in this module: [`SmolStr`] (opaque, for
/// user-defined names) and [`Canonical`] (transparent, for the
/// kernel's derived catalogue).
pub trait Symbol: Hash + Eq + Ord + Clone + fmt::Debug + Send + Sync + 'static {
    /// The opacity of all symbols of this type. Must be a constant.
    const OPACITY: Opacity;
}

// ---- Builtin impls ----

impl Symbol for smol_str::SmolStr {
    /// User-supplied names are opaque: two distinct names with the
    /// same definition are *not* equal as specs.
    const OPACITY: Opacity = Opacity::Opaque;
}
