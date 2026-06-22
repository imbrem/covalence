//! `Symbol` (untrusted names) + the sealed `TrustedCmp` marker +
//! `SymbolRef` (how a spec stores and compares its name).
//!
//! A symbol is the *name* attached to a [`crate::ty::TypeSpec`] or
//! [`crate::term::TermSpec`]. Symbol identity is purely an
//! opacity/efficiency token — it **never** affects soundness (a spec's
//! meaning is its `ty`/`tm`, not its name). So the only question a symbol
//! has to answer is: *when are two names "the same"?* and that has two
//! regimes:
//!
//! - **Trusted** symbols ([`TrustedCmp`]): the type's own value-based
//!   comparison — taken here as comparison by [`Symbol::label`] — is a
//!   deterministic, reflexive equality the kernel can use directly. The
//!   built-in name types ([`smol_str::SmolStr`], [`String`], the kernel's
//!   own [`Canonical`] catalogue) are trusted, so two `SmolStr("foo")`
//!   symbols compare equal regardless of which `Arc` holds them.
//!   `TrustedCmp` is **sealed**: downstream code cannot assert that its
//!   own comparison is trustworthy.
//!
//! - **Untrusted** symbols: an arbitrary `Symbol` implementor whose
//!   `label()` (and any notion of equality) we will not vouch for.
//!   [`SymbolRef::untrusted`] wraps one and compares it **by `Arc`
//!   pointer** — trivially deterministic and reflexive for the lifetime
//!   of the handle — so a buggy or adversarial `label()` cannot make two
//!   distinct names collide.
//!
//! [`Canonical`]: super::canonical::Canonical

use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

/// Object-safe trait for things that can name a spec. Public and
/// **untrusted** — anyone may implement it. By itself it grants no
/// trusted comparison; see [`TrustedCmp`] / [`SymbolRef`].
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

impl Symbol for String {
    fn label(&self) -> &str {
        self.as_str()
    }
}

impl Symbol for &'static str {
    fn label(&self) -> &str {
        self
    }
}

// ============================================================================
// TrustedCmp — sealed marker: this name type's value-comparison is trusted
// ============================================================================

pub(crate) mod sealed {
    /// Seals [`super::TrustedCmp`] to kernel-blessed name types.
    pub trait Sealed {}
}

/// Sealed marker: implementors promise that their `Eq`/`Ord` (and, for a
/// [`Symbol`], comparison by [`Symbol::label`]) is a **deterministic,
/// reflexive** equality and total order for the lifetime of the value — so
/// the kernel may use it directly instead of falling back to pointer
/// identity.
///
/// This is deliberately *independent* of [`Symbol`]: it marks comparison
/// trust, not naming. The "a name whose comparison is trusted" bundle is
/// [`TrustedSymbol`] (= `Symbol + TrustedCmp`).
///
/// `Soundness:` this only governs *opacity*, never logical soundness — a
/// wrong `TrustedCmp` could at worst make two distinct spec names alias
/// (or fail to), which changes nothing about what a spec denotes. The
/// trait is sealed for hygiene, not safety.
pub trait TrustedCmp: sealed::Sealed {}

impl sealed::Sealed for smol_str::SmolStr {}
impl TrustedCmp for smol_str::SmolStr {}

impl sealed::Sealed for String {}
impl TrustedCmp for String {}

impl sealed::Sealed for &'static str {}
impl TrustedCmp for &'static str {}

/// A [`Symbol`] whose comparison is trusted (`Symbol + TrustedCmp`).
/// Blanket-implemented; this is the bound the spec constructors use for
/// their by-value comparison path ([`SymbolRef::trusted`]).
pub trait TrustedSymbol: Symbol + TrustedCmp {}

impl<S: Symbol + TrustedCmp> TrustedSymbol for S {}

// ============================================================================
// SymbolRef — the stored, comparable handle
// ============================================================================

/// A spec's stored name: an `Arc<dyn Symbol>` tagged with whether its
/// comparison is trusted.
///
/// `Eq`/`Ord`/`Hash`:
/// - **trusted vs. trusted** — compare by [`Symbol::label`];
/// - **untrusted vs. untrusted** — compare by `Arc` pointer address;
/// - **mixed** — never equal; trusted orders before untrusted.
#[derive(Clone)]
pub struct SymbolRef {
    inner: Arc<dyn Symbol>,
    trusted: bool,
}

impl SymbolRef {
    /// Wrap a trusted name (compared by `label()`).
    pub fn trusted<S: TrustedSymbol>(symbol: S) -> Self {
        SymbolRef {
            inner: Arc::new(symbol),
            trusted: true,
        }
    }

    /// Wrap an untrusted name (compared by `Arc` pointer identity).
    pub fn untrusted<S: Symbol>(symbol: S) -> Self {
        SymbolRef {
            inner: Arc::new(symbol),
            trusted: false,
        }
    }

    /// The underlying symbol; call `.label()` for display / serialisation.
    pub fn symbol(&self) -> &dyn Symbol {
        &*self.inner
    }

    /// The display label.
    pub fn label(&self) -> &str {
        self.inner.label()
    }

    /// Whether this name is compared by value (`true`) or by pointer
    /// (`false`).
    pub fn is_trusted(&self) -> bool {
        self.trusted
    }

    /// The `Arc` data address (used for untrusted comparison).
    fn addr(&self) -> usize {
        Arc::as_ptr(&self.inner) as *const () as usize
    }
}

impl fmt::Debug for SymbolRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.inner.label())
    }
}

impl PartialEq for SymbolRef {
    fn eq(&self, other: &Self) -> bool {
        match (self.trusted, other.trusted) {
            (true, true) => self.inner.label() == other.inner.label(),
            (false, false) => self.addr() == other.addr(),
            _ => false,
        }
    }
}

impl Eq for SymbolRef {}

impl Ord for SymbolRef {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self.trusted, other.trusted) {
            (true, true) => self.inner.label().cmp(other.inner.label()),
            (false, false) => self.addr().cmp(&other.addr()),
            // Trusted names sort before untrusted ones; never equal.
            (true, false) => Ordering::Less,
            (false, true) => Ordering::Greater,
        }
    }
}

impl PartialOrd for SymbolRef {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Hash for SymbolRef {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.trusted.hash(state);
        if self.trusted {
            self.inner.label().hash(state);
        } else {
            self.addr().hash(state);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::hash_map::DefaultHasher;

    fn hash_of(s: &SymbolRef) -> u64 {
        let mut h = DefaultHasher::new();
        s.hash(&mut h);
        h.finish()
    }

    #[test]
    fn trusted_symbols_compare_by_label() {
        // Distinct allocations, same label → equal (and hash-equal).
        let a = SymbolRef::trusted(smol_str::SmolStr::from("foo"));
        let b = SymbolRef::trusted(smol_str::SmolStr::from("foo"));
        assert_eq!(a, b);
        assert_eq!(hash_of(&a), hash_of(&b));

        let c = SymbolRef::trusted(smol_str::SmolStr::from("bar"));
        assert_ne!(a, c);
        assert_eq!(a.cmp(&c), "foo".cmp("bar"));
    }

    #[test]
    fn trusted_symbols_compare_across_types_by_label() {
        // A `String` and a `SmolStr` with the same label are both trusted
        // and compare equal.
        let a = SymbolRef::trusted(String::from("foo"));
        let b = SymbolRef::trusted(smol_str::SmolStr::from("foo"));
        assert_eq!(a, b);
    }

    #[test]
    fn untrusted_symbols_compare_by_pointer() {
        // Same label, but untrusted → distinct allocations are unequal.
        let a = SymbolRef::untrusted(smol_str::SmolStr::from("foo"));
        let b = SymbolRef::untrusted(smol_str::SmolStr::from("foo"));
        assert_ne!(a, b);
        // A clone shares the Arc, so it *is* equal.
        let a2 = a.clone();
        assert_eq!(a, a2);
        assert_eq!(hash_of(&a), hash_of(&a2));
    }

    #[test]
    fn trusted_and_untrusted_never_equal_and_trusted_orders_first() {
        let t = SymbolRef::trusted(smol_str::SmolStr::from("foo"));
        let u = SymbolRef::untrusted(smol_str::SmolStr::from("foo"));
        assert_ne!(t, u);
        assert_eq!(t.cmp(&u), Ordering::Less);
        assert_eq!(u.cmp(&t), Ordering::Greater);
        assert!(t.is_trusted());
        assert!(!u.is_trusted());
    }
}
