//! The [`Derive`] container trait: the abstraction over "run a rule and bless
//! its output". [`crate::MThm`] is the trusted container; a stricter wrapper
//! (extra checks/bounds) or a looser one can supply its own impl.

/// A kernel container that runs a rule in context `K` and packages the resulting
/// `(K, P)` per the container's discipline.
///
/// [`crate::MThm<K, P>`] implements this for every rule `R` such that
/// `K: `[`crate::Rule`]`<R, P, E>` — that impl *is* the public minting API.
/// Replacing `MThm` with another `Derive` container swaps the kernel discipline
/// (e.g. proof recording, extra checks) without touching any rule.
///
/// `E` is carried as a plain parameter (matching [`crate::Rule`]); an associated
/// error type can be layered on at the untrusted user level later.
pub trait Derive<R, K, P, E>: Sized {
    fn derive(rule: R) -> Result<Self, E>;
}
