//! Operation symbols.

/// An operation symbol `In → Out`. May carry data (the impl type's fields).
/// `In`/`Out` are plain types — **sorts need no trait**; any Rust type becomes a
/// sort the moment it is wrapped in [`crate::Val`]. Relations are ops with
/// `Out = bool`.
///
/// `Op` says nothing about *evaluation*: writing `App<F, _>` is always sound
/// (uninterpreted ⇒ inert). Evaluation arrives separately via
/// [`crate::CanonRule`], and is gated by a language's manifest.
pub trait Op {
    /// The argument sort.
    type In;
    /// The result sort.
    type Out;
}
