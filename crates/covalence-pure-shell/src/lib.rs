//! Untrusted shell over `covalence-pure`.
//!
//! Provides content hashing and the canonical S-expression syntax for
//! Pure terms, types, and theorems. None of these are consumed by
//! Pure's inference rules; a bug in this crate cannot produce a false
//! `Thm` value.
//!
//! ## Multiple serializers per observer
//!
//! The [`Serializer<O>`](sexp::Serializer) trait decouples the
//! serializer type from the observer type. A user crate with its own
//! `O` can impl `Serializer<O> for ()` to opt in to the default
//! representation, OR impl `Serializer<O>` for a custom `MyFormat`
//! type to use a different wire format. The same `O` can have
//! multiple `Serializer<O>` impls; callers pick which to use.
//!
//! For the trivial observer `()`, Pure-shell provides
//! `Serializer<()> for ()` out of the box: it round-trips through
//! S-expression nil (the empty list).
//!
//! See `docs/design/proposals/stacked-pure-hol/README.md` for the
//! overall trust graph.

pub mod hash;
pub mod sexp;
