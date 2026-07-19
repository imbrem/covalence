//! Embeddings of the deterministic fragment into the two nondeterministic ones.
//!
//! # There is no ordered/relational conversion in either direction
//!
//! `OrderedChoice([p, q])` does not denote `Union([p, q])`: the union admits results of `q`
//! on inputs where `p` matched, which ordered choice never explores. The
//! semantics-preserving image of ordered choice is `Union([p, Seq(Not(p), q)])`, which needs
//! a negation combinator this algebra does not have. In the other direction, collapsing a
//! union to its first result is a policy choice about enumeration order, and this crate does
//! not make policy choices for callers.
//!
//! Neither absence is a missing feature.

use crate::syntax::{Core, Deterministic, Ordered, Relational, Signature};

// TODO(cov:lang.combinator-parsing.negation-fragment, minor): A `Not` combinator would make
// ordered choice expressible in the relational fragment; until then no ordered/relational
// conversion exists in either direction.

// TODO(cov:lang.combinator-parsing.env-coherence-unchecked, major): `deterministic_into_*`
// preserves semantics only when the target environment's rule table and continuation
// resolution are the image of the source environment's. The condition is unchecked; only
// the Rule-free, Bind-free restriction is unconditional.

/// Embed a deterministic program into the ordered fragment.
///
/// **Semantics are preserved only under environment coherence.** This function copies
/// `Rule(i)` indices and `Bind(_, k)` symbols verbatim, but they resolve through the
/// *target* environment. The embedding is semantics-preserving exactly when, for every
/// reachable `i` and `k`,
///
/// ```text
/// ordered_rule(i)       == deterministic_into_ordered(total_rule(i))
/// ordered_resolve(k, v) == deterministic_into_ordered(total_resolve(k, v))
/// ```
///
/// This crate cannot check that condition and does not claim it. Callers who need the
/// unconditional statement should embed `Rule`-free, `Bind`-free programs.
pub fn deterministic_into_ordered<S: Signature>(program: &Deterministic<S>) -> Ordered<S> {
    Ordered::Core(map_core(&program.0, |inner| {
        Box::new(deterministic_into_ordered(inner))
    }))
}

/// Embed a deterministic program into the relational fragment, under the analogous side
/// condition on `relational_rule` and `relational_resolve`.
pub fn deterministic_into_relational<S: Signature>(program: &Deterministic<S>) -> Relational<S> {
    Relational::Core(map_core(&program.0, |inner| {
        Box::new(deterministic_into_relational(inner))
    }))
}

/// Rebuild a core node in a new recursive slot. Symbols are copied verbatim: this function
/// is where the "copied, not translated" part of the side condition above lives.
fn map_core<S: Signature, R>(
    core: &Core<S, Box<Deterministic<S>>>,
    mut embed: impl FnMut(&Deterministic<S>) -> R,
) -> Core<S, R> {
    match core {
        Core::Pure(value) => Core::Pure(value.clone()),
        Core::Prim(primitive) => Core::Prim(primitive.clone()),
        Core::Map(function, inner) => Core::Map(function.clone(), embed(inner)),
        Core::Ap(functions, arguments) => Core::Ap(embed(functions), embed(arguments)),
        Core::Bind(head, continuation) => Core::Bind(embed(head), continuation.clone()),
        Core::Rule(rule) => Core::Rule(*rule),
    }
}
