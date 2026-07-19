//! The logic-level seam: combinator syntax and its morphism laws in an object
//! language.
//!
//! Everything the conformance layer does is falsification over a finite corpus.
//! The universal forms of those statements — refinement soundness, union
//! completeness, compilation preserving semantics — are not host results and
//! cannot be minted by evaluation. They belong here, as capabilities a backend
//! supplies. Implementing the syntax trait grants no law.

// SKELETON(cov:lang.combinator-parsing.morphism-theory, minor): CombinatorTheory<L: Logic>
// exposes object-language combinator syntax with no backend realization. The morphism laws
// and the axis-2 translation are checked in the host suite only by falsification over a
// finite corpus. Their universal forms belong here as supplied Result<L::Thm, L::Error>
// capabilities, never mintable by evaluation.

// SKELETON(cov:lang.combinator-parsing.choice-union-refinement-theorem, minor): "Ordered
// choice refines relational union" is a one-way inequation the host suite can only fail to
// falsify. Its universal statement needs quantification over sources AND environments,
// which requires the environment reflected into the object language.

// SKELETON(cov:lang.combinator-parsing.fragment-agreement-theorem, minor): "A deterministic
// program is interpreted identically by all three fragments" is provable only under the
// environment-coherence side condition of the embeddings, which is itself only statable in
// the object language.
