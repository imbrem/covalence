//! Source-local open work for this module/crate.
//!
//! Migrated from the former Markdown registry. Move markers beside the relevant
//! implementation as the area is touched; `bun run todos` provides the index.

// TODO(cov:kernel.hol.init.src.k.no-builtin-hooks-f1, severe): No builtin hooks (F1): requires conditions over the language's own
// TODO(cov:kernel.hol.init.src.k.guarded-rewriting-is-stratified-sound-incomplete, severe): Guarded rewriting is stratified (sound, incomplete): A requires condition
// TODO(cov:kernel.hol.init.src.k.no-cells-ksequence-heating-cooling, severe): No cells / ~> KSequence / heating-cooling: Only top-level + function-rule
// TODO(cov:kernel.hol.init.src.k.no-substitution-binders, severe): No substitution / binders: LAMBDA's β (E[V/X]) needs a capture-avoiding
// TODO(cov:kernel.hol.init.src.k.first-order-matching-only-leftmost-innermost-deterministic, minor): First-order matching only; leftmost-innermost, deterministic: The
// TODO(cov:kernel.hol.init.src.k.priority-owise-unmodelled, minor): Priority / owise unmodelled: Rule order is taken as-is (the
// TODO(cov:kernel.hol.init.src.k.encoding-covers-only-the-configuration-fragment, minor): Encoding covers only the configuration fragment: encodepattern handles
// TODO(cov:kernel.hol.init.src.k.no-cross-relation-k-claim-consumption, minor): No cross-relation / K-claim consumption: claim reachability sentences
// TODO(cov:kernel.hol.init.src.k.no-k-repl-web-route, minor): No /k REPL / web route: cov k (CLI) exists; the repl-core
