//! Source-local open work for the HOL core.
//!
//! Keep these markers beside the relevant implementation as it is touched;
//! `bun run todos` provides the global index.

// TODO(cov:kernel.hol.core.remove-defs-residue, severe): Remove the transitional defs catalogue after literal leaves no longer force its type chain.
// PERF(cov:kernel.hol.core.default-hash-consing, severe): Thread one hash-consing context end-to-end through builders, rules, and replay.
// TODO(cov:kernel.hol.core.move-name-close, major): Move name-only subst::close out of the trusted core and migrate callers to typed close_var.
// TODO(cov:kernel.hol.core.subst-property-coverage, minor): Extend substitution generators and independent reference-model property tests.
// TODO(cov:kernel.hol.core.rule-panic-coverage, minor): Exercise every theorem rule constructor in panic-envelope tests.
// PERF(cov:kernel.hol.core.construct-with-interner, major): Thread the interner through theorem construction instead of interning conclusions post-hoc.
