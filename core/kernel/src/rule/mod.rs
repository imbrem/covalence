/// Deduction rules for the `covalence` kernel
pub mod ensure;

/// Derivation rules for the `covalence` kernel
pub mod derive;

/// Rules for unfolding substitutions, imports, and closures
mod unfold;

/// Predicates which can be inferred from subterms
mod pred;
