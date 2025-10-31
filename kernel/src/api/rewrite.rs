// use crate::api::store::*;
use crate::data::term::*;
use bitflags::bitflags;

pub enum RewriteSide {
    Left,
    Right,
}

pub enum RewriteStep<C, T> {
    // Attempt to complete the goal recursively by congruence
    //
    // This looks through imports, but nothing else
    Congr,
    /// Replace a side with the given node, through a recursive call
    Replace(RewriteSide, NodeVT<C, T>),
    /// Reduce a given side using a given rule
    ///
    /// Place the result in the provided context
    Reduce(RewriteSide, C, ReductionRules),
    /// Swap the LHS and RHS
    Swap,
}

bitflags! {
    pub struct ReductionRules : u16 {
        // == Untyped rules ==

        /// Follow imports
        const IMPORT_FOLLOW = 1 << 0;
        /// Imports are congruent
        const IMPORT_CONGR = 1 << 1;
        /// Closures apply to variables
        const CLOSE_VAR = 1 << 2;
        /// Closures are congruent
        const CLOSE_CONGR = 1 << 3;
        /// Weakenings apply to variables
        const BWK_VAR = 1 << 5;
        /// Weakenings are congruent
        const BWK_CONGR = 1 << 6;
        /// Substitutions apply to variables
        const SUBST_VAR = 1 << 7;
        /// Substitutions are congruent
        const SUBST_CONGR = 1 << 8;

        // == Typed rules ==

        /// Beta-reduce an application
        const BETA_APP = 1 << 9;
        /// Beta-reduce a dependent if-then-else
        const BETA_DITE = 1 << 10;
        /// Beta-reduce natrec at zero
        const BETA_NATREC_ZERO = 1 << 11;
        /// Beta-reduce natrec at succ
        const BETA_NATREC_SUCC = 1 << 12;
        /// Beta-reduce propositions to their normal form
        const BETA_PROP = 1 << 13;
    }
}
