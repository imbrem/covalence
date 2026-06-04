//! Phase P: Prop-as-E-graph (no concl field).
//!
//! `EProp` is the proof environment: an [`Egraph`] plus an optional
//! precondition chain. There is **no** concl field — the egraph IS
//! the conclusion. "What an [`EThm`] proves" = any `TermId` in
//! `prop.egraph` whose UF canonical equals `Bool(true)`'s canonical.
//!
//! Inference rules are mutating methods on [`EThm`]: they
//! pattern-match a shape in the egraph (or build it), discharge any
//! side-conditions, and call `uf.union(matched, Bool(true))`.
//!
//! These types live alongside the legacy `Prop` / `Thm` during the
//! Phase P migration. When every rule has been converted (Phase P5)
//! the legacy types are removed and these are renamed to `Prop` /
//! `Thm`.

use std::sync::Arc;

use crate::egraph::Egraph;
use crate::id::TermId;
use crate::prop::ProofError;
use crate::term::{TermDef, TermRef};

/// A proof environment: an E-graph plus an optional precondition.
/// Anyone can construct an `EProp`; the kernel makes no claim about
/// truth. To get a kernel-verified version, use an [`EThm`]
/// constructor.
#[derive(Debug, Clone, Default)]
pub struct EProp {
    pub egraph: Egraph,
    /// Single chained precondition. A chain
    /// `P_n ← P_{n-1} ← … ← None` encodes the assumption set for
    /// `P_n`. Each link is `Arc<EProp>` so weakening and re-export
    /// share structure.
    pub precondition: Option<Arc<EProp>>,
}

impl EProp {
    /// Build an empty Prop — fresh egraph, no precondition.
    pub fn new() -> Self {
        Self::default()
    }

    /// Set the immediate precondition.
    pub fn with_precondition(mut self, pre: Arc<EProp>) -> Self {
        self.precondition = Some(pre);
        self
    }

    /// Walk the precondition chain innermost-first.
    pub fn precondition_chain(&self) -> Vec<Arc<EProp>> {
        let mut out = Vec::new();
        let mut cur = self.precondition.clone();
        while let Some(p) = cur {
            cur = p.precondition.clone();
            out.push(p);
        }
        out
    }

    /// Is `t` UF-equal to the canonical `Bool(true)` in this Prop's
    /// egraph? Lazily ensures the canonical truth ref exists.
    pub fn knows_true(&mut self, t: TermRef) -> bool {
        let truth = self.egraph.true_ref();
        self.egraph.uf.eq_at_level_0(t, truth)
    }
}

/// A kernel-verified `EProp`. Constructible only via the rule
/// methods below.
#[derive(Debug, Clone)]
pub struct EThm(EProp);

impl EThm {
    /// Read-only access to the wrapped [`EProp`].
    pub fn prop(&self) -> &EProp {
        &self.0
    }

    /// Consume the wrapper, returning the underlying [`EProp`].
    /// Untrusted code can construct a new `EProp` and inspect its
    /// state — but it cannot wrap it back into an `EThm` without
    /// going through a rule constructor.
    pub fn into_inner(self) -> EProp {
        self.0
    }

    /// Promote a fresh, vacuously-true `EProp` to an `EThm`. Used as
    /// the seed for proof construction: subsequent rule calls extend
    /// its egraph with derived facts.
    ///
    /// The seed performs the canonical union `Bool(true) =
    /// Bool(true)` (a no-op) so the resulting `EThm` carries at least
    /// the trivially-true fact `⊢ true`.
    pub fn truth(prop: EProp) -> Self {
        let mut prop = prop;
        // Ensure the canonical Bool(true) ref exists; subsequent rule
        // unions against truth land in one equivalence class.
        let _ = prop.egraph.true_ref();
        Self(prop)
    }

    /// **Reflexivity rule (egraph form).** Build `Eq(t, t)` in
    /// `self.prop.egraph` and union it with `Bool(true)` in the UF.
    /// The caller remembers `t` (and the freshly built `Eq` ref if it
    /// needs it) to query truth later.
    ///
    /// Returns the `TermRef` of the freshly-built `Eq(t, t)` so the
    /// caller can pattern-match against this Thm without a separate
    /// search.
    pub fn refl(&mut self, t: TermId) -> Result<TermRef, ProofError> {
        let egraph = &mut self.0.egraph;
        if !egraph.arena.is_well_typed(t) {
            return Err(ProofError::IllTypedInput);
        }
        let eq = egraph
            .arena
            .alloc_term(TermDef::Eq(TermRef::local(t), TermRef::local(t)));
        let eq_ref = TermRef::local(eq);
        let truth = egraph.true_ref();
        egraph
            .uf
            .union(eq_ref, truth)
            .expect("fresh local terms cannot be both-foreign");
        Ok(eq_ref)
    }
}
