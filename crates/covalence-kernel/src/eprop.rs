//! Phase P: Prop-as-E-graph (no concl field, user-tracked truth).
//!
//! `EProp` is the proof environment: an [`Egraph`] plus an optional
//! precondition chain. **No concl field** — the egraph IS the
//! conclusion. The kernel does not designate a canonical truth term
//! either; userspace allocates `Bool(true)` (or any other sentinel)
//! itself and passes that `TermRef` into every rule that should mark
//! a pattern as known-true.
//!
//! The user-facing query is [`EThm::eq`]: "are these two TermRefs
//! UF-equal in this Thm's egraph?" Users build the terms they care
//! about, accumulate facts via rule calls on one big Thm, and query
//! equality at the end.
//!
//! Lives alongside the legacy `Prop` / `Thm` indefinitely — both
//! APIs coexist.

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
    pub fn into_inner(self) -> EProp {
        self.0
    }

    /// Promote a fresh `EProp` to an `EThm` without performing any
    /// unions. The result is the trivially-empty Thm: nothing is yet
    /// marked equal beyond the implicit reflexive `t = t` of the UF.
    /// Used as the seed for proof construction.
    pub fn empty(prop: EProp) -> Self {
        Self(prop)
    }

    /// Query the Thm: are `a` and `b` UF-equal at level 0?
    /// This is the primary user-facing operation — "given a Thm and
    /// two terms I care about, does the Thm prove they're equal?"
    pub fn eq(&self, a: TermRef, b: TermRef) -> bool {
        self.0.egraph.uf.eq_at_level_0(a, b)
    }

    /// **Reflexivity (egraph form).** Build `Eq(t, t)` in
    /// `self.prop.egraph` and union it with `truth` in the UF.
    /// The `truth` ref is supplied by the caller — typically a
    /// `Bool(true)` they allocated up front and reuse across rules.
    ///
    /// Returns the `TermRef` of the freshly-built `Eq(t, t)` so the
    /// caller can query this Thm later (e.g.,
    /// `thm.eq(eq_ref, truth)`).
    pub fn refl(&mut self, t: TermId, truth: TermRef) -> Result<TermRef, ProofError> {
        let egraph = &mut self.0.egraph;
        if !egraph.arena.is_well_typed(t) {
            return Err(ProofError::IllTypedInput);
        }
        let eq = egraph
            .arena
            .alloc_term(TermDef::Eq(TermRef::local(t), TermRef::local(t)));
        let eq_ref = TermRef::local(eq);
        egraph
            .uf
            .union(eq_ref, truth)
            .expect("user truth ref must be a local term");
        Ok(eq_ref)
    }
}
