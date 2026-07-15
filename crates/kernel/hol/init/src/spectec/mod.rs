//! **The high-level SpecTec-fragment API** — a reusable, trait-based surface
//! over the covalence core for the *universally useful* pieces of a SpecTec
//! specification (`notes/vibes/logics/cfg-stratum-design.md`, the layered-API
//! directive).
//!
//! A SpecTec spec is a set of definitions of a few kinds:
//!
//! | kind | reified as | engine | high-level API |
//! |------|-----------|--------|----------------|
//! | `gram` | CFG `Derives_E n w` | [`crate::grammar::cfg`] (binary engine) | [`GrammarEnv`] |
//! | `rel`/`rule` | `Derivable_R ⌜J⌝` | [`crate::wasm::relation`] (unary engine) | [`RelationEnv`] |
//! | `syntax`/`typ` | reified datatype | [`crate::wasm::syntax`] | *(future)* |
//! | `def` (function) | recursive define | *(todo)* | *(future)* |
//!
//! This module promotes a single **[`Fragment`]** trait to first-class status:
//! a *lowered SpecTec fragment you build kernel-checked derivations in*.
//! [`RelationEnv`] (relations) and [`GrammarEnv`] (grammars) both implement it,
//! so consumers — including the K frontend, which shares the relation engine —
//! drive grammars and operational-semantics relations through one surface.
//!
//! ## Layering (the point)
//!
//! Every trait/method body delegates **strictly downward** to an existing free
//! function ([`crate::wasm::relation`]'s `rule_set`/`derive`, the binary
//! engine's `derive_mixed`, or [`crate::metalogic::apply`]). The trait layer
//! adds **zero** kernel rules and holds no `Thm`-minting logic of its own, so a
//! low-level rewrite (swapping the `Φ = nat` encoding, re-pointing `derive` at
//! `metalogic::apply::apply_rule`, changing the recognizer) leaves this API
//! untouched. Consumers name one crate: `covalence-hol-api` re-exports the whole
//! surface.

use covalence_core::{Result, Term};
use covalence_hol_eval::EvalThm as Thm;

pub mod relation;

pub use relation::RelationEnv;

/// A premise fed to [`Fragment::derive`] — the union of the relation engine's
/// sub-derivations (all [`FragPremise::Derivation`]) and the grammar engine's
/// [`Premise`](crate::metalogic::binary::Premise) (`Side` for a terminal
/// `Matches` leaf, `Derivation` for a non-terminal sub-derivation).
pub enum FragPremise {
    /// A sub-derivation `⊢ <predicate> <j>` (a recursive premise).
    Derivation(Thm),
    /// A side theorem discharged directly (grammar terminal `Matches` leaf).
    Side(Thm),
}

/// A **lowered SpecTec fragment**: a reified definition (a grammar, a relation,
/// …) you can introspect and build derivations in. The common super-trait that
/// unifies [`RelationEnv`] and [`GrammarEnv`](crate::grammar::cfg::GrammarEnv).
pub trait Fragment {
    /// The reified predicate this fragment derives into (`"Derivable_R"` for
    /// relations, `"Derives_E"` for grammars) — provenance/debug only.
    fn judgement_kind(&self) -> &'static str;

    /// The number of closure clauses (rules / productions) — the addressing
    /// space for [`Fragment::derive`]'s `clause_idx`.
    fn n_clauses(&self) -> usize;

    /// **Apply clause `clause_idx`** with reified `args` (metavar / word order)
    /// and `premises`, yielding a hypothesis-free `⊢ <predicate> <j[args]>`.
    ///
    /// This is the one shared derivation-building capability. The kernel
    /// re-checks every step, so a wrong `clause_idx`/`args`/premise fails to
    /// build rather than fabricating a derivation.
    fn derive(&self, clause_idx: usize, args: &[Term], premises: Vec<FragPremise>) -> Result<Thm>;
}

// -- GrammarEnv retrofit: grammars ARE fragments (pure delegation, no behaviour
//    change). Relations get their impl in `relation.rs`. --

use crate::grammar::cfg::GrammarEnv;
use crate::metalogic::binary::Premise as BinPremise;

impl Fragment for GrammarEnv {
    fn judgement_kind(&self) -> &'static str {
        "Derives_E"
    }

    fn n_clauses(&self) -> usize {
        GrammarEnv::n_clauses(self)
    }

    fn derive(&self, clause_idx: usize, args: &[Term], premises: Vec<FragPremise>) -> Result<Thm> {
        let bin: Vec<BinPremise> = premises
            .into_iter()
            .map(|p| match p {
                FragPremise::Side(t) => BinPremise::Side(t),
                FragPremise::Derivation(t) => BinPremise::Derivation(t),
            })
            .collect();
        GrammarEnv::derive(self, clause_idx, args, bin)
    }
}
