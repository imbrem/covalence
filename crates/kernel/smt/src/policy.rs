//! **Rule-acceptance policy** — the "accept only a subset of Alethe" knob.
//!
//! A backend, or a caller who wants to bound what it trusts to replay, declares
//! which *classes* of Alethe rules it will admit. Anything outside the policy is
//! refused up front with a structured reason, rather than attempted and failed
//! deep inside the dispatcher. This is what lets:
//!
//! - a QF_UF-only backend reject arithmetic cleanly;
//! - a logic that has no subproof story (an early internal-PA backend) reject
//!   `anchor`/`subproof` without touching them;
//! - coverage grow one family at a time, with the policy as the ratchet.
//!
//! The classification is by rule name (Alethe rule names are stable). It is
//! deliberately coarse; a policy can additionally allow/deny individual rule
//! names on top of the class filter.

use std::collections::BTreeSet;

/// A coarse family an Alethe rule belongs to.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum RuleClass {
    /// `assume` — introduce an asserted hypothesis.
    Assume,
    /// Resolution / clausification (`resolution`, `th_resolution`, `or`, …).
    Resolution,
    /// Boolean-connective CNF rules (`and`, `and_intro`, `not_not`, `implies`,
    /// `equiv*`, `ite*`, `contraction`, `tautology`, …).
    Propositional,
    /// Equality & congruence (`refl`, `trans`, `symm`, `cong`, `eq_*`).
    Equality,
    /// Linear arithmetic (`la_generic`, `la_mult_pos`/`_neg`, `la_disequality`,
    /// `la_totality`, `la_tautology`, `la_rw_eq`).
    LinearArith,
    /// Evaluation / rewriting of closed or definitional terms (`evaluate`,
    /// `hole`, `equiv_simplify`, `*_simplify`, `rare_rewrite`).
    Rewrite,
    /// Subproof machinery (`subproof`, `bind`, `let`, `sko_ex`, `sko_forall`,
    /// `onepoint`) — steps that require an open `anchor` scope.
    Subproof,
    /// Anything not classified above.
    Other,
}

/// Classify an Alethe rule name into its [`RuleClass`].
pub fn classify(rule: &str) -> RuleClass {
    match rule {
        "assume" => RuleClass::Assume,
        "resolution" | "th_resolution" | "or" | "or_pos" | "or_neg" => RuleClass::Resolution,
        "refl" | "trans" | "symm" | "cong" | "eq_reflexive" | "eq_transitive" | "eq_symmetric"
        | "eq_congruent" | "eq_congruent_pred" => RuleClass::Equality,
        "subproof" | "bind" | "let" | "sko_ex" | "sko_forall" | "onepoint" => RuleClass::Subproof,
        "hole" | "evaluate" | "equiv_simplify" | "rare_rewrite" => RuleClass::Rewrite,
        _ if rule.starts_with("la_") => RuleClass::LinearArith,
        _ if rule.ends_with("_simplify") => RuleClass::Rewrite,
        // The bulk CNF / connective family.
        "and" | "and_intro" | "and_pos" | "and_neg" | "not_not" | "implies" | "implies_pos"
        | "implies_neg" | "equiv1" | "equiv2" | "equiv_pos1" | "equiv_pos2" | "equiv_neg1"
        | "equiv_neg2" | "not_and" | "not_or" | "not_implies1" | "not_implies2" | "contraction"
        | "tautology" | "false" | "true" | "ite1" | "ite2" | "ite_pos1" | "ite_pos2"
        | "ite_neg1" | "ite_neg2" | "comp_simplify" => RuleClass::Propositional,
        _ => RuleClass::Other,
    }
}

/// A set of admitted rule classes, with optional per-name overrides.
#[derive(Clone, Debug)]
pub struct RulePolicy {
    classes: BTreeSet<RuleClass>,
    /// Rule names always accepted, regardless of class.
    allow: BTreeSet<String>,
    /// Rule names always rejected, regardless of class.
    deny: BTreeSet<String>,
}

impl RulePolicy {
    /// A policy admitting exactly the given classes ([`RuleClass::Assume`] is
    /// always included — a proof cannot start without it).
    pub fn classes(classes: impl IntoIterator<Item = RuleClass>) -> Self {
        let mut classes: BTreeSet<_> = classes.into_iter().collect();
        classes.insert(RuleClass::Assume);
        RulePolicy {
            classes,
            allow: BTreeSet::new(),
            deny: BTreeSet::new(),
        }
    }

    /// Everything (every class, no per-name deny).
    pub fn all() -> Self {
        Self::classes([
            RuleClass::Resolution,
            RuleClass::Propositional,
            RuleClass::Equality,
            RuleClass::LinearArith,
            RuleClass::Rewrite,
            RuleClass::Subproof,
            RuleClass::Other,
        ])
    }

    /// The QF_UF fragment: propositional + equality + resolution + rewriting,
    /// no arithmetic, no subproofs.
    pub fn qf_uf() -> Self {
        Self::classes([
            RuleClass::Resolution,
            RuleClass::Propositional,
            RuleClass::Equality,
            RuleClass::Rewrite,
        ])
    }

    /// QF_UFLIA: QF_UF plus linear integer arithmetic.
    pub fn qf_uflia() -> Self {
        let mut p = Self::qf_uf();
        p.classes.insert(RuleClass::LinearArith);
        p
    }

    /// Add a per-name allow override.
    pub fn allow(mut self, rule: impl Into<String>) -> Self {
        self.allow.insert(rule.into());
        self
    }
    /// Add a per-name deny override (takes precedence over everything).
    pub fn deny(mut self, rule: impl Into<String>) -> Self {
        self.deny.insert(rule.into());
        self
    }

    /// Is `rule` admitted under this policy? `deny` wins, then `allow`, then the
    /// class filter.
    pub fn accepts(&self, rule: &str) -> bool {
        if self.deny.contains(rule) {
            return false;
        }
        if self.allow.contains(rule) {
            return true;
        }
        self.classes.contains(&classify(rule))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn classification() {
        assert_eq!(classify("la_generic"), RuleClass::LinearArith);
        assert_eq!(classify("la_mult_pos"), RuleClass::LinearArith);
        assert_eq!(classify("resolution"), RuleClass::Resolution);
        assert_eq!(classify("cong"), RuleClass::Equality);
        assert_eq!(classify("subproof"), RuleClass::Subproof);
        assert_eq!(classify("bool_simplify"), RuleClass::Rewrite);
        assert_eq!(classify("assume"), RuleClass::Assume);
    }

    #[test]
    fn qf_uf_rejects_arith_and_subproofs() {
        let p = RulePolicy::qf_uf();
        assert!(p.accepts("resolution"));
        assert!(p.accepts("cong"));
        assert!(p.accepts("assume"));
        assert!(!p.accepts("la_generic"));
        assert!(!p.accepts("subproof"));
    }

    #[test]
    fn qf_uflia_admits_arith_only() {
        let p = RulePolicy::qf_uflia();
        assert!(p.accepts("la_generic"));
        assert!(!p.accepts("subproof"));
    }

    #[test]
    fn overrides() {
        let p = RulePolicy::qf_uf().allow("la_generic").deny("cong");
        assert!(p.accepts("la_generic")); // allow beats class filter
        assert!(!p.accepts("cong")); // deny beats class filter
    }
}
