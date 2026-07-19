//! Positive decision relations for negative SpecTec applicability.
//!
//! A SpecTec `otherwise` guard can mean that an earlier **relation
//! judgement is not derivable**.  That fact must not be represented as
//! `¬d ⌜J⌝` inside a [`RuleSet`](crate::metalogic::RuleSet) clause:
//! `Derivable` is the impredicative closure of a *positive* rule operator,
//! and a negative occurrence of its predicate `d` would make that operator
//! non-monotone.
//!
//! Instead, a certified decision procedure is represented by an ordinary
//! positive graph judgement
//!
//! ```text
//! decision.<R>(⌜J⌝, bool.false)
//! ```
//!
//! whose clauses compute the answer.  Before such clauses and their adequacy
//! theorem exist, [`OpaqueDecisions`] lowers the request through the standard
//! opaque hatch.  This records the precise missing decision family without
//! making the enclosing rule fireable or improving the honest opacity census.
//!
//! # Certification contract
//!
//! A non-opaque [`DecisionLowerer`] implementation may return the positive
//! graph judgement only when its installed clause family is accompanied by
//! kernel-checked adequacy in both directions:
//!
//! - `decision.R(J, true)  ⟹ Derivable(R(J))`;
//! - `decision.R(J, false) ⟹ ¬Derivable(R(J))`;
//! - every well-sorted ground query derives exactly one answer.
//!
//! The last two properties are what make a `false` graph result a sound and
//! complete replacement for negative rule applicability.  Merely failing to
//! derive the positive relation is not a negative certificate.

use covalence_core::{Error, Result, Term};
use covalence_hol_eval::EvalThm as Thm;

use super::super::encode::{app, con, tag};
use super::{Clause, LowerPrem, opaque, rule_set_of};
use crate::init::ext::TermExt;
use crate::metalogic::{RuleSet, derivable};

/// The answer requested from a positive decision relation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DecisionAnswer {
    Yes,
    No,
}

impl DecisionAnswer {
    fn encoded(self) -> Term {
        match self {
            DecisionAnswer::Yes => con("bool.true"),
            DecisionAnswer::No => con("bool.false"),
        }
    }
}

/// One request to decide an encoded SpecTec relation judgement.
#[derive(Debug, Clone)]
pub struct DecisionRequest {
    relation: String,
    query: Term,
    subject: DecisionSubject,
    expected: DecisionAnswer,
}

/// The proposition whose truth a positive decision graph certifies.
///
/// Relation judgements are reconstructed against the exact source
/// [`RuleSet`].  Composite applicability is already a bool-typed HOL
/// proposition, typically
/// `Derivable(R(args)) ∧ guard`; keeping it as a theorem proposition rather
/// than a Rust callback is what lets certification cover ordered clauses
/// without introducing a negative occurrence of `Derivable`.
#[derive(Debug, Clone)]
enum DecisionSubject {
    RelationJudgement,
    CompositeApplicability(Term),
}

impl DecisionRequest {
    pub fn new(relation: impl Into<String>, query: Term, expected: DecisionAnswer) -> Self {
        Self {
            relation: relation.into(),
            query,
            subject: DecisionSubject::RelationJudgement,
            expected,
        }
    }

    /// Request a decision for an exact composite applicability proposition.
    ///
    /// `query` is its stable, encoded graph key; `applicability` is the
    /// bool-typed HOL proposition related to the graph by adequacy.  The two
    /// are intentionally separate: an encoding is data, while adequacy is a
    /// theorem about semantics.
    pub fn composite(
        relation: impl Into<String>,
        query: Term,
        applicability: Term,
        expected: DecisionAnswer,
    ) -> Result<Self> {
        // Constructing implication is a kernel type check that both operands
        // are propositions; unlike inspecting `Term::ty`, its failure already
        // uses the public HOL error boundary.
        applicability.clone().imp(applicability.clone())?;
        Ok(Self {
            relation: relation.into(),
            query,
            subject: DecisionSubject::CompositeApplicability(applicability),
            expected,
        })
    }

    pub fn relation(&self) -> &str {
        &self.relation
    }

    pub fn query(&self) -> &Term {
        &self.query
    }

    pub fn expected(&self) -> DecisionAnswer {
        self.expected
    }

    /// The canonical positive graph judgement
    /// `decision.<relation>(query, expected)`.
    pub fn judgement(&self) -> Result<Term> {
        let body = app(
            app(con("decision.args"), self.query.clone())?,
            self.expected.encoded(),
        )?;
        tag(format!("decision.{}", self.relation), body)
    }

    fn opaque_reason(&self) -> String {
        format!("decision.{}", self.relation)
    }

    fn consequence(&self, source: &RuleSet<'_>) -> Result<Term> {
        let positive = match &self.subject {
            DecisionSubject::RelationJudgement => derivable(source, self.query())?,
            DecisionSubject::CompositeApplicability(applicability) => applicability.clone(),
        };
        match self.expected {
            DecisionAnswer::Yes => Ok(positive),
            DecisionAnswer::No => positive.not(),
        }
    }
}

/// Lower decision requests into positive clause premises.
///
/// Implementations returning a non-opaque graph premise must satisfy the
/// module-level certification contract.  The default implementation used
/// while a family is unavailable is [`OpaqueDecisions`].
pub trait DecisionLowerer {
    fn premise(&mut self, request: &DecisionRequest) -> Result<LowerPrem>;
}

/// A kernel-checked, answer-specific certificate for one decision query.
///
/// This is deliberately a **ground-query** package, not an assertion that a
/// Rust predicate decided a whole relation family.  It is the smallest useful
/// proof boundary: a later quantified-family constructor can manufacture
/// these cases by specialization, while callers can already install finite
/// certified frontiers without gaining authority over unproved queries.
// TODO(cov:wasm.spectec.decision-family-universal, major): Specialize closed quantified adequacy, totality, and determinacy theorems into ground cases.
///
/// The two theorem obligations are:
///
/// - `totality`: `⊢ Derivable_decision decision.R(query, answer)`;
/// - `adequacy`:
///   - for `Yes`, `⊢ Derivable_decision ... ⟹ Derivable_source query`;
///   - for `No`, `⊢ Derivable_decision ... ⟹ ¬Derivable_source query`.
///
/// Both conclusions are reconstructed from the exact packaged decision
/// clauses and source rule set, and both theorem contexts must be empty.
/// Consequently neither a theorem for another clause family nor an assumed
/// proposition can authorize lowering.
#[derive(Clone)]
pub struct CertifiedDecisionCase {
    request: DecisionRequest,
    totality: Thm,
    adequacy: Thm,
}

impl std::fmt::Debug for CertifiedDecisionCase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CertifiedDecisionCase")
            .field("request", &self.request)
            .finish_non_exhaustive()
    }
}

impl CertifiedDecisionCase {
    /// The certified request.
    pub fn request(&self) -> &DecisionRequest {
        &self.request
    }

    /// The kernel theorem proving that the packaged graph clauses produce the
    /// requested answer.
    pub fn totality(&self) -> &Thm {
        &self.totality
    }

    /// The kernel theorem relating that answer to source derivability.
    pub fn adequacy(&self) -> &Thm {
        &self.adequacy
    }
}

/// Clauses plus the exact query instances they are certified to decide.
///
/// Construction is the only way to obtain a non-opaque decision lowerer in
/// this module.  The fields of [`CertifiedDecisionCase`] are private and every
/// supplied theorem is checked against propositions rebuilt from `clauses`
/// and `source`.  Requests absent from `cases` retain the honest opaque
/// fallback.
#[derive(Debug, Clone)]
pub struct CertifiedDecisionFamily {
    relation: String,
    clauses: Vec<Clause>,
    cases: Vec<CertifiedDecisionCase>,
}

impl CertifiedDecisionFamily {
    /// Validate and package a positive decision family.
    ///
    /// Each tuple is `(request, totality, adequacy)`. All requests must name
    /// `relation`; duplicate request/answer pairs are rejected.
    pub fn certify(
        relation: impl Into<String>,
        clauses: Vec<Clause>,
        source: &RuleSet<'_>,
        certificates: Vec<(DecisionRequest, Thm, Thm)>,
    ) -> Result<Self> {
        let relation = relation.into();
        let decision = rule_set_of(clauses.clone());
        let mut cases = Vec::with_capacity(certificates.len());

        for (request, totality, adequacy) in certificates {
            if request.relation() != relation {
                return Err(certification_error(format!(
                    "request relation `{}` does not match family `{relation}`",
                    request.relation()
                )));
            }
            if cases
                .iter()
                .any(|c: &CertifiedDecisionCase| same_request(c.request(), &request))
            {
                return Err(certification_error("duplicate certified request"));
            }

            let graph = derivable(&decision, &request.judgement()?)?;
            require_closed_exact("totality", &totality, &graph)?;

            let consequence = request.consequence(source)?;
            let expected_adequacy = graph.imp(consequence)?;
            require_closed_exact("adequacy", &adequacy, &expected_adequacy)?;

            cases.push(CertifiedDecisionCase {
                request,
                totality,
                adequacy,
            });
        }

        Ok(Self {
            relation,
            clauses,
            cases,
        })
    }

    /// Relation family authorized by this package.
    pub fn relation(&self) -> &str {
        &self.relation
    }

    /// Positive graph clauses that must be included in the enclosing rule
    /// set whenever this lowerer is used.
    pub fn clauses(&self) -> &[Clause] {
        &self.clauses
    }

    /// The exact query certificates carried by this family.
    pub fn cases(&self) -> &[CertifiedDecisionCase] {
        &self.cases
    }
}

impl DecisionLowerer for CertifiedDecisionFamily {
    fn premise(&mut self, request: &DecisionRequest) -> Result<LowerPrem> {
        if self
            .cases
            .iter()
            .any(|case| same_request(case.request(), request))
        {
            Ok(LowerPrem::Judgement(request.judgement()?))
        } else {
            OpaqueDecisions.premise(request)
        }
    }
}

fn same_request(a: &DecisionRequest, b: &DecisionRequest) -> bool {
    a.relation == b.relation
        && a.query == b.query
        && same_subject(&a.subject, &b.subject)
        && a.expected == b.expected
}

fn same_subject(a: &DecisionSubject, b: &DecisionSubject) -> bool {
    match (a, b) {
        (DecisionSubject::RelationJudgement, DecisionSubject::RelationJudgement) => true,
        (
            DecisionSubject::CompositeApplicability(a),
            DecisionSubject::CompositeApplicability(b),
        ) => a == b,
        _ => false,
    }
}

fn require_closed_exact(label: &str, theorem: &Thm, expected: &Term) -> Result<()> {
    if !theorem.hyps().is_empty() {
        return Err(certification_error(format!(
            "{label} certificate has hypotheses"
        )));
    }
    if theorem.concl() != expected {
        return Err(certification_error(format!(
            "{label} certificate proves the wrong proposition"
        )));
    }
    Ok(())
}

fn certification_error(message: impl Into<String>) -> Error {
    Error::ConnectiveRule(format!(
        "SpecTec decision-family certification: {}",
        message.into()
    ))
}

/// Honest fallback for a decision family that has not yet been certified.
#[derive(Debug, Default, Clone, Copy)]
pub struct OpaqueDecisions;

impl DecisionLowerer for OpaqueDecisions {
    fn premise(&mut self, request: &DecisionRequest) -> Result<LowerPrem> {
        Ok(LowerPrem::Judgement(opaque(
            &request.opaque_reason(),
            request.judgement()?,
        )?))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::metalogic::{self, Premise};
    use crate::wasm::lower::{Clause, rule_set_of};
    use covalence_hol_eval::derived::DerivedRules;

    #[test]
    fn request_has_a_canonical_positive_graph_judgement() {
        let query = con("query");
        let req = DecisionRequest::new("Ref_ok", query.clone(), DecisionAnswer::No);
        let body = app(app(con("decision.args"), query).unwrap(), con("bool.false")).unwrap();
        assert_eq!(
            req.judgement().unwrap(),
            tag("decision.Ref_ok", body).unwrap()
        );
    }

    #[test]
    fn unavailable_family_stays_opaque_and_cannot_use_an_unrelated_proof() {
        let query = con("query");
        let req = DecisionRequest::new("Ref_ok", query, DecisionAnswer::No);
        let mut decisions = OpaqueDecisions;
        let guarded = Clause {
            metavars: vec![],
            prems: vec![decisions.premise(&req).unwrap()],
            concl: con("guarded"),
        };
        let base = Clause {
            metavars: vec![],
            prems: vec![],
            concl: con("unrelated"),
        };
        let rs = rule_set_of(vec![guarded, base]);
        let n = rs.n_clauses().unwrap();

        // The premise-free unrelated fact is derivable.
        let unrelated = metalogic::derive_mixed(&rs, 1, n, &[], vec![]).unwrap();
        // It cannot be substituted for the opaque decision judgement: the
        // kernel checks the exact antecedent during implication elimination.
        assert!(
            metalogic::derive_mixed(&rs, 0, n, &[], vec![Premise::Derivation(unrelated)]).is_err()
        );
        // Omitting an antecedent produces only a partially-applied implication
        // theorem; it is not a proof of the guarded judgement.
        let partial = metalogic::derive_mixed(&rs, 0, n, &[], vec![]).unwrap();
        let guarded_derivable = metalogic::derivable(&rs, &con("guarded")).unwrap();
        assert_ne!(partial.concl(), &guarded_derivable);
    }

    fn certified_yes_toy() -> (CertifiedDecisionFamily, DecisionRequest, RuleSet<'static>) {
        let query = con("toy.query");
        let request = DecisionRequest::new("Toy", query.clone(), DecisionAnswer::Yes);

        // Source semantics: the toy query is an axiom.
        let source = rule_set_of(vec![Clause {
            metavars: vec![],
            prems: vec![],
            concl: query.clone(),
        }]);

        // Decision implementation: the positive `Yes` graph is an axiom.
        let graph_judgement = request.judgement().unwrap();
        let clauses = vec![Clause {
            metavars: vec![],
            prems: vec![],
            concl: graph_judgement,
        }];
        let decision = rule_set_of(clauses.clone());

        let graph = metalogic::derive_mixed(&decision, 0, 1, &[], vec![]).unwrap();
        let source_fact = metalogic::derive_mixed(&source, 0, 1, &[], vec![]).unwrap();
        let adequacy = source_fact.imp_intro(graph.concl()).unwrap();

        let family = CertifiedDecisionFamily::certify(
            "Toy",
            clauses,
            &source,
            vec![(request.clone(), graph, adequacy)],
        )
        .unwrap();
        (family, request, source)
    }

    #[test]
    fn certified_toy_family_exposes_only_the_proved_positive_graph() {
        let (mut family, request, _) = certified_yes_toy();
        assert_eq!(family.relation(), "Toy");
        assert_eq!(family.clauses().len(), 1);
        assert_eq!(family.cases().len(), 1);

        let LowerPrem::Judgement(got) = family.premise(&request).unwrap() else {
            panic!("decision graphs are inductive judgements")
        };
        assert_eq!(got, request.judgement().unwrap());
        assert!(!format!("{got}").contains("opaque"));

        // Certification is answer-specific: proving `Yes` gives no authority
        // to expose the `No` graph for the same query.
        let no = DecisionRequest::new("Toy", request.query().clone(), DecisionAnswer::No);
        let LowerPrem::Judgement(got) = family.premise(&no).unwrap() else {
            panic!("opaque decisions are inductive judgements")
        };
        assert!(format!("{got}").contains("opaque"));
    }

    #[test]
    fn wrong_or_assumed_certificates_cannot_authorize_a_family() {
        let (family, request, source) = certified_yes_toy();
        let clauses = family.clauses().to_vec();
        let decision = rule_set_of(clauses.clone());
        let graph_prop = derivable(&decision, &request.judgement().unwrap()).unwrap();
        let good_totality = metalogic::derive_mixed(&decision, 0, 1, &[], vec![]).unwrap();
        let source_fact = metalogic::derive_mixed(&source, 0, 1, &[], vec![]).unwrap();

        let wrong = CertifiedDecisionFamily::certify(
            "Toy",
            clauses.clone(),
            &source,
            vec![(request.clone(), source_fact.clone(), good_totality.clone())],
        );
        assert!(
            wrong.is_err(),
            "a closed theorem for another logic is not totality"
        );

        let assumed_totality = Thm::assume(graph_prop).unwrap();
        let good_adequacy = source_fact.imp_intro(good_totality.concl()).unwrap();
        let open = CertifiedDecisionFamily::certify(
            "Toy",
            clauses,
            &source,
            vec![(request, assumed_totality, good_adequacy)],
        );
        assert!(open.is_err(), "certificates with hypotheses are rejected");
    }

    #[test]
    fn composite_applicability_is_certified_against_its_exact_hol_proposition() {
        let source_query = con("composite.source");
        let source = rule_set_of(vec![Clause {
            metavars: vec![],
            prems: vec![],
            concl: source_query,
        }]);
        let source_fact = metalogic::derive_mixed(&source, 0, 1, &[], vec![]).unwrap();
        let applicability = source_fact
            .clone()
            .and_intro(crate::init::logic::truth())
            .unwrap();
        let graph_key = con("composite.key");
        let request = DecisionRequest::composite(
            "Composite",
            graph_key,
            applicability.concl().clone(),
            DecisionAnswer::Yes,
        )
        .unwrap();
        let graph_judgement = request.judgement().unwrap();
        let clauses = vec![Clause {
            metavars: vec![],
            prems: vec![],
            concl: graph_judgement,
        }];
        let decision = rule_set_of(clauses.clone());
        let totality = metalogic::derive_mixed(&decision, 0, 1, &[], vec![]).unwrap();
        let adequacy = applicability.imp_intro(totality.concl()).unwrap();

        let mut family = CertifiedDecisionFamily::certify(
            "Composite",
            clauses.clone(),
            &source,
            vec![(request.clone(), totality.clone(), adequacy)],
        )
        .unwrap();
        assert!(matches!(
            family.premise(&request).unwrap(),
            LowerPrem::Judgement(j) if j == request.judgement().unwrap()
        ));

        // Reusing the same encoded key does not let a certificate silently
        // authorize a different semantic conjunction.
        let forged = DecisionRequest::composite(
            "Composite",
            request.query().clone(),
            con("different.bool.proposition"),
            DecisionAnswer::Yes,
        );
        assert!(
            forged.is_err(),
            "an arbitrary data constructor is not a bool proposition"
        );

        let other_applicability = source_fact.concl().clone();
        let other = DecisionRequest::composite(
            "Composite",
            request.query().clone(),
            other_applicability,
            DecisionAnswer::Yes,
        )
        .unwrap();
        assert!(matches!(
            family.premise(&other).unwrap(),
            LowerPrem::Judgement(j) if format!("{j}").contains("opaque")
        ));

        let wrong = CertifiedDecisionFamily::certify(
            "Composite",
            clauses,
            &source,
            vec![(other, totality, family.cases()[0].adequacy().clone())],
        );
        assert!(
            wrong.is_err(),
            "adequacy for one conjunction cannot certify another"
        );
    }
}
