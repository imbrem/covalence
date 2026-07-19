//! Adapter from capability-sized [`covalence_logic_api`] implementations to
//! the legacy inductive compatibility surface.
//!
//! The wrapper is intentionally explicit. It cannot create theorem values:
//! every proof operation delegates to a proof capability already implemented
//! by the wrapped logic. The wrapped logic's `Kind` carrier is irrelevant to
//! the older inductive API and remains accessible through [`inner`](Self::inner).

use covalence_logic_api as api;

use crate::logic::{Logic, LogicOps};

/// Opt-in compatibility wrapper for a capability-sized logic backend.
#[derive(Clone, Copy, Debug, Default)]
#[repr(transparent)]
pub struct LogicApiAdapter<L>(L);

impl<L> LogicApiAdapter<L> {
    pub const fn new(logic: L) -> Self {
        Self(logic)
    }

    pub const fn inner(&self) -> &L {
        &self.0
    }

    pub fn into_inner(self) -> L {
        self.0
    }
}

impl<L: api::Logic> Logic for LogicApiAdapter<L> {
    type Type = L::Type;
    type Term = L::Term;
    type Thm = L::Thm;
    type Error = L::Error;
}

impl<L> LogicOps for LogicApiAdapter<L>
where
    L: api::TypeSystem
        + api::TermLanguage
        + api::ApplicationView
        + api::EqualitySyntax
        + api::PropositionSyntax
        + api::QuantifierSyntax
        + api::TheoremView
        + api::EqualityRules
        + api::AssumptionRules
        + api::BetaRules
        + api::ApplicationCongruence
        + api::TheoremInstantiation
        + api::BinderRules
        + api::ImplicationRules
        + api::ConjunctionRules,
{
    fn bool_ty(&self) -> Self::Type {
        api::TypeSystem::proposition_type(&self.0)
    }

    fn fun_ty(&self, a: Self::Type, b: Self::Type) -> Self::Type {
        api::TypeSystem::function_type(&self.0, a, b)
    }

    fn var(&self, name: &str, ty: Self::Type) -> Self::Term {
        api::TermLanguage::variable(&self.0, name, ty)
    }

    fn app(&self, f: Self::Term, x: Self::Term) -> Result<Self::Term, Self::Error> {
        api::TermLanguage::apply(&self.0, f, x)
    }

    fn lam(&self, name: &str, ty: Self::Type, body: Self::Term) -> Self::Term {
        api::TermLanguage::abstract_term(&self.0, name, ty, body)
    }

    fn eq(&self, a: Self::Term, b: Self::Term) -> Result<Self::Term, Self::Error> {
        api::EqualitySyntax::equal(&self.0, a, b)
    }

    fn imp(&self, a: Self::Term, b: Self::Term) -> Result<Self::Term, Self::Error> {
        api::PropositionSyntax::implies(&self.0, a, b)
    }

    fn and(&self, a: Self::Term, b: Self::Term) -> Result<Self::Term, Self::Error> {
        api::PropositionSyntax::conjunction(&self.0, a, b)
    }

    fn forall(
        &self,
        name: &str,
        ty: Self::Type,
        body: Self::Term,
    ) -> Result<Self::Term, Self::Error> {
        api::QuantifierSyntax::forall(&self.0, name, ty, body)
    }

    fn exists(
        &self,
        name: &str,
        ty: Self::Type,
        body: Self::Term,
    ) -> Result<Self::Term, Self::Error> {
        api::QuantifierSyntax::exists(&self.0, name, ty, body)
    }

    fn type_of(&self, term: &Self::Term) -> Result<Self::Type, Self::Error> {
        api::TermLanguage::type_of(&self.0, term)
    }

    fn dest_app(&self, term: &Self::Term) -> Option<(Self::Term, Self::Term)> {
        api::ApplicationView::as_application(&self.0, term)
    }

    fn dest_eq(&self, term: &Self::Term) -> Option<(Self::Term, Self::Term)> {
        api::EqualitySyntax::as_equal(&self.0, term)
    }

    fn concl(&self, theorem: &Self::Thm) -> Self::Term {
        api::TheoremView::conclusion(&self.0, theorem)
    }

    fn hyps(&self, theorem: &Self::Thm) -> Vec<Self::Term> {
        api::TheoremView::hypotheses(&self.0, theorem)
    }

    fn assume(&self, term: Self::Term) -> Result<Self::Thm, Self::Error> {
        api::AssumptionRules::assume(&self.0, term)
    }

    fn refl(&self, term: Self::Term) -> Result<Self::Thm, Self::Error> {
        api::EqualityRules::reflexivity(&self.0, term)
    }

    fn sym(&self, theorem: Self::Thm) -> Result<Self::Thm, Self::Error> {
        api::EqualityRules::symmetry(&self.0, theorem)
    }

    fn trans(&self, left: Self::Thm, right: Self::Thm) -> Result<Self::Thm, Self::Error> {
        api::EqualityRules::transitivity(&self.0, left, right)
    }

    fn eq_mp(&self, equality: Self::Thm, proof: Self::Thm) -> Result<Self::Thm, Self::Error> {
        api::EqualityRules::equality_elim(&self.0, equality, proof)
    }

    fn beta_conv(&self, redex: Self::Term) -> Result<Self::Thm, Self::Error> {
        api::BetaRules::beta_conversion(&self.0, redex)
    }

    fn cong_app(
        &self,
        functions: Self::Thm,
        arguments: Self::Thm,
    ) -> Result<Self::Thm, Self::Error> {
        api::ApplicationCongruence::application_congruence(&self.0, functions, arguments)
    }

    fn inst(
        &self,
        theorem: Self::Thm,
        name: &str,
        replacement: Self::Term,
    ) -> Result<Self::Thm, Self::Error> {
        api::TheoremInstantiation::instantiate(&self.0, theorem, name, replacement)
    }

    fn all_intro(
        &self,
        theorem: Self::Thm,
        name: &str,
        ty: Self::Type,
    ) -> Result<Self::Thm, Self::Error> {
        api::BinderRules::forall_intro(&self.0, theorem, name, ty)
    }

    fn all_elim(&self, theorem: Self::Thm, term: Self::Term) -> Result<Self::Thm, Self::Error> {
        api::BinderRules::forall_elim(&self.0, theorem, term)
    }

    fn imp_intro(
        &self,
        theorem: Self::Thm,
        hypothesis: &Self::Term,
    ) -> Result<Self::Thm, Self::Error> {
        api::ImplicationRules::implication_intro(&self.0, theorem, hypothesis)
    }

    fn imp_elim(
        &self,
        implication: Self::Thm,
        antecedent: Self::Thm,
    ) -> Result<Self::Thm, Self::Error> {
        api::ImplicationRules::implication_elim(&self.0, implication, antecedent)
    }

    fn and_intro(&self, left: Self::Thm, right: Self::Thm) -> Result<Self::Thm, Self::Error> {
        api::ConjunctionRules::conjunction_intro(&self.0, left, right)
    }

    fn and_elim_l(&self, theorem: Self::Thm) -> Result<Self::Thm, Self::Error> {
        api::ConjunctionRules::conjunction_elim_left(&self.0, theorem)
    }

    fn and_elim_r(&self, theorem: Self::Thm) -> Result<Self::Thm, Self::Error> {
        api::ConjunctionRules::conjunction_elim_right(&self.0, theorem)
    }
}

#[cfg(test)]
mod tests {
    use core::convert::Infallible;

    use super::*;

    #[derive(Clone, Debug, PartialEq, Eq)]
    struct Proof {
        conclusion: String,
        hypotheses: Vec<String>,
    }

    #[derive(Clone, Copy, Debug)]
    struct SymbolicLogic;

    impl api::Logic for SymbolicLogic {
        type Kind = &'static str;
        type Type = String;
        type Term = String;
        type Thm = Proof;
        type Error = Infallible;
    }

    impl api::TypeSystem for SymbolicLogic {
        fn proper(&self) -> &'static str {
            "type"
        }
        fn kind_arrow(&self, _: &'static str, _: &'static str) -> &'static str {
            "operator"
        }
        fn proposition_type(&self) -> String {
            "prop".into()
        }
        fn function_type(&self, a: String, b: String) -> String {
            format!("({a}->{b})")
        }
        fn type_variable(&self, name: &str, _: &'static str) -> String {
            name.into()
        }
        fn type_apply(&self, operator: String, argument: String) -> Result<String, Infallible> {
            Ok(format!("{operator}[{argument}]"))
        }
        fn kind_of(&self, _: &String) -> Result<&'static str, Infallible> {
            Ok("type")
        }
    }

    impl api::TermLanguage for SymbolicLogic {
        fn variable(&self, name: &str, ty: String) -> String {
            format!("{name}:{ty}")
        }
        fn apply(&self, function: String, argument: String) -> Result<String, Infallible> {
            Ok(format!("{function}({argument})"))
        }
        fn abstract_term(&self, name: &str, ty: String, body: String) -> String {
            format!("λ{name}:{ty}.{body}")
        }
        fn type_of(&self, _: &String) -> Result<String, Infallible> {
            Ok("term-type".into())
        }
    }

    impl api::ApplicationView for SymbolicLogic {
        fn as_application(&self, _: &String) -> Option<(String, String)> {
            Some(("function".into(), "argument".into()))
        }
    }

    impl api::EqualitySyntax for SymbolicLogic {
        fn equal(&self, left: String, right: String) -> Result<String, Infallible> {
            Ok(format!("({left}={right})"))
        }
        fn as_equal(&self, _: &String) -> Option<(String, String)> {
            Some(("left".into(), "right".into()))
        }
    }

    impl api::PropositionSyntax for SymbolicLogic {
        fn implies(&self, antecedent: String, consequent: String) -> Result<String, Infallible> {
            Ok(format!("({antecedent}=>{consequent})"))
        }
        fn conjunction(&self, left: String, right: String) -> Result<String, Infallible> {
            Ok(format!("({left}&{right})"))
        }
    }

    impl api::QuantifierSyntax for SymbolicLogic {
        fn forall(&self, name: &str, ty: String, body: String) -> Result<String, Infallible> {
            Ok(format!("∀{name}:{ty}.{body}"))
        }
        fn exists(&self, name: &str, ty: String, body: String) -> Result<String, Infallible> {
            Ok(format!("∃{name}:{ty}.{body}"))
        }
    }

    impl api::TheoremView for SymbolicLogic {
        fn conclusion(&self, theorem: &Proof) -> String {
            theorem.conclusion.clone()
        }
        fn hypotheses(&self, theorem: &Proof) -> Vec<String> {
            theorem.hypotheses.clone()
        }
    }

    fn proof(rule: &str) -> Proof {
        Proof {
            conclusion: rule.into(),
            hypotheses: vec![],
        }
    }

    impl api::EqualityRules for SymbolicLogic {
        fn reflexivity(&self, term: String) -> Result<Proof, Infallible> {
            Ok(proof(&format!("refl({term})")))
        }
        fn symmetry(&self, _: Proof) -> Result<Proof, Infallible> {
            Ok(proof("sym"))
        }
        fn transitivity(&self, _: Proof, _: Proof) -> Result<Proof, Infallible> {
            Ok(proof("trans"))
        }
        fn equality_elim(&self, _: Proof, _: Proof) -> Result<Proof, Infallible> {
            Ok(proof("eq-elim"))
        }
    }

    impl api::AssumptionRules for SymbolicLogic {
        fn assume(&self, proposition: String) -> Result<Proof, Infallible> {
            Ok(Proof {
                conclusion: proposition.clone(),
                hypotheses: vec![proposition],
            })
        }
    }

    impl api::BetaRules for SymbolicLogic {
        fn beta_conversion(&self, redex: String) -> Result<Proof, Infallible> {
            Ok(proof(&format!("beta({redex})")))
        }
    }

    impl api::ApplicationCongruence for SymbolicLogic {
        fn application_congruence(&self, _: Proof, _: Proof) -> Result<Proof, Infallible> {
            Ok(proof("application-congruence"))
        }
    }

    impl api::TheoremInstantiation for SymbolicLogic {
        fn instantiate(
            &self,
            _: Proof,
            name: &str,
            replacement: String,
        ) -> Result<Proof, Infallible> {
            Ok(proof(&format!("instantiate({name},{replacement})")))
        }
    }

    impl api::BinderRules for SymbolicLogic {
        fn forall_intro(&self, _: Proof, name: &str, ty: String) -> Result<Proof, Infallible> {
            Ok(proof(&format!("forall-intro({name},{ty})")))
        }
        fn forall_elim(&self, _: Proof, argument: String) -> Result<Proof, Infallible> {
            Ok(proof(&format!("forall-elim({argument})")))
        }
    }

    impl api::ImplicationRules for SymbolicLogic {
        fn implication_intro(&self, _: Proof, hypothesis: &String) -> Result<Proof, Infallible> {
            Ok(proof(&format!("implication-intro({hypothesis})")))
        }
        fn implication_elim(&self, _: Proof, _: Proof) -> Result<Proof, Infallible> {
            Ok(proof("implication-elim"))
        }
    }

    impl api::ConjunctionRules for SymbolicLogic {
        fn conjunction_intro(&self, _: Proof, _: Proof) -> Result<Proof, Infallible> {
            Ok(proof("conjunction-intro"))
        }
        fn conjunction_elim_left(&self, _: Proof) -> Result<Proof, Infallible> {
            Ok(proof("conjunction-elim-left"))
        }
        fn conjunction_elim_right(&self, _: Proof) -> Result<Proof, Infallible> {
            Ok(proof("conjunction-elim-right"))
        }
    }

    #[test]
    fn adapter_delegates_syntax_and_proof_capabilities() {
        let logic = LogicApiAdapter::new(SymbolicLogic);
        assert_eq!(api::TypeSystem::proper(logic.inner()), "type");
        assert_eq!(LogicOps::bool_ty(&logic), "prop");
        assert_eq!(
            LogicOps::app(&logic, "f".into(), "x".into()).unwrap(),
            "f(x)"
        );
        assert_eq!(
            LogicOps::imp(&logic, "p".into(), "q".into()).unwrap(),
            "(p=>q)"
        );

        let assumed = LogicOps::assume(&logic, "p".into()).unwrap();
        assert_eq!(LogicOps::concl(&logic, &assumed), "p");
        assert_eq!(LogicOps::hyps(&logic, &assumed), vec!["p"]);
        assert_eq!(
            LogicOps::cong_app(&logic, proof("f=g"), proof("x=y"))
                .unwrap()
                .conclusion,
            "application-congruence"
        );
    }
}
