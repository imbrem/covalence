//! First-class HOL predicates for the exact typed SpecTec relation fragment.
//!
//! This is deliberately separate from [`super::relation`], whose carrier is
//! the reified `nat` syntax algebra. Here a relation declared over `T` becomes
//! an ordinary predicate `T → bool`, with its rules interpreted directly over
//! already-resolved HOL carriers. The impredicative [`crate::metalogic`]
//! engine supplies closure and NativeHol-checked rule replay; this module adds
//! no trusted rule or theorem mint site.

use covalence_core::{Error, Result, Term, Type, subst};
use covalence_hol_eval::EvalThm as Thm;
use covalence_spectec::ast::{SpecTecDef, SpecTecParam, SpecTecPrem, SpecTecRule};

use super::denote::{self, DenoteCtx, TypeEnv};
use super::sort::{HolSort, RefinementAwareTypeResolver, SemanticTypeResolver, SortInvariant};
use super::syntax;
use super::type_family::TypeFamilies;
use crate::init::ext::TermExt;
use crate::metalogic::{self, Premise, RuleSet};

fn semantic_err(msg: impl Into<String>) -> Error {
    Error::ConnectiveRule(format!("SpecTec semantic relation: {}", msg.into()))
}

#[derive(Debug, Clone)]
enum TypedPremise {
    Relation(Term),
    Side(Term),
}

#[derive(Debug, Clone)]
struct TypedRule {
    binders: Vec<(String, Type)>,
    premises: Vec<TypedPremise>,
    conclusion: Term,
}

/// A SpecTec relation realized as a genuine HOL predicate on its declared
/// carrier.
pub struct SemanticRelation {
    name: String,
    carrier: Type,
    predicate: Term,
    rules: Vec<TypedRule>,
    rule_set: RuleSet<'static>,
}

/// Backend-neutral consumer surface for first-class typed relations.
pub trait HolRelationPredicate {
    fn name(&self) -> &str;
    fn carrier(&self) -> &Type;
    fn predicate(&self) -> &Term;
    fn rule_count(&self) -> usize;
    fn holds(&self, value: Term) -> Result<Term>;
    fn derive(&self, rule: usize, arguments: &[Term], premises: Vec<Premise>) -> Result<Thm>;
}

impl HolRelationPredicate for SemanticRelation {
    fn name(&self) -> &str {
        &self.name
    }

    fn carrier(&self) -> &Type {
        &self.carrier
    }

    fn predicate(&self) -> &Term {
        &self.predicate
    }

    fn rule_count(&self) -> usize {
        self.rules.len()
    }

    fn holds(&self, value: Term) -> Result<Term> {
        if value.type_of()? != self.carrier {
            return Err(semantic_err("relation argument has the wrong carrier"));
        }
        // Return the β-normal form of `predicate value`, which is also the
        // exact conclusion shape produced by generic rule replay.
        metalogic::derivable(&self.rule_set, &value)
    }

    fn derive(&self, rule: usize, arguments: &[Term], premises: Vec<Premise>) -> Result<Thm> {
        let typed_rule = self
            .rules
            .get(rule)
            .ok_or_else(|| semantic_err("rule index out of range"))?;
        let expected = typed_rule.binders.len();
        if arguments.len() != expected {
            return Err(semantic_err(format!(
                "rule expects {expected} arguments, got {}",
                arguments.len()
            )));
        }
        if premises.len() != typed_rule.premises.len() {
            return Err(semantic_err(format!(
                "rule expects {} premises, got {}",
                typed_rule.premises.len(),
                premises.len()
            )));
        }
        metalogic::derive_mixed(&self.rule_set, rule, self.rules.len(), arguments, premises)
    }
}

fn resolved_sort(
    ty: &covalence_spectec::ast::SpecTecTyp,
    resolver: &impl SemanticTypeResolver,
) -> Result<HolSort> {
    let resolved = resolver.resolve_type(ty)?;
    match resolved.sort.invariant() {
        SortInvariant::Unconstrained | SortInvariant::Predicate(_) => Ok(resolved.sort),
        SortInvariant::Unresolved => Err(semantic_err("relation carrier is unresolved")),
    }
}

fn typed_rule(
    relation: &str,
    rule: &SpecTecRule,
    defs: &[SpecTecDef],
    carrier: &Type,
    relation_invariant: Option<&Term>,
    resolver: &impl SemanticTypeResolver,
) -> Result<TypedRule> {
    let SpecTecRule::Rule { ps, e, prs, .. } = rule;
    let mut types = TypeEnv::new();
    let mut binders = Vec::new();
    let mut binder_guards = Vec::new();
    for param in ps {
        let SpecTecParam::Exp { x, t } = param else {
            return Err(semantic_err(
                "only expression-valued rule binders are in the typed fragment",
            ));
        };
        let sort = resolved_sort(t, resolver)?;
        let ty = sort.carrier().clone();
        if types.insert(x.clone(), ty.clone()).is_some() {
            return Err(semantic_err(format!("duplicate rule binder `{x}`")));
        }
        if let SortInvariant::Predicate(predicate) = sort.invariant() {
            binder_guards.push(predicate.clone().apply(Term::free(x.clone(), ty.clone()))?);
        }
        binders.push((x.clone(), ty));
    }
    let ctx = DenoteCtx::from_spec(defs, types);
    let conclusion = denote::denote(e, &ctx)?;
    if conclusion.type_of()? != *carrier {
        return Err(semantic_err(
            "rule conclusion does not inhabit relation carrier",
        ));
    }

    let mut premises: Vec<_> = binder_guards.into_iter().map(TypedPremise::Side).collect();
    for premise in prs {
        match premise {
            SpecTecPrem::Rule { x, as1, e, .. } if x == relation && as1.is_empty() => {
                let term = denote::denote(e, &ctx)?;
                if term.type_of()? != *carrier {
                    return Err(semantic_err(
                        "relation premise does not inhabit relation carrier",
                    ));
                }
                premises.push(TypedPremise::Relation(term));
            }
            SpecTecPrem::If { e } => {
                let side = denote::denote(e, &ctx)?;
                if side.type_of()? != Type::bool() {
                    return Err(semantic_err("If premise is not boolean"));
                }
                premises.push(TypedPremise::Side(side));
            }
            SpecTecPrem::Rule { .. } => {
                let SpecTecPrem::Rule { x, as1, e, .. } = premise else {
                    unreachable!()
                };
                if !as1.is_empty() {
                    return Err(semantic_err(
                        "parameterized cross-relation premise needs a typed instance family",
                    ));
                }
                let target = find_relation(defs, x)
                    .ok_or_else(|| semantic_err(format!("unknown relation `{x}`")))?;
                let SpecTecDef::Rel {
                    rules: target_rules,
                    ..
                } = target
                else {
                    unreachable!()
                };
                if !target_rules.is_empty() {
                    return Err(semantic_err(
                        "nonempty cross-relation premise needs simultaneous typed closure",
                    ));
                }
                // An empty external relation has a closed, independent
                // impredicative predicate. Using that predicate as a side
                // antecedent is exact and does not pretend mutual closure.
                let external = semantic_relation(target, defs)?;
                let term = denote::denote(e, &ctx)?;
                premises.push(TypedPremise::Side(external.holds(term)?));
            }
            SpecTecPrem::Let { .. } | SpecTecPrem::Else | SpecTecPrem::Iter { .. } => {
                return Err(semantic_err(
                    "dependent/Else/iterated premise is outside the typed fragment",
                ));
            }
        }
    }
    if let Some(invariant) = relation_invariant {
        premises.push(TypedPremise::Side(
            invariant.clone().apply(conclusion.clone())?,
        ));
    }
    Ok(TypedRule {
        binders,
        premises,
        conclusion,
    })
}

fn find_relation<'a>(defs: &'a [SpecTecDef], name: &str) -> Option<&'a SpecTecDef> {
    for def in defs {
        match def {
            SpecTecDef::Rel { x, .. } if x == name => return Some(def),
            SpecTecDef::Rec { ds } => {
                if let Some(found) = find_relation(ds, name) {
                    return Some(found);
                }
            }
            _ => {}
        }
    }
    None
}

fn clause(rule: &TypedRule, d_apply: &dyn Fn(&Term) -> Result<Term>) -> Result<Term> {
    let mut body = d_apply(&rule.conclusion)?;
    for premise in rule.premises.iter().rev() {
        let antecedent = match premise {
            TypedPremise::Relation(term) => d_apply(term)?,
            TypedPremise::Side(term) => term.clone(),
        };
        body = antecedent.imp(body)?;
    }
    for (name, ty) in rule.binders.iter().rev() {
        body = body.forall(name, ty.clone())?;
    }
    Ok(body)
}

fn sealed_valtype_classifier(relation: &str, defs: &[SpecTecDef]) -> Result<(Type, Term)> {
    let defaultable = match relation {
        "Defaultable" => true,
        "Nondefaultable" => false,
        _ => return Err(semantic_err("unknown sealed valtype classifier")),
    };
    let sealed = syntax::sealed_wasm_mutual_carriers()?;
    let carrier = sealed
        .carrier("valtype")
        .cloned()
        .ok_or_else(|| semantic_err("sealed valtype carrier is missing"))?;
    let definition = sealed
        .definitions()
        .get("valtype")
        .ok_or_else(|| semantic_err("sealed valtype definition is missing"))?;
    let type_ctx = syntax::TypeCtx::new(defs);
    let signature = syntax::mutual_church_signature("valtype", &type_ctx)?;
    let value_name = "cov$semantic$valtype$classifier$value";
    let value = Term::free(value_name, carrier.clone());
    let represented = definition.rep.clone().apply(value)?;
    let root = represented.apply(crate::init::list::nil(
        signature.runtime_path_step_carrier(),
    ))?;
    let unit = covalence_hol_eval::defs::unit_nil();
    let mut labels = Vec::new();
    let unit_constructors: &[usize] = if defaultable {
        &[34, 35, 36, 37, 38]
    } else {
        &[40]
    };
    for &constructor in unit_constructors {
        labels.push(signature.carved_root_label(constructor, unit.clone())?);
    }
    let nullability = if defaultable {
        covalence_hol_eval::defs::some(Type::unit()).apply(unit.clone())?
    } else {
        covalence_hol_eval::defs::none(Type::unit())
    };
    let universal = signature.carved_universal_domain_carrier()?;
    let arbitrary_child = Term::select_op(universal.clone()).apply(Term::abs(
        universal.clone(),
        covalence_hol_eval::mk_bool(true),
    ))?;
    let ref_payload =
        covalence_hol_eval::defs::pair(crate::init::option::option(Type::unit()), universal)
            .apply(nullability)?
            .apply(arbitrary_child)?;
    labels.push(signature.carved_root_label(39, ref_payload)?);
    let mut equalities = labels
        .into_iter()
        .map(|label| root.clone().equals(label))
        .collect::<Result<Vec<_>>>()?
        .into_iter();
    let first = equalities
        .next()
        .ok_or_else(|| semantic_err("valtype classifier has no cases"))?;
    let body = equalities.try_fold(first, |left, right| left.or(right))?;
    let predicate = Term::abs(carrier.clone(), subst::close(&body, value_name));
    if predicate.type_of()? != Type::fun(carrier.clone(), Type::bool()) {
        return Err(semantic_err("sealed valtype classifier is ill-typed"));
    }
    Ok((carrier, predicate))
}

fn sealed_valtype_relation(
    relation: &str,
    source_rules: &[SpecTecRule],
    defs: &[SpecTecDef],
) -> Result<SemanticRelation> {
    let [SpecTecRule::Rule { ps, prs, e, .. }] = source_rules else {
        return Err(semantic_err(
            "sealed valtype classifier source rule census drifted",
        ));
    };
    let [SpecTecParam::Exp { x, .. }] = ps.as_slice() else {
        return Err(semantic_err(
            "sealed valtype classifier binder census drifted",
        ));
    };
    if !matches!(prs.as_slice(), [SpecTecPrem::If { .. }])
        || !matches!(e, covalence_spectec::ast::SpecTecExp::Var { id } if id == x)
    {
        return Err(semantic_err("sealed valtype classifier rule shape drifted"));
    }
    let (carrier, classifier) = sealed_valtype_classifier(relation, defs)?;
    let value = Term::free(x.clone(), carrier.clone());
    let typed_rule = TypedRule {
        binders: vec![(x.clone(), carrier.clone())],
        premises: vec![TypedPremise::Side(classifier.apply(value.clone())?)],
        conclusion: value,
    };
    let rules = vec![typed_rule];
    let clause_rules = rules.clone();
    let rule_set = RuleSet::new(carrier.clone(), move |d_apply| {
        clause_rules
            .iter()
            .map(|rule| clause(rule, d_apply))
            .collect()
    });
    let predicate_value = Term::free("cov$semantic$relation$value", carrier.clone());
    let predicate_body = metalogic::derivable(&rule_set, &predicate_value)?;
    let predicate = Term::abs(
        carrier.clone(),
        subst::close(&predicate_body, "cov$semantic$relation$value"),
    );
    Ok(SemanticRelation {
        name: relation.to_owned(),
        carrier,
        predicate,
        rules,
        rule_set,
    })
}

/// Realize one exact relation definition as a first-class HOL predicate.
///
/// Refusal is fail-closed. Relation parameters, refined/unresolved carriers,
/// non-expression binders, cross-relation recursion, and premise forms needing
/// dependent lowering are rejected rather than erased.
// TODO(cov:kernel.hol.init.src.wasm.relations-hol-predicates-over-those-types-leg-b-not-started, severe): Extend beyond the exact 5/125 bundled relations: all 120 remaining carriers need recursive structural lifting of exact nested invariants; 57 still reach ground fNmag(32/64) through the legacy whole-carrier renderer before its exact CasePredicate can be applied; nonempty cross-relation SCCs still need simultaneous closure.
pub fn semantic_relation(def: &SpecTecDef, defs: &[SpecTecDef]) -> Result<SemanticRelation> {
    let SpecTecDef::Rel {
        x,
        ps,
        t,
        rules: source_rules,
        ..
    } = def
    else {
        return Err(semantic_err("definition is not a relation"));
    };
    if !ps.is_empty() {
        return Err(semantic_err(
            "parameterized relation needs a typed instance environment",
        ));
    }
    if matches!(x.as_str(), "Defaultable" | "Nondefaultable") {
        return sealed_valtype_relation(x, source_rules, defs);
    }
    let type_ctx = syntax::TypeCtx::new(defs);
    let families = TypeFamilies::new(defs);
    let resolver = RefinementAwareTypeResolver::new(&type_ctx, &families);
    let relation_sort = resolved_sort(t, &resolver)?;
    let carrier = relation_sort.carrier().clone();
    let relation_invariant = match relation_sort.invariant() {
        SortInvariant::Predicate(predicate) => Some(predicate),
        SortInvariant::Unconstrained => None,
        SortInvariant::Unresolved => unreachable!(),
    };
    let rules = source_rules
        .iter()
        .map(|rule| typed_rule(x, rule, defs, &carrier, relation_invariant, &resolver))
        .collect::<Result<Vec<_>>>()?;
    let clause_rules = rules.clone();
    let rule_set = RuleSet::new(carrier.clone(), move |d_apply| {
        clause_rules
            .iter()
            .map(|rule| clause(rule, d_apply))
            .collect()
    });
    let value = Term::free("cov$semantic$relation$value", carrier.clone());
    let body = metalogic::derivable(&rule_set, &value)?;
    let predicate = Term::abs(
        carrier.clone(),
        subst::close(&body, "cov$semantic$relation$value"),
    );
    if predicate.type_of()? != Type::fun(carrier.clone(), Type::bool()) {
        return Err(semantic_err("constructed relation predicate is ill-typed"));
    }
    Ok(SemanticRelation {
        name: x.clone(),
        carrier,
        predicate,
        rules,
        rule_set,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_hol_eval::{DerivedRules, TypeDefExt, mk_nat, prove_true};
    use covalence_spectec::ast::{
        MixOp, SpecTecBinOp, SpecTecExp, SpecTecNum, SpecTecNumTyp, SpecTecOpTyp,
    };

    fn nat(n: u64) -> SpecTecExp {
        SpecTecExp::Num {
            n: SpecTecNum::Nat(n),
        }
    }

    fn var(name: &str) -> SpecTecExp {
        SpecTecExp::Var { id: name.into() }
    }

    fn successor(value: SpecTecExp) -> SpecTecExp {
        SpecTecExp::Bin {
            op: SpecTecBinOp::Add,
            t: SpecTecOpTyp::Num(SpecTecNumTyp::Nat),
            e1: Box::new(value),
            e2: Box::new(nat(1)),
        }
    }

    fn naturals() -> SpecTecDef {
        SpecTecDef::Rel {
            x: "Natural".into(),
            ps: vec![],
            op: MixOp::new(vec!["NATURAL".into()]),
            t: covalence_spectec::ast::SpecTecTyp::Num(SpecTecNumTyp::Nat),
            rules: vec![
                SpecTecRule::Rule {
                    x: "zero".into(),
                    ps: vec![],
                    op: MixOp::new(vec!["NATURAL".into()]),
                    e: nat(0),
                    prs: vec![],
                },
                SpecTecRule::Rule {
                    x: "succ".into(),
                    ps: vec![SpecTecParam::Exp {
                        x: "n".into(),
                        t: covalence_spectec::ast::SpecTecTyp::Num(SpecTecNumTyp::Nat),
                    }],
                    op: MixOp::new(vec!["NATURAL".into()]),
                    e: successor(var("n")),
                    prs: vec![SpecTecPrem::Rule {
                        x: "Natural".into(),
                        as1: vec![],
                        op: MixOp::new(vec!["NATURAL".into()]),
                        e: var("n"),
                    }],
                },
            ],
        }
    }

    #[test]
    fn typed_nat_relation_is_a_real_predicate_and_replays_rules() {
        let def = naturals();
        let theory = semantic_relation(&def, std::slice::from_ref(&def)).unwrap();
        assert_eq!(theory.name(), "Natural");
        assert_eq!(theory.carrier(), &Type::nat());
        assert_eq!(
            theory.predicate().type_of().unwrap(),
            Type::fun(Type::nat(), Type::bool())
        );
        let applied = theory.predicate().clone().apply(mk_nat(0u64)).unwrap();
        let beta = crate::init::eq::beta_nf(applied);
        assert_eq!(
            beta.concl().as_eq().unwrap().1,
            &theory.holds(mk_nat(0u64)).unwrap()
        );
        let zero = theory.derive(0, &[], vec![]).unwrap();
        assert!(zero.hyps().is_empty());
        assert_eq!(zero.concl(), &theory.holds(mk_nat(0u64)).unwrap());

        let one = theory
            .derive(1, &[mk_nat(0u64)], vec![Premise::Derivation(zero)])
            .unwrap();
        assert!(one.hyps().is_empty());
        let successor_zero = crate::init::nat::nat_add()
            .apply(mk_nat(0u64))
            .unwrap()
            .apply(mk_nat(1u64))
            .unwrap();
        assert_eq!(one.concl(), &theory.holds(successor_zero).unwrap());
    }

    #[test]
    fn denotable_side_condition_is_preserved_and_checked() {
        let mut def = naturals();
        let SpecTecDef::Rel { rules, .. } = &mut def else {
            unreachable!()
        };
        let SpecTecRule::Rule { prs, .. } = &mut rules[0];
        prs.push(SpecTecPrem::If {
            e: SpecTecExp::Cmp {
                op: covalence_spectec::ast::SpecTecCmpOp::Eq,
                t: SpecTecOpTyp::Num(SpecTecNumTyp::Nat),
                e1: Box::new(nat(0)),
                e2: Box::new(nat(0)),
            },
        });
        let theory = semantic_relation(&def, std::slice::from_ref(&def)).unwrap();
        let side = mk_nat(0u64).equals(mk_nat(0u64)).unwrap();
        let proof = prove_true(&side).unwrap();
        let zero = theory.derive(0, &[], vec![Premise::Side(proof)]).unwrap();
        assert!(zero.hyps().is_empty());
    }

    #[test]
    fn refined_relation_carrier_adds_membership_guards_without_erasure() {
        let mut def = naturals();
        let SpecTecDef::Rel { t, .. } = &mut def else {
            unreachable!()
        };
        *t = covalence_spectec::ast::SpecTecTyp::Var {
            x: "byte".into(),
            as1: vec![],
        };
        let defs = crate::wasm::spec::wasm_spec();
        let theory = semantic_relation(&def, &defs).unwrap();
        assert_eq!(theory.carrier(), &Type::nat());
        // The source membership predicate is a real extra rule antecedent, so
        // replay without its proof refuses rather than treating it as true.
        assert!(theory.derive(0, &[], vec![]).is_err());
    }

    #[test]
    fn wasm_exact_typed_relation_fragment_is_censused() {
        let defs = crate::wasm::spec::wasm_spec();
        fn visit<'a>(defs: &'a [SpecTecDef], out: &mut Vec<&'a SpecTecDef>) {
            for def in defs {
                match def {
                    SpecTecDef::Rel { .. } => out.push(def),
                    SpecTecDef::Rec { ds } => visit(ds, out),
                    _ => {}
                }
            }
        }
        let mut relations = Vec::new();
        visit(&defs, &mut relations);
        let audit_families = TypeFamilies::new(&defs);
        let mut accepted = Vec::new();
        let mut refused = std::collections::BTreeMap::new();
        let mut structural_indexed_cases = std::collections::BTreeMap::new();
        for def in relations {
            match semantic_relation(def, &defs) {
                Ok(theory) => accepted.push(theory.name().to_owned()),
                Err(error) => {
                    let reason = error.to_string();
                    if reason.ends_with("parametric field/case not modelled yet") {
                        let SpecTecDef::Rel { t, .. } = def else {
                            unreachable!()
                        };
                        let mut blockers = Vec::new();
                        fn typ_names<'a>(
                            ty: &'a covalence_spectec::ast::SpecTecTyp,
                            out: &mut Vec<&'a str>,
                        ) {
                            match ty {
                                covalence_spectec::ast::SpecTecTyp::Var { x, as1 } => {
                                    out.push(x);
                                    for arg in as1 {
                                        if let covalence_spectec::ast::SpecTecArg::Typ { t } = arg {
                                            typ_names(t, out);
                                        }
                                    }
                                }
                                covalence_spectec::ast::SpecTecTyp::Tup { ets } => {
                                    for bind in ets {
                                        let covalence_spectec::ast::SpecTecTypBind::Bind {
                                            typ,
                                            ..
                                        } = bind;
                                        typ_names(typ, out);
                                    }
                                }
                                covalence_spectec::ast::SpecTecTyp::Iter { t1, .. } => {
                                    typ_names(t1, out)
                                }
                                _ => {}
                            }
                        }
                        let mut pending = Vec::new();
                        typ_names(t, &mut pending);
                        let mut seen = std::collections::BTreeSet::new();
                        while let Some(name) = pending.pop() {
                            if !seen.insert(name.to_owned()) {
                                continue;
                            }
                            if let Some(family) = crate::wasm::type_family::TypeFamilySource::family(
                                &audit_families,
                                name,
                            ) {
                                if family
                                    .instances
                                    .iter()
                                    .any(|instance| match &instance.shape {
                                        crate::wasm::type_family::TypeShape::Variant(cases) => {
                                            cases.iter().any(|case| !case.params.is_empty())
                                        }
                                        crate::wasm::type_family::TypeShape::Struct(fields) => {
                                            fields.iter().any(|field| !field.params.is_empty())
                                        }
                                        _ => false,
                                    })
                                {
                                    blockers.push(name.to_owned());
                                }
                                pending.extend(family.dependencies());
                            }
                        }
                        blockers.sort();
                        blockers.dedup();
                        *structural_indexed_cases.entry(blockers).or_insert(0usize) += 1;
                    }
                    *refused.entry(reason).or_insert(0usize) += 1
                }
            }
        }
        assert_eq!(
            accepted,
            [
                "Defaultable",
                "Nondefaultable",
                "NotationTypingPremise",
                "NotationTypingPremisedots",
                "NotationTypingScheme",
            ]
        );
        assert_eq!(refused.values().sum::<usize>(), 120);
        let count = |suffix: &str| {
            refused
                .iter()
                .find(|(reason, _)| reason.ends_with(suffix))
                .map(|(_, count)| *count)
        };
        assert_eq!(count("relation carrier is unresolved"), Some(120));
        assert_eq!(count("parametric field/case not modelled yet"), None);
        assert!(structural_indexed_cases.is_empty());
    }

    fn replay_sealed_valtype_case(relation: &str, constructor: usize) -> Thm {
        use crate::init::ext::ThmExt;

        let defs = crate::wasm::spec::wasm_spec();
        let relation_def = find_relation(&defs, relation).unwrap();
        let theory = semantic_relation(relation_def, &defs).unwrap();
        let type_ctx = syntax::TypeCtx::new(&defs);
        let signature = syntax::mutual_church_signature("valtype", &type_ctx).unwrap();
        assert_eq!(signature.constructors()[constructor].owner(), "valtype");
        let payload = covalence_hol_eval::defs::unit_nil();
        let universal = signature
            .carved_u_constructor(constructor, payload.clone())
            .unwrap();
        let wf = signature
            .carved_nonrecursive_wf_witness(constructor, payload.clone())
            .unwrap();
        let sealed = syntax::sealed_wasm_mutual_carriers().unwrap();
        let definition = &sealed.definitions()["valtype"];
        let value = definition.abs.clone().apply(universal.clone()).unwrap();
        let rep_abs = definition
            .rep_abs_fwd()
            .unwrap()
            .all_elim(universal.clone())
            .unwrap()
            .imp_elim(wf)
            .unwrap();
        let root = signature
            .carved_u_root_equation(constructor, payload)
            .unwrap();

        let rule = &theory.rules[0];
        let TypedPremise::Side(generic_side) = &rule.premises[0] else {
            panic!("sealed valtype relation must retain its classifier side premise");
        };
        let binder = Term::free(&rule.binders[0].0, rule.binders[0].1.clone());
        let side =
            covalence_core::subst::subst_free(generic_side, binder.as_free().unwrap(), &value);
        let mut reduction = crate::init::eq::beta_nf(side.clone());
        reduction = reduction.rhs_conv(|term| term.rw_all(&rep_abs)).unwrap();
        reduction = reduction.rhs_conv(|term| term.rw_all(&root)).unwrap();
        let normal = reduction.concl().as_eq().unwrap().1.clone();
        let disjunct_count = if relation == "Defaultable" { 6 } else { 2 };
        let mut leftmost = normal.clone();
        let mut rights = Vec::new();
        for _ in 1..disjunct_count {
            let (function, right) = leftmost.as_app().expect("classifier must be disjunction");
            let (_, left) = function
                .as_app()
                .expect("classifier disjunction must be binary");
            rights.push(right.clone());
            leftmost = left.clone();
        }
        let (left, right) = leftmost
            .as_eq()
            .expect("leftmost classifier case must be equality");
        assert_eq!(
            left, right,
            "selected source constructor must match first case"
        );
        let mut normal_proof = Thm::refl(left.clone()).unwrap();
        for right in rights.into_iter().rev() {
            normal_proof = normal_proof.or_intro_l(right).unwrap();
        }
        assert_eq!(normal_proof.concl(), &normal);
        let side_proof = reduction.sym().unwrap().eq_mp(normal_proof).unwrap();
        assert!(side_proof.hyps().is_empty());

        let theorem = theory
            .derive(0, &[value.clone()], vec![Premise::Side(side_proof)])
            .unwrap();
        assert!(theorem.hyps().is_empty());
        assert_eq!(theorem.concl(), &theory.holds(value).unwrap());
        theorem
    }

    #[test]
    fn defaultability_relations_replay_over_distinct_sealed_valtype_cases() {
        let defaultable_i32 = replay_sealed_valtype_case("Defaultable", 34);
        let nondefaultable_bot = replay_sealed_valtype_case("Nondefaultable", 40);
        assert_ne!(defaultable_i32.concl(), nondefaultable_bot.concl());
    }

    #[test]
    fn bundled_notation_scheme_rule_replays_against_exact_external_predicates() {
        let defs = crate::wasm::spec::wasm_spec();
        let scheme_def = find_relation(&defs, "NotationTypingScheme").unwrap();
        let theory = semantic_relation(scheme_def, &defs).unwrap();
        assert_eq!(theory.rule_count(), 1);
        let rule = &theory.rules[0];
        assert_eq!(rule.premises.len(), 4);

        let arguments: Vec<_> = rule
            .binders
            .iter()
            .enumerate()
            .map(|(i, (_, ty))| Term::free(format!("notation_arg_{i}"), ty.clone()))
            .collect();
        let instantiate = |term: &Term| {
            rule.binders.iter().zip(&arguments).fold(
                term.clone(),
                |term, ((name, ty), replacement)| {
                    let variable = Term::free(name, ty.clone());
                    covalence_core::subst::subst_free(
                        &term,
                        variable.as_free().unwrap(),
                        replacement,
                    )
                },
            )
        };
        let premises = rule
            .premises
            .iter()
            .map(|premise| {
                let TypedPremise::Side(statement) = premise else {
                    panic!("notation dependencies must be closed external predicates");
                };
                Premise::Side(Thm::assume(instantiate(statement)).unwrap())
            })
            .collect();
        let theorem = theory.derive(0, &arguments, premises).unwrap();
        assert_eq!(theorem.hyps().len(), 4);
        assert_eq!(
            theorem.concl(),
            &theory.holds(instantiate(&rule.conclusion)).unwrap()
        );
    }
}
