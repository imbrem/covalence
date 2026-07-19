//! **`Else` (`-- otherwise`) preprocessing** — rewrite each `SpecTecPrem::Else`
//! into ordinary premises representing the conjunction of **negations** of
//! each textually-earlier sibling's applicability (design note leg 5,
//! `notes/vibes/logics/spectec-total-load.md`). Shared relation judgements and
//! condition conjuncts are factored against the current rule before negation.
//!
//! ## Semantics
//!
//! `-- otherwise` means "no textually-preceding rule of the same conclusion
//! group applies". Writing `A_j` for rule `j`'s own-premise conjunction, rule
//! `j`'s effective guard is `otherwise_j ∧ A_j`; induction gives
//! `⋀_{j<k} ¬(effective_j) = ⋀_{j<k} ¬A_j`, so earlier `Else` markers are
//! ignored. Under premises `P` already required by the current rule,
//! `P ∧ ¬(P ∧ G)` is simplified exactly to `P ∧ ¬G`. Remaining ordinary
//! conditions become one `If` premise per sibling, with De Morgan pushed to
//! the leaves. A remaining positive relation judgement cannot be negated in
//! the positive Horn encoding and therefore makes the rewrite fail closed.
//!
//! ## Sibling matching (safety-critical)
//!
//! A missed sibling would *drop* a negated guard — an over-approximation. So
//! matching is conservative: an earlier rule is skipped **only** on a rigid
//! pattern clash (provably disjoint conclusions); it becomes a sibling when its
//! conclusion pattern corresponds to ours by a variable mapping; and *any*
//! indeterminate comparison fails the whole rewrite ([`ElseStatus::Failed`] —
//! the rule then loads with an opaque `else` antecedent, never wrongly).
//! Reduction-shaped conclusions (`Tup[lhs, rhs]`) are matched on the redex
//! `lhs` only (the corpus shape; sibling RHSs legitimately differ).
//!
//! Negation ([`negate`]) is a pure `SpecTecExp → SpecTecExp` transform pushed
//! to the leaves: De Morgan, `Eq ↔ Ne`, `Lt ↔ Ge`, `Le ↔ Gt`, `¬(bool call)`
//! stays `Un Not` (flattened through the graph relation with result `false`).

use std::collections::BTreeMap;

use covalence_spectec::ast::{
    SpecTecBinOp, SpecTecBoolTyp, SpecTecCmpOp, SpecTecExp, SpecTecExpField, SpecTecIterExp,
    SpecTecOpTyp, SpecTecParam, SpecTecPath, SpecTecPrem, SpecTecRule, SpecTecTyp, SpecTecUnOp,
};

use super::super::syntax::CaseCatalogue;

/// Internal relation-name prefix used to carry an exact negative
/// single-judgement applicability test from Else preprocessing to the HOL
/// decision-family boundary.
///
/// NUL cannot occur in a SpecTec identifier, so this cannot collide with a
/// source relation.  The marker is consumed by `flatten`; it is never emitted
/// as a HOL source judgement.
pub(super) const NEGATED_RULE_PREFIX: &str = "\0decision-no:";

/// What happened to a rule under [`preprocess_else`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ElseStatus {
    /// The rule had no `Else` premise (unchanged).
    NoElse,
    /// Its `Else` was rewritten into `negated` `If` premises (one per sibling).
    Rewritten { negated: usize },
    /// The rewrite refused (reason bucket); the `Else` premise is left in
    /// place, so lowering keeps the rule loaded-but-unfirable via `opaque`.
    Failed(String),
}

/// A rule after `Else` preprocessing.
#[derive(Debug, Clone)]
pub struct PreprocessedRule {
    pub rule: SpecTecRule,
    pub status: ElseStatus,
}

/// Preprocess one relation's rules **in order**, rewriting each `Else` premise
/// into the negations of its earlier siblings' `If` conditions. Total: refusals
/// keep the original rule (with its `Else`) and report why.
pub fn preprocess_else(rules: &[SpecTecRule]) -> Vec<PreprocessedRule> {
    preprocess_else_impl(rules, None)
}

/// Catalogue-aware [`preprocess_else`]. Besides the general correspondence
/// rewrite, this can simplify a finite constructor-pattern complement when the
/// catalogue proves the scrutinized variant exhaustive.
pub fn preprocess_else_with_catalogue(
    rules: &[SpecTecRule],
    cat: &CaseCatalogue,
) -> Vec<PreprocessedRule> {
    preprocess_else_impl(rules, Some(cat))
}

fn preprocess_else_impl(
    rules: &[SpecTecRule],
    cat: Option<&CaseCatalogue>,
) -> Vec<PreprocessedRule> {
    rules
        .iter()
        .enumerate()
        .map(|(k, rule)| {
            let SpecTecRule::Rule { prs, .. } = rule;
            if !prs.iter().any(|p| matches!(p, SpecTecPrem::Else)) {
                return PreprocessedRule {
                    rule: rule.clone(),
                    status: ElseStatus::NoElse,
                };
            }
            let rewritten = cat
                .and_then(|cat| handler_catch_complement(rule, &rules[..k], cat))
                .map(Ok)
                .unwrap_or_else(|| rewrite_else(rule, &rules[..k]));
            match rewritten {
                Ok((rule, negated)) => PreprocessedRule {
                    rule,
                    status: ElseStatus::Rewritten { negated },
                },
                Err(reason) => PreprocessedRule {
                    rule: rule.clone(),
                    status: ElseStatus::Failed(reason),
                },
            }
        })
        .collect()
}

/// The finite complement of the exception-handler catch dispatch.
///
/// The source fallback scrutinizes one `catch`, whose declared variant has
/// exactly `CATCH`, `CATCH_REF`, `CATCH_ALL`, and `CATCH_ALL_REF`. The first
/// two earlier clauses are conditional on the exception tag; the latter two
/// are unconditional. Hence the complement is the disjunction
///
/// ```text
/// catch = CATCH(x,l)     ∧ tag mismatch
/// catch = CATCH_REF(x,l) ∧ tag mismatch
/// ```
///
/// Constructor equalities expose `x,l` as clause-instantiation witnesses.
/// The two unconditional constructors contribute no branch. Every source and
/// catalogue shape is checked; any drift returns `None` and the ordinary
/// fail-closed path remains in force.
fn handler_catch_complement(
    rule: &SpecTecRule,
    prior: &[SpecTecRule],
    cat: &CaseCatalogue,
) -> Option<(SpecTecRule, usize)> {
    let SpecTecRule::Rule { x, ps, op, e, prs } = rule;
    if x != "throw_ref-handler-next"
        || !prs.iter().any(|p| matches!(p, SpecTecPrem::Else))
        || !ps.iter().any(|p| {
            matches!(
                p,
                SpecTecParam::Exp {
                    x,
                    t: SpecTecTyp::Var { x: ty, as1 }
                } if x == "catch" && ty == "catch" && as1.is_empty()
            )
        })
    {
        return None;
    }
    let declared = cat.cases_of("catch")?;
    if declared.len() != 4 {
        return None;
    }
    let (our_catches, our_body) = handler_parts(redex(e))?;
    let (our_head, our_tail) = cons_parts(our_catches)?;
    if !matches!(our_head, SpecTecExp::Var { id } if id == "catch") {
        return None;
    }
    let expected = [
        ("throw_ref-handler-catch", true),
        ("throw_ref-handler-catch_ref", true),
        ("throw_ref-handler-catch_all", false),
        ("throw_ref-handler-catch_all_ref", false),
    ];
    let mut seen_keys = std::collections::BTreeSet::new();
    let mut branches = Vec::new();
    for (name, conditional) in expected {
        let sibling = prior.iter().find(|r| {
            let SpecTecRule::Rule { x, .. } = r;
            x == name
        })?;
        let SpecTecRule::Rule {
            e: sibling_e,
            prs: sibling_prs,
            ..
        } = sibling;
        let (sibling_catches, sibling_body) = handler_parts(redex(sibling_e))?;
        let (sibling_head, sibling_tail) = cons_parts(sibling_catches)?;
        let SpecTecExp::Case { op: ctor_op, .. } = sibling_head else {
            return None;
        };
        seen_keys.insert(crate::wasm::encode::mixop_key(ctor_op));
        // The tail and thrown exception body are shared. This also rejects a
        // coincidentally named rule with a different handler shape.
        let mut common = BTreeMap::new();
        if sibling_tail != our_tail || sibling_body != our_body {
            return None;
        }

        if !conditional {
            if !sibling_prs.is_empty() {
                return None;
            }
            continue;
        }
        if sibling_prs
            .iter()
            .any(|p| !matches!(p, SpecTecPrem::If { .. }))
        {
            return None;
        }

        // Preserve sibling-local constructor payload variables as fresh
        // witnesses, while translating all shared variables through the
        // correspondence established above.
        let mut all_vars = Vec::new();
        free_vars(redex(sibling_e), &mut all_vars);
        for prem in sibling_prs {
            if let SpecTecPrem::If { e } = prem {
                free_vars(e, &mut all_vars);
            }
        }
        for id in all_vars {
            common.entry(id.clone()).or_insert(SpecTecExp::Var { id });
        }
        let constructor = subst_vars(sibling_head, &common).ok()?;
        let mut guards = Vec::new();
        for prem in sibling_prs {
            let SpecTecPrem::If { e } = prem else {
                unreachable!()
            };
            guards.push(subst_vars(e, &common).ok()?);
        }
        let mut pattern_vars = Vec::new();
        free_vars(redex(e), &mut pattern_vars);
        free_vars(&constructor, &mut pattern_vars);
        let projected = super::decs::project_guard_witnesses(&guards, &pattern_vars)?;
        let mismatch = negate_conj(&projected).ok()?;
        let selects_constructor = SpecTecExp::Cmp {
            op: SpecTecCmpOp::Eq,
            t: bool_ty(),
            e1: Box::new(our_head.clone()),
            e2: Box::new(constructor),
        };
        branches.push(SpecTecExp::Bin {
            op: SpecTecBinOp::And,
            t: bool_ty(),
            e1: Box::new(selects_constructor),
            e2: Box::new(mismatch),
        });
    }

    let declared: std::collections::BTreeSet<_> = declared.iter().cloned().collect();
    if seen_keys != declared || branches.len() != 2 {
        return None;
    }
    let guard = SpecTecExp::Bin {
        op: SpecTecBinOp::Or,
        t: bool_ty(),
        e1: Box::new(branches.remove(0)),
        e2: Box::new(branches.remove(0)),
    };
    let mut new_prs = Vec::with_capacity(prs.len());
    for prem in prs {
        if matches!(prem, SpecTecPrem::Else) {
            new_prs.push(SpecTecPrem::If { e: guard.clone() });
        } else {
            new_prs.push(prem.clone());
        }
    }
    Some((
        SpecTecRule::Rule {
            x: x.clone(),
            ps: ps.clone(),
            op: op.clone(),
            e: e.clone(),
            prs: new_prs,
        },
        4,
    ))
}

/// `(catch-list, handler-body)` of the first `HANDLER_` node in `e`.
fn handler_parts(e: &SpecTecExp) -> Option<(&SpecTecExp, &SpecTecExp)> {
    if let SpecTecExp::Case { op, e1 } = strip_sub(e)
        && crate::wasm::encode::mixop_key(op).starts_with("HANDLER_")
        && let SpecTecExp::Tup { es } = strip_sub(e1)
        && es.len() == 3
    {
        return Some((&es[1], &es[2]));
    }
    let mut kids = Vec::new();
    children(e, &mut kids);
    kids.into_iter().find_map(handler_parts)
}

/// The head and tail of a syntactic nonempty list `List[head] ++ tail`.
fn cons_parts(e: &SpecTecExp) -> Option<(&SpecTecExp, &SpecTecExp)> {
    let SpecTecExp::Cat { e1, e2 } = strip_sub(e) else {
        return None;
    };
    let SpecTecExp::List { es } = strip_sub(e1) else {
        return None;
    };
    (es.len() == 1).then(|| (&es[0], &**e2))
}

/// Rewrite the `Else` premise of `rule` against the textually-earlier `prior`
/// rules. Returns the rewritten rule and the number of negated-guard premises.
fn rewrite_else(rule: &SpecTecRule, prior: &[SpecTecRule]) -> Result<(SpecTecRule, usize), String> {
    let SpecTecRule::Rule { x, ps, op, e, prs } = rule;
    let our_lhs = redex(e);

    // Collect one negated applicability premise per sibling.
    let our_tag = instr_tag(our_lhs);
    let mut negations = Vec::new();
    for p in prior {
        let SpecTecRule::Rule {
            x: prior_name,
            e: pe,
            prs: pprs,
            ..
        } = p;
        // Group discriminator: upstream's `otherwise` desugaring is scoped to
        // the rule group of one instruction, and step-rule redexes end in
        // their instruction's `Case` tag. A prior rule with a different (or
        // no) instruction tag is not in the group — e.g. the generic
        // `trap-instrs`/`throw_ref-instrs` propagation rules, whose wildcard
        // patterns are disjoint from any concrete instruction group by
        // *typing* (a `val*` slot never holds `TRAP`). An untaggable own
        // conclusion refuses (conservative).
        let Some(our_tag) = &our_tag else {
            return Err("else-group-untaggable".into());
        };
        if instr_tag(redex(pe)).as_deref() != Some(our_tag.as_str()) {
            continue;
        }
        let mut map = match correspond(redex(pe), our_lhs) {
            Corr::Disjoint => continue, // provably never overlaps: not a sibling
            Corr::Overlap(map) => map,
            Corr::Unknown => {
                let SpecTecRule::Rule { x: px, .. } = p;
                return Err(format!("sibling-undecided:{px}"));
            }
        };
        // Factor relation judgements shared by the sibling and current rule.
        // This may extend the variable correspondence with outputs bound by
        // the shared judgement.
        let mut unmatched_rules = Vec::new();
        for pp in pprs {
            match pp {
                SpecTecPrem::If { .. } | SpecTecPrem::Else => {}
                SpecTecPrem::Rule {
                    x: rx,
                    as1,
                    op: rop,
                    e: re,
                } => {
                    // Under a Rule premise shared by the current clause,
                    // `shared ∧ ¬(shared ∧ guards)` is exactly
                    // `shared ∧ ¬guards`. Factor it rather than trying to
                    // negate a relation judgement. Non-expression rule
                    // arguments are rare here and remain conservative.
                    if !as1.is_empty() {
                        return Err("sibling-rule-premise".into());
                    }
                    let mut shared_map = None;
                    for ours in prs {
                        let SpecTecPrem::Rule {
                            x,
                            as1,
                            op,
                            e: ours_e,
                        } = ours
                        else {
                            continue;
                        };
                        if x != rx || !as1.is_empty() || op != rop {
                            continue;
                        }
                        // A textually identical shared judgement can bind
                        // variables not mentioned by the outer conclusion.
                        // Extend the correspondence with those identity
                        // bindings before translating the sibling's guards.
                        let mut exact_candidate = map.clone();
                        let mut vars = Vec::new();
                        free_vars(re, &mut vars);
                        for id in vars {
                            exact_candidate
                                .entry(id.clone())
                                .or_insert(SpecTecExp::Var { id });
                        }
                        if subst_vars(re, &exact_candidate).as_ref().ok() == Some(ours_e) {
                            shared_map = Some(exact_candidate);
                            break;
                        }
                        let mut candidate = map.clone();
                        if matches!(unify(re, ours_e, &mut candidate), U::Ok) {
                            shared_map = Some(candidate);
                            break;
                        }
                    }
                    if let Some(candidate) = shared_map {
                        map = candidate;
                    } else {
                        // Outputs introduced by an unmatched judgement are
                        // existential witnesses for that sibling's
                        // applicability.  Give them identity mappings so
                        // subsequent conditions can be translated as part of
                        // the same conjunction.  They are never leaked into a
                        // rewritten rule unless the whole conjunction can be
                        // represented; the unsupported Rule-and-If case below
                        // still fails closed.
                        let mut vars = Vec::new();
                        free_vars(re, &mut vars);
                        for id in vars {
                            map.entry(id.clone()).or_insert(SpecTecExp::Var { id });
                        }
                        unmatched_rules.push((rx, as1, rop, re));
                    }
                }
                SpecTecPrem::Iter { .. } => return Err("sibling-iter-premise".into()),
                SpecTecPrem::Let { .. } => return Err("sibling-let-premise".into()),
            }
        }

        // Under a condition conjunct shared by the current rule,
        // `shared ∧ ¬(shared ∧ guards)` is exactly
        // `shared ∧ ¬guards`. Match at conjunction granularity so a sibling
        // `A ∧ B` and current `B` leave only `¬A`.
        let mut our_conds = Vec::new();
        for pp in prs {
            if let SpecTecPrem::If { e } = pp {
                conjuncts(e, &mut our_conds);
            }
        }
        let mut conds = Vec::new();
        for pp in pprs {
            let SpecTecPrem::If { e } = pp else {
                continue;
            };
            let mut sibling_conds = Vec::new();
            conjuncts(e, &mut sibling_conds);
            for sibling_cond in sibling_conds {
                let mut shared_map = None;
                for our_cond in &our_conds {
                    if let Some(candidate) = shared_expression(sibling_cond, our_cond, &map) {
                        shared_map = Some(candidate);
                        break;
                    }
                }
                if let Some(candidate) = shared_map {
                    map = candidate;
                } else {
                    conds.push(subst_vars(sibling_cond, &map)?);
                }
            }
        }
        match unmatched_rules.as_slice() {
            [] => negations.push(SpecTecPrem::If {
                e: negate_conj(&conds)?,
            }),
            // `¬R(args)` is routed to the positive, theorem-certified
            // `decision.R(args,false)` interface.  Until that family is
            // installed, lowering remains honestly opaque under the precise
            // `decision.R` reason.  A conjunction `R ∧ condition` would need
            // `¬R ∨ ¬condition`; positive Horn premises cannot express that
            // disjunction, so it remains fail-closed below.
            [(rx, as1, rop, re)] if conds.is_empty() && as1.is_empty() => {
                negations.push(SpecTecPrem::Rule {
                    x: format!("{NEGATED_RULE_PREFIX}{rx}"),
                    as1: Vec::new(),
                    op: (*rop).clone(),
                    e: subst_vars(re, &map)?,
                });
            }
            [(rx, as1, _, _)] => {
                return Err(format!(
                    "sibling-rule-premise:{rx}:args{}:conds{}",
                    as1.len(),
                    conds.len()
                ));
            }
            _ => {
                let names = unmatched_rules
                    .iter()
                    .map(|(x, as1, _, _)| format!("{x}/{}", as1.len()))
                    .collect::<Vec<_>>()
                    .join(",");
                return Err(format!(
                    "sibling-rule-premise:{prior_name}:multiple:{names}:conds{}",
                    conds.len()
                ));
            }
        }
    }

    // Splice the negations in place of the `Else` premise(s).
    let mut new_prs = Vec::with_capacity(prs.len() + negations.len());
    for p in prs {
        if matches!(p, SpecTecPrem::Else) {
            new_prs.extend(negations.iter().cloned());
        } else {
            new_prs.push(p.clone());
        }
    }
    let n = negations.len();
    Ok((
        SpecTecRule::Rule {
            x: x.clone(),
            ps: ps.clone(),
            op: op.clone(),
            e: e.clone(),
            prs: new_prs,
        },
        n,
    ))
}

/// The redex pattern of a conclusion: reduction judgements are pairs
/// `Tup[lhs, rhs]` whose RHSs legitimately differ between siblings — match on
/// the `lhs` only; anything else is matched whole.
fn redex(e: &SpecTecExp) -> &SpecTecExp {
    match e {
        SpecTecExp::Tup { es } if es.len() >= 2 => &es[0],
        other => other,
    }
}

/// The **group key** of a step-rule redex: the `Case` key of the last element
/// of the instruction list (`val* instr` patterns end in the instruction),
/// falling back to the innermost enclosing `Case` key. This mirrors how the
/// upstream SpecTec middle-end scopes `otherwise` desugaring: to the rule
/// group of one instruction (the `$t_totalize` clauses in the vendored
/// `assets/spectec` test suite) — generic propagation rules (`trap-instrs`,
/// `val* TRAP instr*`) are *not* in any instruction's group even though their
/// wildcard patterns syntactically overlap everything (typing keeps them
/// disjoint). Deterministic on same-shaped conclusions, so genuine group
/// members always agree; `None` when no key is extractable.
///
/// **Known coarseness (reviewed, deliberately kept):** wrapper rules tag by
/// the wrapper's key, so e.g. every `HANDLER_`-wrapped rule initially shares
/// one tag. Refining the tag by diving into the wrapper payload's instruction
/// list is **unsound as a group discriminator**: a payload ending in a
/// variable segment has no reliable last literal. Instead, [`unify`] proves
/// rigidly incompatible wrapper bodies disjoint (the return-call/throw case),
/// while [`handler_catch_complement`] handles the genuine finite catch-pattern
/// overlap under an exhaustive catalogue check. Coarse tags therefore only
/// add candidates, the conservative direction.
fn instr_tag(e: &SpecTecExp) -> Option<String> {
    use SpecTecExp as E;
    match strip_sub(e) {
        E::List { es } => match strip_sub(es.last()?) {
            E::Case { op, .. } => Some(crate::wasm::encode::mixop_key(op)),
            _ => None,
        },
        E::Cat { e2, .. } => instr_tag(e2),
        // Wrappers (`z; instr*`, handler frames): prefer the payload's tag,
        // fall back to the wrapper's own key.
        E::Case { op, e1 } => instr_tag(e1).or_else(|| Some(crate::wasm::encode::mixop_key(op))),
        E::Tup { es } => instr_tag(es.last()?),
        _ => None,
    }
}

/// How a sibling candidate's pattern relates to ours.
///
/// `pub(super)`: the `Dec` clause-order machinery ([`super::decs`]) reuses
/// the correspondence check for its confluent-overlap detection.
pub(super) enum Corr {
    /// Rigidly disjoint — provably not a sibling.
    Disjoint,
    /// Corresponds: sibling metavariable → our sub-expression.
    Overlap(BTreeMap<String, SpecTecExp>),
    /// Cannot decide — the whole rewrite must refuse (soundness).
    Unknown,
}

pub(super) fn correspond(sib: &SpecTecExp, ours: &SpecTecExp) -> Corr {
    let mut map = BTreeMap::new();
    match unify(sib, ours, &mut map) {
        U::Ok => Corr::Overlap(map),
        U::Clash => Corr::Disjoint,
        U::Unknown => Corr::Unknown,
    }
}

enum U {
    Ok,
    Clash,
    Unknown,
}

impl U {
    fn and(self, other: impl FnOnce() -> U) -> U {
        match self {
            U::Ok => other(),
            // A rigid clash elsewhere keeps the pair disjoint even if this
            // component is indeterminate — but the *conservative* combination
            // is: any Clash ⇒ Clash dominates only when sound. Disjointness
            // needs just one clash, so Clash wins; Unknown otherwise taints.
            U::Clash => U::Clash,
            U::Unknown => match other() {
                U::Clash => U::Clash,
                _ => U::Unknown,
            },
        }
    }
}

/// Strip type-subsumption casts (they don't affect matching).
fn strip_sub(e: &SpecTecExp) -> &SpecTecExp {
    match e {
        SpecTecExp::Sub { e1, .. } => strip_sub(e1),
        other => other,
    }
}

/// Unify a sibling *pattern* against our *pattern*: sibling metavariables bind
/// to our sub-expressions (consistently); rigid structure must agree. `Clash`
/// = provably disjoint; `Unknown` = anything indeterminate (flexible list
/// splits, calls, our-var-vs-their-structure, inconsistent nonlinear binds).
fn unify(sib: &SpecTecExp, ours: &SpecTecExp, map: &mut BTreeMap<String, SpecTecExp>) -> U {
    use SpecTecExp as E;
    let (sib, ours) = (strip_sub(sib), strip_sub(ours));
    if let E::Var { id } = sib {
        return match map.get(id) {
            Some(prev) if prev == ours => U::Ok,
            Some(_) => U::Unknown, // nonlinear sibling pattern, differing binds
            None => {
                map.insert(id.clone(), ours.clone());
                U::Ok
            }
        };
    }
    if matches!(ours, E::Var { .. }) {
        // Sibling is more specific than us: it applies to only part of our
        // instances — a conditional overlap we can't negate. Refuse.
        return U::Unknown;
    }
    match (sib, ours) {
        (E::Case { op: o1, e1: a }, E::Case { op: o2, e1: b }) => {
            if o1 == o2 {
                unify(a, b, map)
            } else {
                U::Clash
            }
        }
        (E::Tup { es: a }, E::Tup { es: b }) | (E::List { es: a }, E::List { es: b }) => {
            if a.len() != b.len() {
                return U::Clash;
            }
            let mut acc = U::Ok;
            for (x, y) in a.iter().zip(b) {
                acc = acc.and(|| unify(x, y, map));
                if matches!(acc, U::Clash) {
                    return U::Clash;
                }
            }
            acc
        }
        (E::Num { n: a }, E::Num { n: b }) => {
            use covalence_spectec::ast::SpecTecNum as N;
            if a == b {
                U::Ok
            } else {
                // A value clash is a clash only within one literal kind:
                // cross-kind literals can denote the same value (`Nat 2` vs
                // `Int 2`), and `Rat`/`Real` carry unnormalised strings.
                match (a, b) {
                    (N::Nat(_), N::Nat(_)) | (N::Int(_), N::Int(_)) => U::Clash,
                    _ => U::Unknown,
                }
            }
        }
        (E::Bool { b: a }, E::Bool { b }) => {
            if a == b {
                U::Ok
            } else {
                U::Clash
            }
        }
        (E::Text { t: a }, E::Text { t: b }) => {
            if a == b {
                U::Ok
            } else {
                U::Clash
            }
        }
        (E::Opt { eo: None }, E::Opt { eo: None }) => U::Ok,
        (E::Opt { eo: Some(a) }, E::Opt { eo: Some(b) }) => unify(a, b, map),
        (E::Opt { .. }, E::Opt { .. }) => U::Clash,
        // An exact-length literal list vs a concatenation can be compared
        // exactly enough to prove disjointness.  Non-literal Cat segments are
        // conservatively treated as arbitrary (possibly-empty) list
        // languages; if no allocation of those segments places every fixed
        // literal on a non-clashing exact element, the two list languages are
        // disjoint.  A surviving allocation remains Unknown: choosing its
        // split, and binding variables inside flexible segments, belongs to a
        // fuller pattern compiler rather than this safety check.
        (E::List { es }, cat @ E::Cat { .. }) | (cat @ E::Cat { .. }, E::List { es }) => {
            if min_cat_len(cat) > es.len() || cat_exact_disjoint(cat, es, map) {
                U::Clash
            } else {
                U::Unknown
            }
        }
        // Distinct rigid kinds are disjoint values.
        (a, b) if rigid_kind(a).is_some() && rigid_kind(b).is_some() => {
            if rigid_kind(a) == rigid_kind(b) {
                // Same rigid kind but not handled above (unreachable in
                // practice) — stay conservative.
                U::Unknown
            } else {
                U::Clash
            }
        }
        // Cat / Iter / Call / anything flexible: cannot decide.
        _ => U::Unknown,
    }
}

/// A lower bound on the length of the list a pattern matches: literal
/// segments count, everything else (vars, iterations, calls) contributes 0.
fn min_cat_len(e: &SpecTecExp) -> usize {
    match strip_sub(e) {
        SpecTecExp::List { es } => es.len(),
        SpecTecExp::Cat { e1, e2 } => min_cat_len(e1) + min_cat_len(e2),
        _ => 0,
    }
}

/// One piece of a flattened concatenation language. Literal `List` nodes
/// contribute fixed elements; every other expression is widened to an
/// arbitrary, possibly-empty list segment. Widening is deliberate: failure to
/// find an overlap in the wider language is a sound disjointness proof, while
/// a possible overlap merely leaves [`unify`] indeterminate.
enum CatPiece<'a> {
    Fixed(&'a [SpecTecExp]),
    Flex,
}

fn cat_pieces<'a>(e: &'a SpecTecExp, out: &mut Vec<CatPiece<'a>>) {
    match strip_sub(e) {
        SpecTecExp::Cat { e1, e2 } => {
            cat_pieces(e1, out);
            cat_pieces(e2, out);
        }
        SpecTecExp::List { es } => out.push(CatPiece::Fixed(es)),
        _ => out.push(CatPiece::Flex),
    }
}

/// Whether the widened language of `cat` has empty intersection with the exact
/// list `es`. This is a bounded search: each flexible segment receives
/// `0..=es.len()` elements, and fixed pieces are checked by the ordinary
/// structural unifier. `Unknown` is overlap-compatible; only a rigid `Clash`
/// rejects a placement.
fn cat_exact_disjoint(
    cat: &SpecTecExp,
    es: &[SpecTecExp],
    initial: &BTreeMap<String, SpecTecExp>,
) -> bool {
    let mut pieces = Vec::new();
    cat_pieces(cat, &mut pieces);

    fn overlaps(
        pieces: &[CatPiece<'_>],
        es: &[SpecTecExp],
        pos: usize,
        map: &BTreeMap<String, SpecTecExp>,
    ) -> bool {
        let Some((piece, rest)) = pieces.split_first() else {
            return pos == es.len();
        };
        match piece {
            CatPiece::Fixed(fixed) => {
                let Some(slice) = es.get(pos..pos.saturating_add(fixed.len())) else {
                    return false;
                };
                if slice.len() != fixed.len() {
                    return false;
                }
                let mut candidate = map.clone();
                for (pattern, exact) in fixed.iter().zip(slice) {
                    if matches!(unify(pattern, exact, &mut candidate), U::Clash) {
                        return false;
                    }
                }
                overlaps(rest, es, pos + fixed.len(), &candidate)
            }
            CatPiece::Flex => {
                // The segment may consume any remaining prefix. Try every
                // bounded allocation; a single possible placement prevents a
                // disjointness claim.
                (pos..=es.len()).any(|next| overlaps(rest, es, next, map))
            }
        }
    }

    !overlaps(&pieces, es, 0, initial)
}

/// The rigid discriminator of a pattern node, if it has one.
fn rigid_kind(e: &SpecTecExp) -> Option<u8> {
    use SpecTecExp as E;
    match e {
        E::Case { .. } => Some(0),
        E::Tup { .. } => Some(1),
        E::List { .. } => Some(2),
        E::Num { .. } => Some(3),
        E::Bool { .. } => Some(4),
        E::Text { .. } => Some(5),
        E::Opt { .. } => Some(6),
        _ => None,
    }
}

fn bool_ty() -> SpecTecOpTyp {
    SpecTecOpTyp::Bool(SpecTecBoolTyp::Bool)
}

fn conjuncts<'a>(e: &'a SpecTecExp, out: &mut Vec<&'a SpecTecExp>) {
    if let SpecTecExp::Bin {
        op: SpecTecBinOp::And,
        e1,
        e2,
        ..
    } = e
    {
        conjuncts(e1, out);
        conjuncts(e2, out);
    } else {
        out.push(e);
    }
}

/// Prove that two premise expressions are the same under `map`, extending
/// the map with variables exposed only by that shared premise.
fn shared_expression(
    sibling: &SpecTecExp,
    ours: &SpecTecExp,
    map: &BTreeMap<String, SpecTecExp>,
) -> Option<BTreeMap<String, SpecTecExp>> {
    if subst_vars(sibling, map).as_ref().ok() == Some(ours) {
        return Some(map.clone());
    }

    // SpecTec uses the same metavariable spelling across sibling clauses.
    // Syntactic identity is useful evidence, but only after adding identity
    // bindings for its free variables and rechecking by substitution.
    if sibling == ours {
        let mut candidate = map.clone();
        let mut vars = Vec::new();
        free_vars(sibling, &mut vars);
        for id in vars {
            candidate
                .entry(id.clone())
                .or_insert(SpecTecExp::Var { id });
        }
        if subst_vars(sibling, &candidate).as_ref().ok() == Some(ours) {
            return Some(candidate);
        }
    }

    let mut candidate = map.clone();
    matches!(unify(sibling, ours, &mut candidate), U::Ok).then_some(candidate)
}

/// `¬(c₁ ∧ … ∧ cₘ)` as a SpecTec expression: `¬c₁ ∨ … ∨ ¬cₘ` (`m = 0` ⇒
/// `false` — an unconditional sibling always applies).
fn negate_conj(conds: &[SpecTecExp]) -> Result<SpecTecExp, String> {
    let mut negs = conds.iter().map(negate).collect::<Result<Vec<_>, _>>()?;
    let Some(mut acc) = negs.pop() else {
        return Ok(SpecTecExp::Bool { b: false });
    };
    while let Some(n) = negs.pop() {
        acc = SpecTecExp::Bin {
            op: SpecTecBinOp::Or,
            t: bool_ty(),
            e1: Box::new(n),
            e2: Box::new(acc),
        };
    }
    Ok(acc)
}

/// Negate a boolean SpecTec expression, pushing the negation to the leaves:
/// De Morgan on `∧`/`∨`/`⟹`, comparison flipping (`Eq ↔ Ne`, `Lt ↔ Ge`,
/// `Le ↔ Gt`), double-negation elimination; a bool-valued `Call` (or any other
/// atom the flattener can evaluate to a boolean) stays under `Un Not`.
pub fn negate(e: &SpecTecExp) -> Result<SpecTecExp, String> {
    use SpecTecExp as E;
    match e {
        E::Bool { b } => Ok(E::Bool { b: !b }),
        E::Un {
            op: SpecTecUnOp::Not,
            e2,
            ..
        } => Ok((**e2).clone()),
        E::Bin { op, t, e1, e2 } => match op {
            SpecTecBinOp::And => Ok(E::Bin {
                op: SpecTecBinOp::Or,
                t: t.clone(),
                e1: Box::new(negate(e1)?),
                e2: Box::new(negate(e2)?),
            }),
            SpecTecBinOp::Or => Ok(E::Bin {
                op: SpecTecBinOp::And,
                t: t.clone(),
                e1: Box::new(negate(e1)?),
                e2: Box::new(negate(e2)?),
            }),
            SpecTecBinOp::Impl => Ok(E::Bin {
                op: SpecTecBinOp::And,
                t: t.clone(),
                e1: e1.clone(),
                e2: Box::new(negate(e2)?),
            }),
            _ => Err("negate-bin".into()),
        },
        E::Cmp { op, t, e1, e2 } => {
            use SpecTecCmpOp as C;
            let flipped = match op {
                C::Eq => C::Ne,
                C::Ne => C::Eq,
                C::Lt => C::Ge,
                C::Ge => C::Lt,
                C::Le => C::Gt,
                C::Gt => C::Le,
            };
            Ok(E::Cmp {
                op: flipped,
                t: t.clone(),
                e1: e1.clone(),
                e2: e2.clone(),
            })
        }
        // A bool-valued call: keep `¬call` — the flattener grounds it through
        // the graph relation with result `false`.
        E::Call { .. } => Ok(E::Un {
            op: SpecTecUnOp::Not,
            t: bool_ty(),
            e2: Box::new(e.clone()),
        }),
        _ => Err("negate-atom".into()),
    }
}

/// Every variable id occurring in an expression, by **full** traversal
/// (including iteration domains and update paths — unlike
/// `encode::collect_metavars`, which follows only encoding-relevant
/// positions). Used for the binder-capture refusal below, where a missed
/// occurrence would substitute wrongly.
fn free_vars(e: &SpecTecExp, out: &mut Vec<String>) {
    use SpecTecExp as E;
    if let E::Var { id } = e {
        if !out.iter().any(|s| s == id) {
            out.push(id.clone());
        }
        return;
    }
    match e {
        E::Iter { e1, it, xes } => {
            free_vars(e1, out);
            if let covalence_spectec::ast::SpecTecIter::ListN { e, .. } = it {
                e.iter().for_each(|b| free_vars(b, out));
            }
            for SpecTecIterExp::Dom { e, .. } in xes {
                free_vars(e, out);
            }
        }
        E::Upd { e1, path, e2 } | E::Ext { e1, path, e2 } => {
            free_vars(e1, out);
            free_vars(e2, out);
            path_free_vars(path, out);
        }
        _ => {
            let mut kids = Vec::new();
            children(e, &mut kids);
            for k in kids {
                free_vars(k, out);
            }
        }
    }
}

fn path_free_vars(p: &SpecTecPath, out: &mut Vec<String>) {
    match p {
        SpecTecPath::Root => {}
        SpecTecPath::Idx { p1, e } => {
            path_free_vars(p1, out);
            free_vars(e, out);
        }
        SpecTecPath::Slice { p1, e1, e2 } => {
            path_free_vars(p1, out);
            free_vars(e1, out);
            free_vars(e2, out);
        }
        SpecTecPath::Dot { p1, .. } => path_free_vars(p1, out),
    }
}

/// The direct child expressions of a node (all of them — full traversal).
fn children<'e>(e: &'e SpecTecExp, out: &mut Vec<&'e SpecTecExp>) {
    use SpecTecExp as E;
    match e {
        E::Var { .. } | E::Bool { .. } | E::Num { .. } | E::Text { .. } => {}
        E::Un { e2, .. } => out.push(e2),
        E::Bin { e1, e2, .. }
        | E::Cmp { e1, e2, .. }
        | E::Idx { e1, e2 }
        | E::Comp { e1, e2 }
        | E::Mem { e1, e2 }
        | E::Cat { e1, e2 } => {
            out.push(e1);
            out.push(e2);
        }
        E::Slice { e1, e2, e3 } => {
            out.push(e1);
            out.push(e2);
            out.push(e3);
        }
        E::Str { efs } => {
            for SpecTecExpField::Field { e, .. } in efs {
                out.push(e);
            }
        }
        E::Dot { e1, .. }
        | E::Len { e1 }
        | E::Proj { e1, .. }
        | E::Case { e1, .. }
        | E::Uncase { e1, .. }
        | E::Unopt { e1 }
        | E::Lift { e1 }
        | E::Cvt { e1, .. }
        | E::Sub { e1, .. } => out.push(e1),
        E::Opt { eo } => {
            if let Some(e1) = eo {
                out.push(e1);
            }
        }
        E::Tup { es } | E::List { es } => out.extend(es.iter()),
        E::Call { as1, .. } => {
            for a in as1 {
                if let covalence_spectec::ast::SpecTecArg::Exp { e } = a {
                    out.push(e);
                }
            }
        }
        // Handled by `free_vars` directly (binders / paths), but keep the
        // body child so a generic walk stays total.
        E::Iter { e1, .. } | E::Upd { e1, .. } | E::Ext { e1, .. } => out.push(e1),
    }
}

/// Capture-checked substitution of the correspondence map through a sibling
/// condition. Iteration binders (`xes` domains) shadow — a colliding binder
/// refuses rather than substituting wrongly, and so does a binder that any
/// map **value**'s free variables intersect (substituting under it would
/// capture). `pub(super)`: also the `Dec` clause-order confluence check.
pub(super) fn subst_vars(
    e: &SpecTecExp,
    map: &BTreeMap<String, SpecTecExp>,
) -> Result<SpecTecExp, String> {
    use SpecTecExp as E;
    let go = |e: &SpecTecExp| subst_vars(e, map);
    let gob = |e: &SpecTecExp| go(e).map(Box::new);
    Ok(match e {
        E::Var { id } => match map.get(id) {
            Some(t) => t.clone(),
            None => return Err("unmapped-condition-var".into()),
        },
        E::Bool { .. } | E::Num { .. } | E::Text { .. } => e.clone(),
        E::Un { op, t, e2 } => E::Un {
            op: op.clone(),
            t: t.clone(),
            e2: gob(e2)?,
        },
        E::Bin { op, t, e1, e2 } => E::Bin {
            op: op.clone(),
            t: t.clone(),
            e1: gob(e1)?,
            e2: gob(e2)?,
        },
        E::Cmp { op, t, e1, e2 } => E::Cmp {
            op: op.clone(),
            t: t.clone(),
            e1: gob(e1)?,
            e2: gob(e2)?,
        },
        E::Idx { e1, e2 } => E::Idx {
            e1: gob(e1)?,
            e2: gob(e2)?,
        },
        E::Slice { e1, e2, e3 } => E::Slice {
            e1: gob(e1)?,
            e2: gob(e2)?,
            e3: gob(e3)?,
        },
        E::Upd { e1, path, e2 } => E::Upd {
            e1: gob(e1)?,
            path: Box::new(subst_path(path, map)?),
            e2: gob(e2)?,
        },
        E::Ext { e1, path, e2 } => E::Ext {
            e1: gob(e1)?,
            path: Box::new(subst_path(path, map)?),
            e2: gob(e2)?,
        },
        E::Str { efs } => E::Str {
            efs: efs
                .iter()
                .map(|SpecTecExpField::Field { at, e }| {
                    Ok(SpecTecExpField::Field {
                        at: at.clone(),
                        e: go(e)?,
                    })
                })
                .collect::<Result<_, String>>()?,
        },
        E::Dot { e1, at } => E::Dot {
            e1: gob(e1)?,
            at: at.clone(),
        },
        E::Comp { e1, e2 } => E::Comp {
            e1: gob(e1)?,
            e2: gob(e2)?,
        },
        E::Mem { e1, e2 } => E::Mem {
            e1: gob(e1)?,
            e2: gob(e2)?,
        },
        E::Len { e1 } => E::Len { e1: gob(e1)? },
        E::Tup { es } => E::Tup {
            es: es.iter().map(go).collect::<Result<_, _>>()?,
        },
        E::Call { x, as1 } => E::Call {
            x: x.clone(),
            as1: as1
                .iter()
                .map(|a| match a {
                    covalence_spectec::ast::SpecTecArg::Exp { e } => {
                        Ok(covalence_spectec::ast::SpecTecArg::Exp { e: go(e)? })
                    }
                    other => Ok(other.clone()),
                })
                .collect::<Result<_, String>>()?,
        },
        E::Iter { e1, it, xes } => {
            // Iteration binders shadow: refuse if a binder collides with a
            // mapped variable it would have to rename, or if any map value's
            // free variables intersect the binder set (substituting under
            // the binder would capture them).
            for SpecTecIterExp::Dom { x, .. } in xes {
                if let Some(t) = map.get(x)
                    && *t != (E::Var { id: x.clone() })
                {
                    return Err("iter-binder-collision".into());
                }
                for (k, v) in map.iter() {
                    if k == x {
                        continue; // the binder's own (identity) mapping
                    }
                    let mut fv = Vec::new();
                    free_vars(v, &mut fv);
                    if fv.iter().any(|f| f == x) {
                        return Err("iter-binder-capture".into());
                    }
                }
            }
            E::Iter {
                e1: gob(e1)?,
                it: it.clone(),
                xes: xes
                    .iter()
                    .map(|SpecTecIterExp::Dom { x, e }| {
                        Ok(SpecTecIterExp::Dom {
                            x: x.clone(),
                            e: go(e)?,
                        })
                    })
                    .collect::<Result<_, String>>()?,
            }
        }
        E::Proj { e1, i } => E::Proj {
            e1: gob(e1)?,
            i: *i,
        },
        E::Case { op, e1 } => E::Case {
            op: op.clone(),
            e1: gob(e1)?,
        },
        E::Uncase { e1, op } => E::Uncase {
            e1: gob(e1)?,
            op: op.clone(),
        },
        E::Opt { eo } => E::Opt {
            eo: match eo {
                Some(inner) => Some(gob(inner)?),
                None => None,
            },
        },
        E::Unopt { e1 } => E::Unopt { e1: gob(e1)? },
        E::List { es } => E::List {
            es: es.iter().map(go).collect::<Result<_, _>>()?,
        },
        E::Lift { e1 } => E::Lift { e1: gob(e1)? },
        E::Cat { e1, e2 } => E::Cat {
            e1: gob(e1)?,
            e2: gob(e2)?,
        },
        E::Cvt { nt1, nt2, e1 } => E::Cvt {
            nt1: nt1.clone(),
            nt2: nt2.clone(),
            e1: gob(e1)?,
        },
        E::Sub { t1, t2, e1 } => E::Sub {
            t1: t1.clone(),
            t2: t2.clone(),
            e1: gob(e1)?,
        },
    })
}

fn subst_path(p: &SpecTecPath, map: &BTreeMap<String, SpecTecExp>) -> Result<SpecTecPath, String> {
    Ok(match p {
        SpecTecPath::Root => SpecTecPath::Root,
        SpecTecPath::Idx { p1, e } => SpecTecPath::Idx {
            p1: Box::new(subst_path(p1, map)?),
            e: subst_vars(e, map)?,
        },
        SpecTecPath::Slice { p1, e1, e2 } => SpecTecPath::Slice {
            p1: Box::new(subst_path(p1, map)?),
            e1: subst_vars(e1, map)?,
            e2: subst_vars(e2, map)?,
        },
        SpecTecPath::Dot { p1, at } => SpecTecPath::Dot {
            p1: Box::new(subst_path(p1, map)?),
            at: at.clone(),
        },
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_spectec::ast::{MixOp, SpecTecIter, SpecTecNum};
    use covalence_spectec::wasm::get_wasm_spectec_ast;

    fn var(id: &str) -> SpecTecExp {
        SpecTecExp::Var { id: id.into() }
    }
    fn case(name: &str, payload: SpecTecExp) -> SpecTecExp {
        SpecTecExp::Case {
            op: MixOp::new(vec![name.to_string()]),
            e1: Box::new(payload),
        }
    }
    fn list(es: Vec<SpecTecExp>) -> SpecTecExp {
        SpecTecExp::List { es }
    }
    fn unit() -> SpecTecExp {
        SpecTecExp::Tup { es: vec![] }
    }

    /// R2 binder-capture gap: a map VALUE whose free vars intersect the
    /// iteration binder set must refuse (substituting under the binder
    /// would capture), even when the binder itself is not a map key.
    #[test]
    fn subst_vars_refuses_value_capture_under_iter_binder() {
        // Sibling condition: (x = ch)* with ch ← chs   (binder `ch`).
        let cond = SpecTecExp::Iter {
            e1: Box::new(SpecTecExp::Cmp {
                op: SpecTecCmpOp::Eq,
                t: SpecTecOpTyp::Bool(SpecTecBoolTyp::Bool),
                e1: Box::new(var("x")),
                e2: Box::new(var("ch")),
            }),
            it: SpecTecIter::List,
            xes: vec![SpecTecIterExp::Dom {
                x: "ch".into(),
                e: var("chs"),
            }],
        };
        // Map: x ↦ F(ch) — the value's free var `ch` collides with the
        // binder; ch/chs map identically (the allowed binder mapping).
        let mut map = BTreeMap::new();
        map.insert("x".to_string(), case("F", var("ch")));
        map.insert("ch".to_string(), var("ch"));
        map.insert("chs".to_string(), var("chs"));
        assert_eq!(
            subst_vars(&cond, &map),
            Err("iter-binder-capture".to_string())
        );
        // A capture-free value substitutes fine.
        map.insert("x".to_string(), case("F", var("y")));
        assert!(subst_vars(&cond, &map).is_ok());
    }

    /// The (List, Cat) unification arm: a rigid k-element list clashes with
    /// a concatenation guaranteeing more than k elements, and stays
    /// indeterminate otherwise.
    #[test]
    fn unify_list_vs_cat_length_clash() {
        let cat2 = SpecTecExp::Cat {
            e1: Box::new(list(vec![case("A", unit())])),
            e2: Box::new(SpecTecExp::Cat {
                e1: Box::new(list(vec![case("B", unit())])),
                e2: Box::new(var("rest")),
            }),
        };
        // 1-element list vs ≥2-element cat: provably disjoint.
        let mut m = BTreeMap::new();
        assert!(matches!(
            unify(&cat2, &list(vec![case("A", unit())]), &mut m),
            U::Clash
        ));
        // 2-element list vs ≥2-element cat: indeterminate (trailing var).
        let mut m = BTreeMap::new();
        assert!(matches!(
            unify(
                &cat2,
                &list(vec![case("A", unit()), case("B", unit())]),
                &mut m
            ),
            U::Unknown
        ));
    }

    /// A Cat pattern with a required rigid token is disjoint from an exact
    /// list that contains no placement for that token, even when arbitrary
    /// list segments surround it. This is the shape that separates
    /// `return_call_ref-handler` from `throw_ref-handler-next`.
    #[test]
    fn unify_exact_list_vs_cat_required_token_clash() {
        let return_call_body = SpecTecExp::Cat {
            e1: Box::new(var("vals")),
            e2: Box::new(SpecTecExp::Cat {
                e1: Box::new(list(vec![case("RETURN_CALL_REF", var("yy"))])),
                e2: Box::new(var("instrs")),
            }),
        };
        let throw_body = list(vec![
            case("REF.EXN_ADDR", var("a")),
            case("THROW_REF", unit()),
        ]);

        let mut m = BTreeMap::new();
        assert!(matches!(
            unify(&return_call_body, &throw_body, &mut m),
            U::Clash
        ));
        // Disjointness is structural and therefore also detected when the
        // exact list occurs on the sibling side of the directional matcher.
        let mut m = BTreeMap::new();
        assert!(matches!(
            unify(&throw_body, &return_call_body, &mut m),
            U::Clash
        ));

        // A genuine placement must remain conservative: the leading and
        // trailing flexible segments may consume the surrounding elements.
        let with_return_call = list(vec![
            case("REF.FUNC_ADDR", var("a")),
            case("RETURN_CALL_REF", var("t")),
            case("NOP", unit()),
        ]);
        let mut m = BTreeMap::new();
        assert!(matches!(
            unify(&return_call_body, &with_return_call, &mut m),
            U::Unknown
        ));
    }

    /// Corpus regression for the exact false-sibling attribution: the actual
    /// elaborated return-call handler redex is rigidly disjoint from the
    /// throw-handler fallback redex.
    #[test]
    fn real_return_call_handler_is_disjoint_from_throw_handler_next() {
        fn find<'a>(
            defs: &'a [covalence_spectec::ast::SpecTecDef],
            name: &str,
        ) -> Option<&'a SpecTecRule> {
            use covalence_spectec::ast::SpecTecDef;
            for def in defs {
                match def {
                    SpecTecDef::Rel { rules, .. } => {
                        if let Some(rule) = rules.iter().find(|rule| {
                            let SpecTecRule::Rule { x, .. } = rule;
                            x == name
                        }) {
                            return Some(rule);
                        }
                    }
                    SpecTecDef::Rec { ds } => {
                        if let Some(rule) = find(ds, name) {
                            return Some(rule);
                        }
                    }
                    _ => {}
                }
            }
            None
        }

        let defs = get_wasm_spectec_ast();
        let return_call = find(&defs, "return_call_ref-handler").expect("return-call handler");
        let handler_next = find(&defs, "throw_ref-handler-next").expect("handler-next");
        let SpecTecRule::Rule { e: return_e, .. } = return_call;
        let SpecTecRule::Rule { e: next_e, .. } = handler_next;
        assert!(matches!(
            correspond(redex(return_e), redex(next_e)),
            Corr::Disjoint
        ));
    }

    /// The catalogue-aware finite complement rewrites the real handler
    /// fallback into one DNF guard: the two conditional catch constructors
    /// survive with tag-mismatch guards; the two unconditional catch-all
    /// constructors contribute no branch.
    #[test]
    fn real_throw_handler_next_has_exact_finite_complement() {
        use covalence_spectec::ast::SpecTecDef;

        fn step_read(defs: &[SpecTecDef]) -> Option<&[SpecTecRule]> {
            for def in defs {
                match def {
                    SpecTecDef::Rel { x, rules, .. } if x == "Step_read" => {
                        return Some(rules);
                    }
                    SpecTecDef::Rec { ds } => {
                        if let Some(rules) = step_read(ds) {
                            return Some(rules);
                        }
                    }
                    _ => {}
                }
            }
            None
        }

        let defs = get_wasm_spectec_ast();
        let rules = step_read(&defs).expect("Step_read");
        let cat = CaseCatalogue::new(&defs);
        let pre = preprocess_else_with_catalogue(rules, &cat);
        let next = pre
            .iter()
            .find(|p| {
                let SpecTecRule::Rule { x, .. } = &p.rule;
                x == "throw_ref-handler-next"
            })
            .expect("handler-next");
        assert_eq!(next.status, ElseStatus::Rewritten { negated: 4 });
        let SpecTecRule::Rule { prs, .. } = &next.rule;
        let [
            SpecTecPrem::If {
                e:
                    SpecTecExp::Bin {
                        op: SpecTecBinOp::Or,
                        e1,
                        e2,
                        ..
                    },
            },
        ] = prs.as_slice()
        else {
            panic!("expected one DNF guard, got {prs:#?}");
        };

        let branch_key = |e: &SpecTecExp| {
            let SpecTecExp::Bin {
                op: SpecTecBinOp::And,
                e1,
                e2,
                ..
            } = e
            else {
                panic!("branch is not a conjunction: {e:#?}");
            };
            let SpecTecExp::Cmp {
                op: SpecTecCmpOp::Eq,
                e2: constructor,
                ..
            } = &**e1
            else {
                panic!("branch lacks constructor equality: {e1:#?}");
            };
            let SpecTecExp::Case { op, .. } = &**constructor else {
                panic!("constructor equality RHS: {constructor:#?}");
            };
            assert!(
                matches!(
                    &**e2,
                    SpecTecExp::Cmp {
                        op: SpecTecCmpOp::Ne,
                        ..
                    }
                ),
                "branch must negate the tag match: {e2:#?}"
            );
            crate::wasm::encode::mixop_key(op)
        };
        let keys = [branch_key(e1), branch_key(e2)];
        assert_eq!(keys, ["CATCH", "CATCH_REF"]);

        // Without an exhaustive constructor catalogue the optimization must
        // fail closed and retain the opaque Else.
        let uncatalogued = preprocess_else_with_catalogue(rules, &CaseCatalogue::default());
        let next = uncatalogued
            .iter()
            .find(|p| {
                let SpecTecRule::Rule { x, .. } = &p.rule;
                x == "throw_ref-handler-next"
            })
            .unwrap();
        assert_eq!(
            next.status,
            ElseStatus::Failed("sibling-undecided:throw_ref-handler-catch".into())
        );
    }

    /// A single unmatched relation judgement has an exact negative
    /// applicability meaning, but cannot be negated inside the positive
    /// source relation.  Preserve that meaning as an internal decision
    /// request; the HOL lowering then keeps it opaque until a certified
    /// decision family is installed.
    #[test]
    fn single_rule_applicability_routes_to_negative_decision() {
        use covalence_spectec::ast::SpecTecDef;

        fn find(defs: &[SpecTecDef], name: &str) -> Option<SpecTecRule> {
            for def in defs {
                match def {
                    SpecTecDef::Rel { rules, .. } => {
                        if let Some(rule) = rules.iter().find(|rule| {
                            let SpecTecRule::Rule { x, .. } = rule;
                            x == name
                        }) {
                            return Some(rule.clone());
                        }
                    }
                    SpecTecDef::Rec { ds } => {
                        if let Some(rule) = find(ds, name) {
                            return Some(rule);
                        }
                    }
                    _ => {}
                }
            }
            None
        }

        let defs = get_wasm_spectec_ast();
        let mut succeed = find(&defs, "ref.test-true").expect("ref.test success");
        let fail = find(&defs, "ref.test-false").expect("ref.test fallback");
        let SpecTecRule::Rule { prs, .. } = &mut succeed;
        prs.retain(|prem| {
            matches!(
                prem,
                SpecTecPrem::Rule { x, .. } if x == "Ref_ok"
            )
        });
        assert_eq!(prs.len(), 1, "fixture has one Ref_ok applicability premise");

        let pre = preprocess_else(&[succeed, fail]);
        assert_eq!(pre[1].status, ElseStatus::Rewritten { negated: 1 });
        let SpecTecRule::Rule { prs, .. } = &pre[1].rule;
        assert!(matches!(
            prs.as_slice(),
            [SpecTecPrem::Rule { x, .. }]
                if x == &format!("{NEGATED_RULE_PREFIX}Ref_ok")
        ));
    }

    /// Pin the exact proof obligations behind every remaining rule-level
    /// `Else` refusal in the bundled corpus.  Four reference-instruction
    /// fallbacks need the complement of a *conjunction* of two relation
    /// judgements (`Ref_ok` and `Reftype_sub`).  The array-data zero case
    /// needs both the arithmetic complement of `oob1` and the complement of
    /// `Expand ∧ oob2-condition`.  Neither shape is a single negative
    /// relation request, so rewriting either as one would be an
    /// over-approximation; they belong at the certified composite-decision
    /// boundary.
    #[test]
    fn remaining_real_else_sites_are_exact_composite_decision_obligations() {
        use covalence_spectec::ast::SpecTecDef;

        fn step_read(defs: &[SpecTecDef]) -> Option<&[SpecTecRule]> {
            for def in defs {
                match def {
                    SpecTecDef::Rel { x, rules, .. } if x == "Step_read" => {
                        return Some(rules);
                    }
                    SpecTecDef::Rec { ds } => {
                        if let Some(rules) = step_read(ds) {
                            return Some(rules);
                        }
                    }
                    _ => {}
                }
            }
            None
        }

        let defs = get_wasm_spectec_ast();
        let rules = step_read(&defs).expect("bundled Step_read");
        let pre = preprocess_else_with_catalogue(rules, &CaseCatalogue::new(&defs));
        let status = |name: &str| {
            pre.iter()
                .find_map(|p| {
                    let SpecTecRule::Rule { x, .. } = &p.rule;
                    (x == name).then_some(p.status.clone())
                })
                .unwrap_or_else(|| panic!("missing Step_read/{name}"))
        };

        for (fallback, success) in [
            ("br_on_cast-fail", "br_on_cast-succeed"),
            ("br_on_cast_fail-fail", "br_on_cast_fail-succeed"),
            ("ref.test-false", "ref.test-true"),
            ("ref.cast-fail", "ref.cast-succeed"),
        ] {
            assert_eq!(
                status(fallback),
                ElseStatus::Failed(format!(
                    "sibling-rule-premise:{success}:multiple:Ref_ok/0,Reftype_sub/0:conds0"
                ))
            );
            let SpecTecRule::Rule { prs, .. } = rules
                .iter()
                .find(|r| matches!(r, SpecTecRule::Rule { x, .. } if x == success))
                .expect("success sibling");
            let relation_names: Vec<_> = prs
                .iter()
                .filter_map(|p| match p {
                    SpecTecPrem::Rule { x, .. } => Some(x.as_str()),
                    _ => None,
                })
                .collect();
            assert_eq!(relation_names, ["Ref_ok", "Reftype_sub"]);
            assert!(
                prs.iter().all(|p| matches!(p, SpecTecPrem::Rule { .. })),
                "{success} applicability is exactly the two judgements"
            );
        }

        assert_eq!(
            status("array.init_data-zero"),
            ElseStatus::Failed("sibling-rule-premise:Expand:args0:conds1".into())
        );
        let prior = |name: &str| {
            rules
                .iter()
                .find(|r| matches!(r, SpecTecRule::Rule { x, .. } if x == name))
                .unwrap_or_else(|| panic!("missing Step_read/{name}"))
        };
        let SpecTecRule::Rule { prs: oob1, .. } = prior("array.init_data-oob1");
        assert_eq!(
            (
                oob1.iter()
                    .filter(|p| matches!(p, SpecTecPrem::Rule { .. }))
                    .count(),
                oob1.iter()
                    .filter(|p| matches!(p, SpecTecPrem::If { .. }))
                    .count(),
            ),
            (0, 1),
            "oob1 applicability is its arithmetic guard"
        );
        let SpecTecRule::Rule { prs: oob2, .. } = prior("array.init_data-oob2");
        assert_eq!(
            (
                oob2.iter()
                    .filter(|p| matches!(p, SpecTecPrem::Rule { x, .. } if x == "Expand"))
                    .count(),
                oob2.iter()
                    .filter(|p| matches!(p, SpecTecPrem::If { .. }))
                    .count(),
            ),
            (1, 1),
            "oob2 applicability is exactly Expand and its arithmetic guard"
        );
    }

    /// Cross-kind numeric literals are never a rigid clash (`Nat 2` and
    /// `Int 2` can denote the same value); same-kind unequal values are.
    #[test]
    fn unify_num_kind_guard() {
        let nat = |n: u64| SpecTecExp::Num {
            n: SpecTecNum::Nat(n),
        };
        let int = |n: i64| SpecTecExp::Num {
            n: SpecTecNum::Int(n),
        };
        let mut m = BTreeMap::new();
        assert!(matches!(unify(&nat(2), &nat(3), &mut m), U::Clash));
        assert!(matches!(unify(&nat(2), &nat(2), &mut m), U::Ok));
        assert!(matches!(unify(&nat(2), &int(2), &mut m), U::Unknown));
        assert!(matches!(
            unify(
                &SpecTecExp::Num {
                    n: SpecTecNum::Rat("2/1".into())
                },
                &SpecTecExp::Num {
                    n: SpecTecNum::Rat("4/2".into())
                },
                &mut m
            ),
            U::Unknown
        ));
    }
}
