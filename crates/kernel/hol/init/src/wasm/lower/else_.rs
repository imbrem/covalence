//! **`Else` (`-- otherwise`) preprocessing** — rewrite each `SpecTecPrem::Else`
//! into ordinary `If` premises: the conjunction of **negations** of each
//! textually-earlier *sibling* rule's own `If` conditions (design note leg 5,
//! `notes/vibes/logics/spectec-total-load.md`).
//!
//! ## Semantics
//!
//! `-- otherwise` means "no textually-preceding rule of the same conclusion
//! group applies". Writing `A_j` for rule `j`'s own `If`-conjunction, rule
//! `j`'s *effective* guard is `otherwise_j ∧ A_j`, and an easy induction shows
//! `⋀_{j<k} ¬(effective_j) = ⋀_{j<k} ¬A_j` — so it suffices to negate each
//! earlier sibling's **own** `If` premises, ignoring their `Else` markers.
//! Each sibling contributes one `If` premise `¬A_j` (`¬(c₁ ∧ … ∧ cₘ)` pushed to
//! `¬c₁ ∨ … ∨ ¬cₘ`; a condition-free sibling contributes `false` — it always
//! applies, so the `otherwise` rule can never fire).
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
    SpecTecOpTyp, SpecTecPath, SpecTecPrem, SpecTecRule, SpecTecUnOp,
};

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
            match rewrite_else(rule, &rules[..k]) {
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

/// Rewrite the `Else` premise of `rule` against the textually-earlier `prior`
/// rules. Returns the rewritten rule and the number of negated-guard premises.
fn rewrite_else(rule: &SpecTecRule, prior: &[SpecTecRule]) -> Result<(SpecTecRule, usize), String> {
    let SpecTecRule::Rule { x, ps, op, e, prs } = rule;
    let our_lhs = redex(e);

    // Collect one negated-guard condition per sibling.
    let our_tag = instr_tag(our_lhs);
    let mut negations = Vec::new();
    for p in prior {
        let SpecTecRule::Rule {
            e: pe, prs: pprs, ..
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
        let map = match correspond(redex(pe), our_lhs) {
            Corr::Disjoint => continue, // provably never overlaps: not a sibling
            Corr::Overlap(map) => map,
            Corr::Unknown => {
                let SpecTecRule::Rule { x: px, .. } = p;
                return Err(format!("sibling-undecided:{px}"));
            }
        };
        // A sibling's applicability must be a pure condition: `If`s only
        // (its own `Else` markers are ignored — see the module docs algebra).
        let mut conds = Vec::new();
        for pp in pprs {
            match pp {
                SpecTecPrem::If { e } => conds.push(subst_vars(e, &map)?),
                SpecTecPrem::Else => {}
                SpecTecPrem::Rule { .. } => return Err("sibling-rule-premise".into()),
                SpecTecPrem::Iter { .. } => return Err("sibling-iter-premise".into()),
                SpecTecPrem::Let { .. } => return Err("sibling-let-premise".into()),
            }
        }
        negations.push(negate_conj(&conds)?);
    }

    // Splice the negations in place of the `Else` premise(s).
    let mut new_prs = Vec::with_capacity(prs.len() + negations.len());
    for p in prs {
        if matches!(p, SpecTecPrem::Else) {
            new_prs.extend(negations.iter().cloned().map(|e| SpecTecPrem::If { e }));
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
/// the wrapper's key, so e.g. every `HANDLER_`-wrapped rule shares one tag —
/// `Step_read/throw_ref-handler-next`'s refusal blames the same-tagged
/// `return_call_ref-handler` rather than its genuine `throw_ref-handler-*`
/// siblings. Refining the tag by diving into the wrapper payload's
/// instruction list is **unsound as a group discriminator**: a payload list
/// ending in a *variable* segment (`… ++ [BR l] ++ instr*`, the
/// `br-handler` shape) has no reliable last-literal, so two genuine group
/// members could tag differently and a sibling's negated guard would be
/// silently dropped — an over-approximation. And it would not unlock
/// `handler-next` anyway: its genuine catch siblings overlap `Cat`-vs-`Cat`
/// (`[CATCH x l] ++ catch'*` vs `[catch] ++ catch'*`), whose complement is a
/// pattern disequality [`unify`] correctly refuses. Coarse tags only ever
/// *add* sibling candidates, which is the conservative direction.
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
        // An exact-length literal list vs a concatenation with a longer
        // guaranteed (literal-segment) length cannot match the same value.
        (E::List { es }, cat @ E::Cat { .. }) | (cat @ E::Cat { .. }, E::List { es }) => {
            if min_cat_len(cat) > es.len() {
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
