//! **Sort guards for `Sub`-stripped metavariables** — the Wave-D soundness
//! fix for the sortless-metavariable over-approximation.
//!
//! ## The problem
//!
//! Clause metavariables are untyped `Φ = nat` leaves and [`super::super::encode::canon`]
//! strips `Sub` casts, so a metavariable whose **every** occurrence in its
//! rule/clause is `Sub`-wrapped (a *sub-only* variable — e.g. the `Inn` in
//! `$default_(Inn) = (CONST Inn 0)`, or the `at : addrtype` used at `numtype`
//! positions throughout the `Step_read` memory rules) loses its sort
//! constraint entirely: the lowered clause is `∀`-open at that variable and
//! derives **false facts at well-sorted points** (`fn.default_(F32, CONST F32
//! 0)`). A variable with at least one *bare* (exact-sort) occurrence is
//! harmless: an ill-sorted instantiation makes that position — hence the whole
//! conclusion or a premise judgement — the encoding of no well-sorted SpecTec
//! instance, which is outside the faithfulness contract (see
//! `encode.rs` § *Faithfulness, not soundness* and the argument in
//! [`super`]'s module docs).
//!
//! ## The two fixes (chosen per site — policy in [`super::decs`]' docs)
//!
//! - **Per-case expansion** ([`expansions`]): when the lost sort's cases are
//!   catalogue-enumerable and **all nullary** (`Inn = {I32, I64}`,
//!   `Fnn = {F32, F64}`, `addrtype = {I32, I64}`, …), substitute each concrete
//!   case for the variable and emit one clause per case — exact, premise-free.
//!   Used by the `Dec` leg (clause multiplicity is already variable there).
//! - **Sort-guard premises** ([`guard_judgement`] + [`sort_clauses`]): an
//!   `ev.sort.<ty>` membership relation, one clause per catalogue case of
//!   `<ty>` — **exact** for nullary cases (payload pinned to the unit `tup`),
//!   **head-level** for payload-carrying cases (payload `∀`-open: an ill-sorted
//!   payload makes the guarded position junk, which is outside the contract).
//!   Emitted on demand like `ev.neq`. Used by the rule leg (preserves the
//!   one-clause-per-rule order contract) and for non-nullary sorts in the
//!   `Dec` leg (`valtype`, `import`).
//!
//! Both fixes only ever *strengthen* antecedents / *specialize* conclusions,
//! so the soundness frame (never weaken) is preserved by construction.

use std::collections::{BTreeMap, BTreeSet};

use covalence_core::{Result, Term};
use covalence_spectec::ast::{
    MixOp, SpecTecArg, SpecTecClause, SpecTecExp, SpecTecExpField, SpecTecIterExp, SpecTecPrem,
    SpecTecTyp,
};

use super::super::encode::metavar;
use super::super::syntax::CaseCatalogue;
use super::Clause;
use super::evalrel::ev_graph;

// ===========================================================================
// Occurrence analysis: sub-only variables and their lost sorts
// ===========================================================================

/// The head name of a subtype annotation (`Sub.t1`) — sort guards only apply
/// to *named* sorts (the catalogue key space). Compound types return `None`
/// (no `Sub`-typed variable in the corpus has one).
fn typ_name(t: &SpecTecTyp) -> Option<&str> {
    match t {
        SpecTecTyp::Var { x, .. } => Some(x),
        _ => None,
    }
}

#[derive(Debug, Default, Clone)]
struct Occ {
    subbed: usize,
    /// Bare occurrences at **pinning** positions: positions that survive
    /// verbatim into the encoded *conclusion* (rule conclusion / `Dec`
    /// pattern spine) — outside `Call` arguments (lifted into `fn.*`
    /// premises), outside identity-collapsed iteration bodies (replaced by
    /// the domain) and non-identity iteration domains (dropped from the
    /// encoding), and outside `Dec` RHSs (whose structural operators the
    /// result flattening moves into `ev.*` premises). An ill-sorted value at
    /// a pinning position makes the conclusion the encoding of no well-sorted
    /// SpecTec instance — outside the faithfulness contract — so one pinning
    /// bare occurrence makes the variable harmless. Bare occurrences in
    /// *premises* do NOT rescue: premise relations can be sort-coarse
    /// (`ev.neq` is head-level, evaluator relations are sort-generic), so a
    /// premise can be derivable at an ill-sorted instantiation.
    bare_pinning: usize,
    /// `Sub.t1` head names seen (misses compound `t1`s — counted in `subbed`
    /// but contributing no guardable sort, reported unguardable; 0 such in
    /// the corpus).
    sorts: BTreeSet<String>,
}

fn walk(e: &SpecTecExp, sub: Option<&SpecTecTyp>, pinning: bool, out: &mut BTreeMap<String, Occ>) {
    use SpecTecExp as E;
    use covalence_spectec::ast::SpecTecIter;
    match e {
        E::Var { id } => {
            let o = out.entry(id.clone()).or_default();
            match sub {
                Some(t1) => {
                    o.subbed += 1;
                    if let Some(n) = typ_name(t1) {
                        o.sorts.insert(n.to_owned());
                    }
                }
                None if pinning => o.bare_pinning += 1,
                None => {}
            }
        }
        // Nested `Sub`s: the innermost annotation is the variable's own sort.
        E::Sub { e1, t1, .. } => walk(e1, Some(t1), pinning, out),
        E::Bool { .. } | E::Num { .. } | E::Text { .. } => {}
        E::Un { e2, .. } => walk(e2, None, pinning, out),
        E::Bin { e1, e2, .. }
        | E::Cmp { e1, e2, .. }
        | E::Idx { e1, e2 }
        | E::Comp { e1, e2 }
        | E::Mem { e1, e2 }
        | E::Cat { e1, e2 }
        | E::Upd { e1, e2, .. }
        | E::Ext { e1, e2, .. } => {
            walk(e1, None, pinning, out);
            walk(e2, None, pinning, out);
        }
        E::Slice { e1, e2, e3 } => {
            walk(e1, None, pinning, out);
            walk(e2, None, pinning, out);
            walk(e3, None, pinning, out);
        }
        E::Str { efs } => {
            for SpecTecExpField::Field { e, .. } in efs {
                walk(e, None, pinning, out);
            }
        }
        E::Dot { e1, .. }
        | E::Len { e1 }
        | E::Proj { e1, .. }
        | E::Case { e1, .. }
        | E::Uncase { e1, .. }
        | E::Unopt { e1 }
        | E::Lift { e1 }
        | E::Cvt { e1, .. } => walk(e1, None, pinning, out),
        E::Iter { e1, it, xes } => {
            // Identity-collapsed site: the domain replaces the node (walked
            // at the node's own pinning-ness); the body occurrence vanishes
            // from the encoding (walked non-pinning, so its `Sub` sorts are
            // still seen for the elementwise-guard plan).
            let collapsed =
                matches!(it, SpecTecIter::List | SpecTecIter::Opt) && xes.len() == 1 && {
                    let SpecTecIterExp::Dom { x, .. } = &xes[0];
                    matches!(super::super::encode::canon(e1), E::Var { id } if id == x)
                };
            if collapsed {
                let SpecTecIterExp::Dom { e: dom, .. } = &xes[0];
                walk(e1, None, false, out);
                walk(dom, None, pinning, out);
            } else {
                // Non-identity: the body child stays in the encoding; the
                // binders/domains are dropped from it.
                walk(e1, None, pinning, out);
                for SpecTecIterExp::Dom { e, .. } in xes {
                    walk(e, None, false, out);
                }
            }
        }
        E::Opt { eo } => {
            if let Some(e1) = eo {
                walk(e1, None, pinning, out);
            }
        }
        E::Tup { es } | E::List { es } => es.iter().for_each(|c| walk(c, None, pinning, out)),
        E::Call { as1, .. } => {
            // Call arguments are lifted into `fn.*` premises — never pinning.
            for a in as1 {
                if let SpecTecArg::Exp { e } = a {
                    walk(e, None, false, out);
                }
            }
        }
    }
}

/// The variables of a rule / `Dec` clause that **lost their sort** to the
/// `Sub`-strip: ≥1 `Sub`-wrapped occurrence and no bare occurrence at a
/// *pinning* position (see [`Occ::bare_pinning`]). `pinning_exprs` are the
/// positions that survive into the encoded conclusion (rule conclusion /
/// `Dec` patterns); `other_exprs` everything else (premises, `Dec` RHS).
/// Returns `(variable, lost sorts)` in name order.
pub fn sub_only_vars(
    pinning_exprs: &[&SpecTecExp],
    other_exprs: &[&SpecTecExp],
) -> Vec<(String, BTreeSet<String>)> {
    let mut occ: BTreeMap<String, Occ> = BTreeMap::new();
    for e in pinning_exprs {
        walk(e, None, true, &mut occ);
    }
    for e in other_exprs {
        walk(e, None, false, &mut occ);
    }
    occ.into_iter()
        .filter(|(_, o)| o.subbed > 0 && o.bare_pinning == 0 && !o.sorts.is_empty())
        .map(|(v, o)| (v, o.sorts))
        .collect()
}

/// Every expression a premise mentions (descending through `Iter` premises,
/// including their domain expressions).
pub fn prem_exprs<'e>(pr: &'e SpecTecPrem, out: &mut Vec<&'e SpecTecExp>) {
    match pr {
        SpecTecPrem::Rule { e, .. } | SpecTecPrem::If { e } => out.push(e),
        SpecTecPrem::Let { e1, e2 } => {
            out.push(e1);
            out.push(e2);
        }
        SpecTecPrem::Iter { pr1, xes, .. } => {
            prem_exprs(pr1, out);
            for SpecTecIterExp::Dom { e, .. } in xes {
                out.push(e);
            }
        }
        SpecTecPrem::Else => {}
    }
}

// ===========================================================================
// The case catalogue view: distinct keys + nullary flags
// ===========================================================================

/// The distinct case keys of a catalogued sort with their nullary flags
/// (`true` ⟺ the payload is the empty tuple). `None` if the sort is not a
/// catalogued variant. A key that is ambiguous *within* the type counts as
/// non-nullary (head-level guard — refusing to guess its arity).
pub fn sort_case_list(cat: &CaseCatalogue, sort: &str) -> Option<Vec<(String, bool)>> {
    let keys = cat.cases_of(sort)?;
    let mut seen = BTreeSet::new();
    let mut out = Vec::new();
    for k in keys {
        if seen.insert(k.clone()) {
            let nullary = cat.case(sort, k).is_some_and(|i| i.shape.arity() == 0);
            out.push((k.clone(), nullary));
        }
    }
    Some(out)
}

/// Whether every case of the list is nullary (the per-case-expansion
/// precondition).
pub fn all_nullary(cases: &[(String, bool)]) -> bool {
    cases.iter().all(|(_, n)| *n)
}

// ===========================================================================
// Per-case expansion (the `Dec`-leg fix)
// ===========================================================================

/// The nullary-case expression for a case key (`case.<key>` applied to the
/// empty tuple — exactly what [`super::super::encode::encode_exp`] gives the
/// key's use sites).
pub fn nullary_case(key: &str) -> SpecTecExp {
    SpecTecExp::Case {
        op: MixOp::new(key.split('%').map(str::to_owned).collect()),
        e1: Box::new(SpecTecExp::Tup { es: vec![] }),
    }
}

/// Deep, pure substitution of `rep` for the metavariable `var` in an
/// expression (metavariables have no binders in SpecTec rule syntax — `Iter`
/// domain bindings shadow nothing we substitute for, since expansion targets
/// sub-only *pattern* variables, never iteration element variables).
pub fn subst_var(e: &SpecTecExp, var: &str, rep: &SpecTecExp) -> SpecTecExp {
    use SpecTecExp as E;
    let s = |x: &SpecTecExp| subst_var(x, var, rep);
    match e {
        E::Var { id } if id == var => rep.clone(),
        E::Var { .. } | E::Bool { .. } | E::Num { .. } | E::Text { .. } => e.clone(),
        E::Sub { t1, t2, e1 } => E::Sub {
            t1: t1.clone(),
            t2: t2.clone(),
            e1: Box::new(s(e1)),
        },
        E::Un { op, t, e2 } => E::Un {
            op: op.clone(),
            t: t.clone(),
            e2: Box::new(s(e2)),
        },
        E::Bin { op, t, e1, e2 } => E::Bin {
            op: op.clone(),
            t: t.clone(),
            e1: Box::new(s(e1)),
            e2: Box::new(s(e2)),
        },
        E::Cmp { op, t, e1, e2 } => E::Cmp {
            op: op.clone(),
            t: t.clone(),
            e1: Box::new(s(e1)),
            e2: Box::new(s(e2)),
        },
        E::Idx { e1, e2 } => E::Idx {
            e1: Box::new(s(e1)),
            e2: Box::new(s(e2)),
        },
        E::Slice { e1, e2, e3 } => E::Slice {
            e1: Box::new(s(e1)),
            e2: Box::new(s(e2)),
            e3: Box::new(s(e3)),
        },
        E::Upd { e1, path, e2 } => E::Upd {
            e1: Box::new(s(e1)),
            path: path.clone(),
            e2: Box::new(s(e2)),
        },
        E::Ext { e1, path, e2 } => E::Ext {
            e1: Box::new(s(e1)),
            path: path.clone(),
            e2: Box::new(s(e2)),
        },
        E::Str { efs } => E::Str {
            efs: efs
                .iter()
                .map(|SpecTecExpField::Field { at, e }| SpecTecExpField::Field {
                    at: at.clone(),
                    e: s(e),
                })
                .collect(),
        },
        E::Dot { e1, at } => E::Dot {
            e1: Box::new(s(e1)),
            at: at.clone(),
        },
        E::Comp { e1, e2 } => E::Comp {
            e1: Box::new(s(e1)),
            e2: Box::new(s(e2)),
        },
        E::Mem { e1, e2 } => E::Mem {
            e1: Box::new(s(e1)),
            e2: Box::new(s(e2)),
        },
        E::Len { e1 } => E::Len {
            e1: Box::new(s(e1)),
        },
        E::Tup { es } => E::Tup {
            es: es.iter().map(s).collect(),
        },
        E::Call { x, as1 } => E::Call {
            x: x.clone(),
            as1: as1.iter().map(|a| subst_var_arg(a, var, rep)).collect(),
        },
        E::Iter { e1, it, xes } => E::Iter {
            e1: Box::new(s(e1)),
            it: it.clone(),
            xes: xes
                .iter()
                .map(|SpecTecIterExp::Dom { x, e }| SpecTecIterExp::Dom {
                    x: x.clone(),
                    e: s(e),
                })
                .collect(),
        },
        E::Proj { e1, i } => E::Proj {
            e1: Box::new(s(e1)),
            i: *i,
        },
        E::Case { op, e1 } => E::Case {
            op: op.clone(),
            e1: Box::new(s(e1)),
        },
        E::Uncase { e1, op } => E::Uncase {
            e1: Box::new(s(e1)),
            op: op.clone(),
        },
        E::Opt { eo } => E::Opt {
            eo: eo.as_ref().map(|b| Box::new(s(b))),
        },
        E::Unopt { e1 } => E::Unopt {
            e1: Box::new(s(e1)),
        },
        E::List { es } => E::List {
            es: es.iter().map(s).collect(),
        },
        E::Lift { e1 } => E::Lift {
            e1: Box::new(s(e1)),
        },
        E::Cat { e1, e2 } => E::Cat {
            e1: Box::new(s(e1)),
            e2: Box::new(s(e2)),
        },
        E::Cvt { nt1, nt2, e1 } => E::Cvt {
            nt1: nt1.clone(),
            nt2: nt2.clone(),
            e1: Box::new(s(e1)),
        },
    }
}

fn subst_var_arg(a: &SpecTecArg, var: &str, rep: &SpecTecExp) -> SpecTecArg {
    match a {
        SpecTecArg::Exp { e } => SpecTecArg::Exp {
            e: subst_var(e, var, rep),
        },
        other => other.clone(),
    }
}

fn subst_var_prem(pr: &SpecTecPrem, var: &str, rep: &SpecTecExp) -> SpecTecPrem {
    match pr {
        SpecTecPrem::Rule { x, as1, op, e } => SpecTecPrem::Rule {
            x: x.clone(),
            as1: as1.iter().map(|a| subst_var_arg(a, var, rep)).collect(),
            op: op.clone(),
            e: subst_var(e, var, rep),
        },
        SpecTecPrem::If { e } => SpecTecPrem::If {
            e: subst_var(e, var, rep),
        },
        SpecTecPrem::Let { e1, e2 } => SpecTecPrem::Let {
            e1: subst_var(e1, var, rep),
            e2: subst_var(e2, var, rep),
        },
        SpecTecPrem::Iter { pr1, it, xes } => SpecTecPrem::Iter {
            pr1: Box::new(subst_var_prem(pr1, var, rep)),
            it: it.clone(),
            xes: xes
                .iter()
                .map(|SpecTecIterExp::Dom { x, e }| SpecTecIterExp::Dom {
                    x: x.clone(),
                    e: subst_var(e, var, rep),
                })
                .collect(),
        },
        SpecTecPrem::Else => SpecTecPrem::Else,
    }
}

/// Substitute a nullary case for a metavariable throughout a `Dec` clause
/// (patterns, RHS, premises).
pub fn subst_clause(c: &SpecTecClause, var: &str, key: &str) -> SpecTecClause {
    let rep = nullary_case(key);
    let SpecTecClause::Clause { ps, as_, e, prs } = c;
    SpecTecClause::Clause {
        ps: ps.clone(),
        as_: as_.iter().map(|a| subst_var_arg(a, var, &rep)).collect(),
        e: subst_var(e, var, &rep),
        prs: prs.iter().map(|p| subst_var_prem(p, var, &rep)).collect(),
    }
}

/// Cap on the per-clause expansion product (cross product over the clause's
/// expandable variables). Above it, every variable falls back to a sort
/// guard — still sound, still exact for nullary sorts. Kept small: the
/// 2-case sorts (`Inn`/`Fnn`/`addrtype`/…) expand premise-free, while the
/// wide sorts (`Jnn` 4, `lanetype` 6, `absheaptype` 13, `$zeroop`'s 4×4
/// product) would multiply clause copies — and duplicate any opaque residue
/// they carry — for no fireability the (equally exact) nullary guard doesn't
/// already give.
pub const MAX_EXPANSION: usize = 4;

// ===========================================================================
// Sort-guard premises + the `ev.sort.<ty>` relations (the guard fix)
// ===========================================================================

/// How a sort constraint re-attaches to a metavariable.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GuardKind {
    /// `ev.sort.<ty>(x)` — the variable holds one value of the sort.
    Plain,
    /// `ev.sort.list.<ty>(xs)` — every element of the snoc spine is of the
    /// sort (an identity-collapsed `x*` iteration's domain).
    List,
    /// `ev.sort.opt.<ty>(xo)` — `opt.none` or `opt.some` of the sort (an
    /// identity-collapsed `x?` iteration's domain).
    Opt,
}

impl GuardKind {
    /// The `ev.*` tag suffix (also the on-demand dedup key).
    pub fn tag(self, sort: &str) -> String {
        match self {
            GuardKind::Plain => format!("sort.{sort}"),
            GuardKind::List => format!("sort.list.{sort}"),
            GuardKind::Opt => format!("sort.opt.{sort}"),
        }
    }
}

/// The guard premise `ev.<kind-tag>(x)` for a metavariable.
pub fn guard_judgement(var: &str, sort: &str, kind: GuardKind) -> Result<Term> {
    ev_graph(&kind.tag(sort), &[], &metavar(var))
}

/// The clauses of `ev.sort.<sort>`: one per distinct case key. Nullary cases
/// pin the payload to the unit `tup` (exact); payload-carrying cases leave it
/// `∀`-open (head-level — see the module docs).
pub fn sort_clauses(sort: &str, cases: &[(String, bool)]) -> Result<Vec<Clause>> {
    use super::super::encode::{app, con};
    let mut out = Vec::with_capacity(cases.len());
    for (key, nullary) in cases {
        let (metavars, payload) = if *nullary {
            (vec![], con("tup"))
        } else {
            (vec!["%p".to_string()], metavar("%p"))
        };
        out.push(Clause {
            metavars,
            prems: vec![],
            concl: ev_graph(
                &format!("sort.{sort}"),
                &[],
                &app(con(format!("case.{key}")), payload)?,
            )?,
        });
    }
    Ok(out)
}

/// The clauses of `ev.sort.list.<sort>` — elementwise list membership over
/// snoc spines: `[]` is in, and `xs·x` is in when `xs` is and `x` is of the
/// sort. Callers must request the plain `sort.<sort>` clauses too.
pub fn list_sort_clauses(sort: &str) -> Result<Vec<Clause>> {
    use super::super::encode::{app, con};
    let tag = GuardKind::List.tag(sort);
    let nil = Clause {
        metavars: vec![],
        prems: vec![],
        concl: ev_graph(&tag, &[], &con("list"))?,
    };
    let snoc = Clause {
        metavars: vec!["%xs".into(), "%x".into()],
        prems: vec![
            super::LowerPrem::Judgement(ev_graph(&tag, &[], &metavar("%xs"))?),
            super::LowerPrem::Judgement(guard_judgement("%x", sort, GuardKind::Plain)?),
        ],
        concl: ev_graph(&tag, &[], &app(metavar("%xs"), metavar("%x"))?)?,
    };
    Ok(vec![nil, snoc])
}

/// The clauses of `ev.sort.opt.<sort>` — `opt.none`, or `opt.some x` with `x`
/// of the sort. Callers must request the plain `sort.<sort>` clauses too.
pub fn opt_sort_clauses(sort: &str) -> Result<Vec<Clause>> {
    use super::super::encode::{app, con};
    let tag = GuardKind::Opt.tag(sort);
    let none = Clause {
        metavars: vec![],
        prems: vec![],
        concl: ev_graph(&tag, &[], &con("opt.none"))?,
    };
    let some = Clause {
        metavars: vec!["%x".into()],
        prems: vec![super::LowerPrem::Judgement(guard_judgement(
            "%x",
            sort,
            GuardKind::Plain,
        )?)],
        concl: ev_graph(&tag, &[], &app(con("opt.some"), metavar("%x"))?)?,
    };
    Ok(vec![none, some])
}

// ===========================================================================
// The per-clause/per-rule fix plan
// ===========================================================================

/// One guard to attach: the premise `ev.<kind-tag(sort)>(st$v$<var>)` — the
/// caller pushes it iff `var` is one of the lowered clause's metavariables
/// (a variable that collapsed away entirely constrains nothing).
#[derive(Debug, Clone)]
pub struct Guard {
    pub var: String,
    pub sort: String,
    pub kind: GuardKind,
}

/// The sort fix for one rule / `Dec` clause.
#[derive(Debug, Clone, Default)]
pub struct SortPlan {
    /// Per-case expansions (var → nullary case keys) — `Dec` leg only.
    pub expansions: Vec<(String, Vec<String>)>,
    /// Guard premises to attach.
    pub guards: Vec<Guard>,
    /// Sub-only variables whose sort could not be guarded (uncatalogued sort
    /// or a compound collapsed-iteration domain) — the caller must attach an
    /// opaque premise per entry (`(var, sort)`); 0 on the bundled corpus.
    pub unguardable: Vec<(String, String)>,
}

/// Scan for **identity-collapsed iteration sites**: `Iter` nodes the
/// [`super::super::encode::canon`] view collapses to their domain. Returns
/// element var → the collapse targets `(domain var if plain, opt?)`.
fn collapse_sites(exprs: &[&SpecTecExp]) -> BTreeMap<String, BTreeSet<(Option<String>, bool)>> {
    use SpecTecExp as E;
    use covalence_spectec::ast::SpecTecIter;
    fn go(e: &SpecTecExp, out: &mut BTreeMap<String, BTreeSet<(Option<String>, bool)>>) {
        if let E::Iter { e1, it, xes } = e
            && matches!(it, SpecTecIter::List | SpecTecIter::Opt)
            && xes.len() == 1
        {
            let SpecTecIterExp::Dom { x, e: dom } = &xes[0];
            if matches!(super::super::encode::canon(e1), E::Var { id } if id == x) {
                let d = match super::super::encode::canon(dom) {
                    E::Var { id } => Some(id.clone()),
                    _ => None,
                };
                out.entry(x.clone())
                    .or_default()
                    .insert((d, matches!(it, SpecTecIter::Opt)));
            }
        }
        // Recurse everywhere (a site may nest under anything).
        visit_children_all(e, &mut |c| go(c, out));
    }
    let mut out = BTreeMap::new();
    for e in exprs {
        go(e, &mut out);
    }
    out
}

/// Total child visitor (including `Sub` bodies, `Iter` bodies and domains).
fn visit_children_all(e: &SpecTecExp, f: &mut impl FnMut(&SpecTecExp)) {
    use SpecTecExp as E;
    match e {
        E::Var { .. } | E::Bool { .. } | E::Num { .. } | E::Text { .. } => {}
        E::Un { e2, .. } => f(e2),
        E::Bin { e1, e2, .. }
        | E::Cmp { e1, e2, .. }
        | E::Idx { e1, e2 }
        | E::Comp { e1, e2 }
        | E::Mem { e1, e2 }
        | E::Cat { e1, e2 }
        | E::Upd { e1, e2, .. }
        | E::Ext { e1, e2, .. } => {
            f(e1);
            f(e2);
        }
        E::Slice { e1, e2, e3 } => {
            f(e1);
            f(e2);
            f(e3);
        }
        E::Str { efs } => {
            for SpecTecExpField::Field { e, .. } in efs {
                f(e);
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
        | E::Sub { e1, .. } => f(e1),
        E::Iter { e1, xes, .. } => {
            f(e1);
            for SpecTecIterExp::Dom { e, .. } in xes {
                f(e);
            }
        }
        E::Opt { eo } => {
            if let Some(e1) = eo {
                f(e1);
            }
        }
        E::Tup { es } | E::List { es } => es.iter().for_each(f),
        E::Call { as1, .. } => {
            for a in as1 {
                if let SpecTecArg::Exp { e } = a {
                    f(e);
                }
            }
        }
    }
}

/// Compute the sort fix for one rule / clause. `pinning_exprs` are the
/// positions surviving into the encoded conclusion (rule conclusion / `Dec`
/// patterns), `other_exprs` everything else (premises, `Dec` RHS) — see
/// [`sub_only_vars`]. `allow_expansion` is `true` on the `Dec` leg only (the
/// rule leg must keep one clause per rule).
pub fn plan(
    pinning_exprs: &[&SpecTecExp],
    other_exprs: &[&SpecTecExp],
    cat: &CaseCatalogue,
    allow_expansion: bool,
) -> SortPlan {
    let sub_only = sub_only_vars(pinning_exprs, other_exprs);
    if sub_only.is_empty() {
        return SortPlan::default();
    }
    let exprs: Vec<&SpecTecExp> = pinning_exprs
        .iter()
        .chain(other_exprs.iter())
        .copied()
        .collect();
    let sites = collapse_sites(&exprs);
    let mut plan = SortPlan::default();
    // Expansion candidates gathered first (cap applied after).
    let mut candidates: Vec<(String, String, Vec<String>)> = Vec::new(); // (var, sort, keys)
    for (v, sorts) in sub_only {
        if let Some(targets) = sites.get(&v) {
            // Identity-collapsed element: guard the domain(s) elementwise.
            for (dom, is_opt) in targets {
                let kind = if *is_opt {
                    GuardKind::Opt
                } else {
                    GuardKind::List
                };
                for sort in &sorts {
                    match (dom, sort_case_list(cat, sort)) {
                        (Some(d), Some(_)) => plan.guards.push(Guard {
                            var: d.clone(),
                            sort: sort.clone(),
                            kind,
                        }),
                        _ => plan.unguardable.push((v.clone(), sort.clone())),
                    }
                }
            }
            // The element var may *also* occur directly (outside collapse
            // sites); a plain guard then applies too — attached only if it
            // survives as a clause metavariable (caller checks membership).
            for sort in &sorts {
                if sort_case_list(cat, sort).is_some() {
                    plan.guards.push(Guard {
                        var: v.clone(),
                        sort: sort.clone(),
                        kind: GuardKind::Plain,
                    });
                }
            }
            continue;
        }
        let mut expanded = false;
        if allow_expansion
            && sorts.len() == 1
            && let Some(sort) = sorts.first()
            && let Some(cases) = sort_case_list(cat, sort)
            && all_nullary(&cases)
        {
            candidates.push((
                v.clone(),
                sort.clone(),
                cases.into_iter().map(|(k, _)| k).collect(),
            ));
            expanded = true;
        }
        if !expanded {
            for sort in &sorts {
                if sort_case_list(cat, sort).is_some() {
                    plan.guards.push(Guard {
                        var: v.clone(),
                        sort: sort.clone(),
                        kind: GuardKind::Plain,
                    });
                } else {
                    plan.unguardable.push((v.clone(), sort.clone()));
                }
            }
        }
    }
    // Cap the cross product: expand the narrowest sorts first while the
    // product stays within [`MAX_EXPANSION`]; the rest guard (nullary sorts
    // guard exactly, so nothing is lost but a premise).
    candidates.sort_by_key(|(v, _, ks)| (ks.len(), v.clone()));
    let mut product = 1usize;
    for (v, sort, ks) in candidates {
        if product.saturating_mul(ks.len().max(1)) <= MAX_EXPANSION {
            product *= ks.len().max(1);
            plan.expansions.push((v, ks));
        } else {
            plan.guards.push(Guard {
                var: v,
                sort,
                kind: GuardKind::Plain,
            });
        }
    }
    plan
}

/// The on-demand clause families a guard needs, as `(dedup key, clauses)`
/// pairs — `List`/`Opt` kinds also carry the plain family their element
/// premise uses. Fails if the sort is not catalogued (planned guards never
/// are; see [`SortPlan::unguardable`]).
pub fn guard_families(guard: &Guard, cat: &CaseCatalogue) -> Result<Vec<(String, Vec<Clause>)>> {
    let cases = sort_case_list(cat, &guard.sort).ok_or_else(|| {
        covalence_core::Error::ConnectiveRule(format!(
            "spectec sortguard: sort `{}` is not a catalogued variant",
            guard.sort
        ))
    })?;
    let plain = (
        GuardKind::Plain.tag(&guard.sort),
        sort_clauses(&guard.sort, &cases)?,
    );
    Ok(match guard.kind {
        GuardKind::Plain => vec![plain],
        GuardKind::List => vec![
            plain,
            (
                GuardKind::List.tag(&guard.sort),
                list_sort_clauses(&guard.sort)?,
            ),
        ],
        GuardKind::Opt => vec![
            plain,
            (
                GuardKind::Opt.tag(&guard.sort),
                opt_sort_clauses(&guard.sort)?,
            ),
        ],
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn var(id: &str) -> SpecTecExp {
        SpecTecExp::Var { id: id.into() }
    }
    fn sub(e: SpecTecExp, t1: &str, t2: &str) -> SpecTecExp {
        SpecTecExp::Sub {
            t1: SpecTecTyp::Var {
                x: t1.into(),
                as1: vec![],
            },
            t2: SpecTecTyp::Var {
                x: t2.into(),
                as1: vec![],
            },
            e1: Box::new(e),
        }
    }

    #[test]
    fn sub_only_detection() {
        // x sub-only; y bare once at a pinning position (harmless).
        let e1 = sub(var("x"), "Inn", "numtype");
        let e2 = SpecTecExp::Tup {
            es: vec![sub(var("y"), "Fnn", "numtype"), var("y")],
        };
        let so = sub_only_vars(&[&e1, &e2], &[]);
        assert_eq!(so.len(), 1);
        assert_eq!(so[0].0, "x");
        assert!(so[0].1.contains("Inn"));
    }

    #[test]
    fn premise_bare_occurrence_does_not_rescue() {
        // v is Sub-wrapped in the conclusion and bare in a premise: premise
        // relations can be sort-coarse, so v still needs a guard.
        let concl = sub(var("v"), "val", "instr");
        let prem = var("v");
        let so = sub_only_vars(&[&concl], &[&prem]);
        assert_eq!(so.len(), 1);
        assert_eq!(so[0].0, "v");
        // …while a bare occurrence in the conclusion rescues.
        let concl2 = SpecTecExp::Tup {
            es: vec![sub(var("v"), "val", "instr"), var("v")],
        };
        assert!(sub_only_vars(&[&concl2], &[]).is_empty());
        // …but a bare occurrence inside a conclusion *call argument* does not
        // (call args are lifted into premises).
        let call = SpecTecExp::Call {
            x: "f".into(),
            as1: vec![SpecTecArg::Exp { e: var("v") }],
        };
        let concl3 = SpecTecExp::Tup {
            es: vec![sub(var("v"), "val", "instr"), call],
        };
        assert_eq!(sub_only_vars(&[&concl3], &[]).len(), 1);
    }

    #[test]
    fn nullary_case_encodes_like_use_sites() {
        use super::super::super::encode::{app, con, encode_exp};
        let enc = encode_exp(&nullary_case("I32")).unwrap();
        assert_eq!(enc, app(con("case.I32"), con("tup")).unwrap());
    }

    #[test]
    fn subst_replaces_under_sub() {
        let e = sub(var("x"), "Inn", "numtype");
        let got = subst_var(&e, "x", &nullary_case("I32"));
        let SpecTecExp::Sub { e1, .. } = got else {
            panic!("Sub preserved");
        };
        assert_eq!(*e1, nullary_case("I32"));
    }
}
