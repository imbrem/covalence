//! **Functions as graph relations** — every `SpecTecDef::Dec` clause
//! `f(pats) = rhs -- prs` lowers to a clause of relation `fn.<f>` (conclusion
//! built ONLY via [`super::fn_graph`]): zero axioms, relational reading,
//! call-flattened RHS. See `notes/vibes/logics/spectec-total-load.md` leg 4.
//!
//! ## Conventions (load-bearing; the whole rule set must agree on these)
//!
//! - **Spine layout**: `fn.<f>` judgement = the `Exp` arguments in declaration
//!   order followed by the result ([`super::fn_graph`]). **`Typ` arguments are
//!   dropped** from the spine: every `Typ` argument on a Dec clause LHS in the
//!   corpus is a plain type variable (measured: 30/30), so no Dec dispatches on
//!   a type argument and the graph is type-generic — dropping is collision-free
//!   and matches `encode::call_exp_args` (which already drops non-`Exp` call
//!   arguments). `Def` arguments are dropped too — they are absorbed into the
//!   **monomorphised tag** (below). `Gram` arguments never occur (opaque if
//!   they ever do).
//! - **Monomorphisation**: the 16 higher-order combinators (`iv*`/`fv*`, `Def`
//!   params) are specialised per constant op actually passed at a call site:
//!   tag `fn.<f>$<op>` (multi-param: `$`-joined in param order), one clause set
//!   per distinct instantiation. Call sites resolve their `Def` args through
//!   the active instantiation, so `$f_(x)` inside a combinator body becomes a
//!   `fn.<op>` premise. The corpus has no combinator→combinator `Def`-arg
//!   chains (measured), so discovery is a single scan; instantiation vectors
//!   mentioning unknown (non-Dec) names are counted and skipped.
//! - **Zero-clause builtins** (91: float/int-bit/serialisation primitives):
//!   their `fn.<g>` tags simply have **no clauses** — declared frontier, sound
//!   (judgements mentioning them are underivable), counted in the census,
//!   never axiomatised.
//! - **`Sub` casts are stripped** (they are semantically transparent and the
//!   encoder drops their types anyway), and the **identity iteration**
//!   `x*`/`x?` with a single binding `x ← xs` and body exactly `Var x`
//!   collapses to `xs` (exact: an identity-mapped iteration *is* its domain).
//!   This is what makes the corpus's cons-style list patterns expressible.
//!   (`ListN`/`List1` identity iterations are *not* collapsed — they carry a
//!   length constraint that collapsing would drop, an over-approximation.)
//! - **Sort fix for `Sub`-only metavariables** (see [`super::sortguard`]): a
//!   clause metavariable whose *every* occurrence is `Sub`-wrapped (e.g. the
//!   `Inn` in `$default_(Inn) = (CONST Inn 0)`) would otherwise be `∀`-open at
//!   the wrong sorts and derive false graph facts (`fn.default_(F32, CONST
//!   F32 0)`). **Policy (per site):** when the lost sort's cases are
//!   catalogue-enumerable and all **nullary** (`Inn`, `Fnn`, `Jnn`, `Vnn`,
//!   `numtype`, `addrtype`, `consttype`, `lanetype`, `packtype`,
//!   `absheaptype`, …), the clause is **per-case expanded** — one clause per
//!   concrete case, exact and premise-free (the graph stays maximally
//!   fireable; the `Dec` leg's clause multiplicity is already variable, so
//!   expansion costs nothing structurally). Where expansion doesn't apply
//!   (payload-carrying cases: `valtype`, `import`; multi-sort annotations;
//!   expansion products over [`super::sortguard::MAX_EXPANSION`]) the clause
//!   instead gets an **`ev.sort.<ty>` guard premise** (on-demand clauses like
//!   `ev.neq`, exact for nullary cases, head-level for payload cases). A
//!   sub-only variable that is an identity-collapsed iteration *element* gets
//!   the elementwise guard `ev.sort.list.<ty>`/`ev.sort.opt.<ty>` on its
//!   domain variable instead (expansion would defeat the collapse). Both
//!   fixes only specialize/strengthen — the soundness frame is preserved by
//!   construction. The rule leg ([`super::flatten`]) uses guards uniformly
//!   (expansion would break its one-clause-per-rule addressing contract).
//! - **`Cat` splits**: a concatenation encodes exactly where possible —
//!   a literal-`List` segment appends directly onto the running snoc spine
//!   (so the right-singleton pattern `xs ++ [x]` is literally `app(xs, x)`),
//!   and every non-literal segment beyond the first becomes an [`ev_graph`]
//!   `ev.cat` premise (`ev.cat(l, r, out)` ⟺ `out = l ++ r` over snoc
//!   spines, two schematic clauses, emitted once per rule set). This makes the
//!   dominant cons-style pattern `[h] ++ t*` fire on ground lists: the
//!   conclusion slot is a metavariable constrained by a derivable `ev.cat`
//!   premise.
//! - **Call lifting**: every `Call` (top-level or nested, in patterns, RHS or
//!   `Rule` premises) becomes a fresh metavariable plus a `fn.<callee>` graph
//!   premise, innermost first. Recursion through self/mutual calls is just a
//!   premise on the same/other `fn.<g>` tag. `If` conditions are *not*
//!   pre-lifted — they go to [`CondFlattener::cond`] whole (the real flattener
//!   owns condition-internal calls) — but their `Def`-param callee names ARE
//!   pre-substituted through the monomorphisation environment first
//!   ([`subst_def_calls`]): the flattener knows nothing of the active
//!   instantiation, so an unresolved `$f_(…)` in a condition would flatten
//!   against the nonexistent tag `fn.f_` (silently underivable). Unresolved
//!   names are censused `dec.def-param`.
//! - **Numeric-metavar discipline**: a metavar used arithmetically (a direct
//!   `Var` operand of a `Bin`/`Cmp`/`Un` node annotated `Num(Nat)`) appears in
//!   judgement spines as `app(st$c$num.nat, st$v$n)` (the wrapped form) and is
//!   instantiated with a **bare numeral**, which simultaneously yields the
//!   encoding of the substituted literal in the spine and a closed,
//!   kernel-reducible arithmetic antecedent. The wrap is applied (term-level
//!   substitution) to the conclusion and to the premises built *here*; a
//!   flattener's own premises are its own responsibility.
//! - **Clause order**: SpecTec `Dec` clauses match **in order** — a later
//!   clause applies only where no earlier clause of the same Dec does (an
//!   explicit `Else` premise states the same constraint in the source, so it
//!   only changes census labels). Loading a later clause without its order
//!   complement would over-approximate wherever it overlaps an earlier
//!   sibling with a different RHS (concretely: `idiv_`/`irem_`'s truncating
//!   legs vs their `eps` legs at `i_2 = 0`). So **every** clause gets, per
//!   earlier sibling: nothing when provably disjoint (rigid pattern clash,
//!   or identical patterns with **complementary guards** — some conjunct of
//!   one guard set is the syntactic negation of a conjunct of the other, up
//!   to comparison-operand canonicalisation: the `signed_`/`imin_`/`imax_`
//!   strict-dual shape); nothing when the overlap is **confluent** (the
//!   patterns correspond with one side purely more general and the RHSs are
//!   literally equal under the correspondence — firing there re-derives a
//!   fact the earlier clause already derives); the **negated guard
//!   conjunction** as an ordinary condition when the patterns are identical
//!   and the earlier guards are pure pattern-variable `If`s (comparison
//!   flipping, De Morgan); otherwise an [`opaque`] premise (`dec.order`, or
//!   the finer `dec.else-*` buckets for explicit-`Else` clauses) — counted,
//!   never fabricated, never dropped.
//! - **Non-value result spines**: a graph conclusion may still carry an
//!   *unevaluated* operator node where no evaluator family exists yet — a
//!   `cvt.*` numeric conversion, or a non-`nat` `bin.*`/`un.*` arithmetic
//!   spine (the `Rat`-typed `idiv_` bodies). These are **not** encodings of
//!   SpecTec values: they are junk terms a consumer must treat as opaque
//!   (never compare against a value encoding, never project). They are
//!   sound — a spine mentioning them can only be matched by the same spine —
//!   but fireability at such points is meaningless until the corresponding
//!   `ev.*` family lands.
//! - **Store writes evaluate**: an `Upd`/`Ext` RHS along a `Dot`/`Idx`
//!   access path (`$with_local`/`$with_table`/`$add_structinst`/… — the
//!   store-writer family) flattens through the on-demand
//!   `ev.upd.*`/`ev.ext.*` write families
//!   ([`super::evalrel::upd_ext_families`], via the flattener's `enc` in
//!   both modes — so `$with_locals`' recursive *call-argument* write
//!   evaluates too): the graph conclusion carries the genuinely-updated
//!   value, and the writing `Step` rules ground
//!   (`total::tests::store_writes_fire_end_to_end`). A `Slice` path segment
//!   refuses (an exact slice-write evaluator doesn't exist yet; a write is
//!   never approximated) — `$with_mem` keeps its coarse spine, censused
//!   below.
//! - **Coarse spine honesty**: if a conclusion still contains a
//!   collision-prone encoding node after all of the above (a residual
//!   non-identity `iter.*` node, or an unevaluated `upd`/`ext` carrying an
//!   index/slice access path — post the write families, only slice paths),
//!   the clause gets an `opaque` premise
//!   (`dec.coarse-spine`): a colliding *conclusion* could make the graph
//!   over-approximate, which the soundness frame forbids. Coarse nodes in
//!   *premise* position are safe (they only make the clause harder to fire)
//!   and are counted separately.
//!
//! Loading is **total**: every equation clause of every Dec yields a
//! [`Clause`] (the opaque hatch is the last resort); dischargeability is the
//! growing number ([`FnCensus`] reports exact buckets).

use std::collections::{BTreeMap, BTreeSet};

use covalence_core::subst::subst_free;
use covalence_core::{Result, Term, Var};
use covalence_spectec::ast::{
    SpecTecArg, SpecTecBinOp, SpecTecBoolTyp, SpecTecClause, SpecTecCmpOp, SpecTecDef, SpecTecExp,
    SpecTecExpField, SpecTecIter, SpecTecIterExp, SpecTecNum, SpecTecNumTyp, SpecTecOpTyp,
    SpecTecParam, SpecTecPrem, SpecTecRule, SpecTecTyp, SpecTecUnOp,
};

use super::super::encode::{self, collect_metavars, con, metavar, metavar_name, mixop_key, phi};
use super::{Clause, CondFlattener, LowerPrem, fn_graph, opaque};

// ============================================================================
// Reports
// ============================================================================

/// What lowering one Dec (or one monomorphised instance of it) produced.
#[derive(Debug, Default, Clone)]
pub struct DecReport {
    /// The function name (`Dec.x`).
    pub name: String,
    /// The relation tag suffix used (`<name>` or `<name>$<op>…`).
    pub tag: String,
    /// Clauses emitted.
    pub clauses: usize,
    /// Clauses with **no** opaque residue.
    pub clean: usize,
    /// Clauses whose only opaque residue is a condition-flattener escape:
    /// the [`super::PureFlattener`] `cond` hatch, or a real-flattener
    /// `cond.*` refusal (a condition shape the flattener cannot express yet
    /// — these become clean as the condition leg grows).
    pub cond_only: usize,
    /// Clauses with structural opaque residue (anything beyond `cond`).
    pub opaque: usize,
    /// Opaque reasons → clause counts (a clause may hit several).
    pub reasons: BTreeMap<String, usize>,
    /// Clauses whose *premises* contain coarse encoding nodes (fireability
    /// caveat only — sound, counted for honesty).
    pub coarse_premises: usize,
    /// Extra clause copies from per-case sort expansion (beyond one per
    /// source clause).
    pub expanded: usize,
    /// `ev.sort.*` guard premises attached.
    pub sort_guards: usize,
    /// Expanded iterated-premise sites owned by this lowering.
    pub iter_sites: usize,
    /// Star clauses defining those sites (two per site).
    pub iter_aux_clauses: usize,
}

/// Whole-corpus census for [`spec_fn_clauses`].
#[derive(Debug, Default, Clone)]
pub struct FnCensus {
    /// Total `Dec` definitions seen.
    pub functions: usize,
    /// Zero-clause builtins (declared frontier: tags with no clauses).
    pub builtins: usize,
    /// Higher-order (`Def`-param) combinators.
    pub combinators: usize,
    /// Monomorphised combinator instances emitted.
    pub mono_instances: usize,
    /// `Def`-arg call instantiations skipped (unknown op names) — 0 on the
    /// bundled corpus.
    pub unresolved_instantiations: usize,
    /// Source equation clauses in the spec (the 804).
    pub spec_clauses: usize,
    /// Source clauses represented by at least one emitted clause (loading is
    /// total: must equal `spec_clauses`).
    pub spec_loaded: usize,
    /// Source clauses whose canonical lowering is clean.
    pub spec_clean: usize,
    /// Source clauses whose only residue is flattener-`cond` opaqueness.
    pub spec_cond_only: usize,
    /// Source clauses with structural opaque residue.
    pub spec_opaque: usize,
    /// Clauses emitted in total (source/expanded/mono clauses plus Dec-owned
    /// star clauses; excludes evaluator families drained separately).
    pub clauses_emitted: usize,
    /// Auxiliary clauses appended (the `ev.cat` pair).
    pub aux_clauses: usize,
    /// Functions (with ≥1 clause) whose canonical lowering is fully clean.
    pub fns_fully_clean: usize,
    /// Opaque reasons → clause counts, over canonical lowerings.
    pub reasons: BTreeMap<String, usize>,
    /// Canonical clauses with coarse nodes in premise position (info).
    pub coarse_premises: usize,
    /// Extra clause copies from per-case sort expansion, over **all**
    /// lowerings (mono instances included).
    pub expanded_clauses: usize,
    /// `ev.sort.*` guard premises attached, over all lowerings.
    pub sort_guards: usize,
    /// Expanded iterated-premise sites, over all lowerings.
    pub iter_sites: usize,
    /// Star clauses defining those sites.
    pub iter_aux_clauses: usize,
    /// Per-function/instance reports, in emission order.
    pub reports: Vec<DecReport>,
}

// ============================================================================
// The `ev.cat` evaluator relation (shared with the condition-flattener leg)
// ============================================================================

/// The canonical judgement body of an **evaluator** relation instance — the
/// one shared constructor, re-exported from [`super::evalrel`] so the `Dec`
/// leg and the condition flattener can never diverge on tag or layout.
pub use super::evalrel::ev_graph;

/// The two schematic clauses of `ev.cat` — `ev.cat(left, right, out)` ⟺
/// `out = left ++ right` over left-nested snoc spines (base `st$c$list`),
/// recursing on `right`. **Exactly** [`super::evalrel::cat_clauses`] (one
/// definition — a same-tag/different-layout divergence between the legs would
/// over-approximate).
pub fn cat_aux_clauses() -> Result<Vec<Clause>> {
    super::evalrel::cat_clauses()
}

// ============================================================================
// Pass 1: pure collapse (Sub-strip + identity-iteration collapse)
// ============================================================================

/// Deep, pure rewrite: strip `Sub` casts; collapse identity iterations
/// (`List`/`Opt`, single `x ← xs` binding, body exactly `Var x`) to their
/// domain. Everything else is rebuilt structurally.
fn collapse(e: &SpecTecExp) -> SpecTecExp {
    use SpecTecExp as E;
    match e {
        E::Sub { e1, .. } => collapse(e1),
        E::Iter { e1, it, xes } => {
            let b = collapse(e1);
            let xes2: Vec<SpecTecIterExp> = xes
                .iter()
                .map(|SpecTecIterExp::Dom { x, e }| SpecTecIterExp::Dom {
                    x: x.clone(),
                    e: collapse(e),
                })
                .collect();
            if matches!(it, SpecTecIter::List | SpecTecIter::Opt)
                && xes2.len() == 1
                && matches!((&b, &xes2[0]),
                    (E::Var { id }, SpecTecIterExp::Dom { x, .. }) if id == x)
            {
                let SpecTecIterExp::Dom { e, .. } = &xes2[0];
                return e.clone();
            }
            E::Iter {
                e1: Box::new(b),
                it: it.clone(),
                xes: xes2,
            }
        }
        E::Var { .. } | E::Bool { .. } | E::Num { .. } | E::Text { .. } => e.clone(),
        E::Un { op, t, e2 } => E::Un {
            op: op.clone(),
            t: t.clone(),
            e2: Box::new(collapse(e2)),
        },
        E::Bin { op, t, e1, e2 } => E::Bin {
            op: op.clone(),
            t: t.clone(),
            e1: Box::new(collapse(e1)),
            e2: Box::new(collapse(e2)),
        },
        E::Cmp { op, t, e1, e2 } => E::Cmp {
            op: op.clone(),
            t: t.clone(),
            e1: Box::new(collapse(e1)),
            e2: Box::new(collapse(e2)),
        },
        E::Idx { e1, e2 } => E::Idx {
            e1: Box::new(collapse(e1)),
            e2: Box::new(collapse(e2)),
        },
        E::Slice { e1, e2, e3 } => E::Slice {
            e1: Box::new(collapse(e1)),
            e2: Box::new(collapse(e2)),
            e3: Box::new(collapse(e3)),
        },
        E::Upd { e1, path, e2 } => E::Upd {
            e1: Box::new(collapse(e1)),
            path: path.clone(),
            e2: Box::new(collapse(e2)),
        },
        E::Ext { e1, path, e2 } => E::Ext {
            e1: Box::new(collapse(e1)),
            path: path.clone(),
            e2: Box::new(collapse(e2)),
        },
        E::Str { efs } => E::Str {
            efs: efs
                .iter()
                .map(|SpecTecExpField::Field { at, e }| SpecTecExpField::Field {
                    at: at.clone(),
                    e: collapse(e),
                })
                .collect(),
        },
        E::Dot { e1, at } => E::Dot {
            e1: Box::new(collapse(e1)),
            at: at.clone(),
        },
        E::Comp { e1, e2 } => E::Comp {
            e1: Box::new(collapse(e1)),
            e2: Box::new(collapse(e2)),
        },
        E::Mem { e1, e2 } => E::Mem {
            e1: Box::new(collapse(e1)),
            e2: Box::new(collapse(e2)),
        },
        E::Len { e1 } => E::Len {
            e1: Box::new(collapse(e1)),
        },
        E::Tup { es } => E::Tup {
            es: es.iter().map(collapse).collect(),
        },
        E::Call { x, as1 } => E::Call {
            x: x.clone(),
            as1: as1.iter().map(collapse_arg).collect(),
        },
        E::Proj { e1, i } => E::Proj {
            e1: Box::new(collapse(e1)),
            i: *i,
        },
        E::Case { op, e1 } => E::Case {
            op: op.clone(),
            e1: Box::new(collapse(e1)),
        },
        E::Uncase { e1, op } => E::Uncase {
            e1: Box::new(collapse(e1)),
            op: op.clone(),
        },
        E::Opt { eo } => E::Opt {
            eo: eo.as_ref().map(|b| Box::new(collapse(b))),
        },
        E::Unopt { e1 } => E::Unopt {
            e1: Box::new(collapse(e1)),
        },
        E::List { es } => E::List {
            es: es.iter().map(collapse).collect(),
        },
        E::Lift { e1 } => E::Lift {
            e1: Box::new(collapse(e1)),
        },
        E::Cat { e1, e2 } => E::Cat {
            e1: Box::new(collapse(e1)),
            e2: Box::new(collapse(e2)),
        },
        E::Cvt { nt1, nt2, e1 } => E::Cvt {
            nt1: nt1.clone(),
            nt2: nt2.clone(),
            e1: Box::new(collapse(e1)),
        },
    }
}

fn collapse_arg(a: &SpecTecArg) -> SpecTecArg {
    match a {
        SpecTecArg::Exp { e } => SpecTecArg::Exp { e: collapse(e) },
        other => other.clone(),
    }
}

// ============================================================================
// Helpers: children visitor, numeric-var scan, negation, disjointness
// ============================================================================

/// Visit the encoding-relevant child expressions of a node (the positions
/// [`encode::encode_exp`] keeps, plus condition-only positions).
fn visit_children(e: &SpecTecExp, f: &mut impl FnMut(&SpecTecExp)) {
    use SpecTecExp as E;
    match e {
        E::Var { .. } | E::Bool { .. } | E::Num { .. } | E::Text { .. } => {}
        E::Un { e2, .. } => f(e2),
        E::Bin { e1, e2, .. } | E::Cmp { e1, e2, .. } => {
            f(e1);
            f(e2);
        }
        E::Idx { e1, e2 }
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
        | E::Iter { e1, .. }
        | E::Proj { e1, .. }
        | E::Case { e1, .. }
        | E::Uncase { e1, .. }
        | E::Unopt { e1 }
        | E::Lift { e1 }
        | E::Cvt { e1, .. }
        | E::Sub { e1, .. } => f(e1),
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

fn is_nat_op(t: &SpecTecOpTyp) -> bool {
    matches!(t, SpecTecOpTyp::Num(SpecTecNumTyp::Nat))
}

/// Collect the metavariables used **arithmetically**: direct `Var` operands of
/// `Bin`/`Cmp`/`Un` nodes annotated `Num(Nat)` (the numeric-metavar
/// discipline's trigger set).
fn numeric_vars(e: &SpecTecExp, out: &mut BTreeSet<String>) {
    use SpecTecExp as E;
    let mark = |child: &SpecTecExp, out: &mut BTreeSet<String>| {
        if let E::Var { id } = child {
            out.insert(id.clone());
        }
    };
    match e {
        E::Bin { t, e1, e2, .. } | E::Cmp { t, e1, e2, .. } if is_nat_op(t) => {
            mark(e1, out);
            mark(e2, out);
        }
        E::Un { t, e2, .. } if is_nat_op(t) => mark(e2, out),
        _ => {}
    }
    visit_children(e, &mut |c| numeric_vars(c, out));
}

/// Exact syntactic negation of a boolean condition: comparison flipping,
/// De Morgan on the connectives, `¬` as the fallback wrapper.
fn negate(e: &SpecTecExp) -> SpecTecExp {
    use SpecTecBinOp as B;
    use SpecTecCmpOp as C;
    use SpecTecExp as E;
    let bool_t = || SpecTecOpTyp::Bool(SpecTecBoolTyp::Bool);
    match e {
        E::Bool { b } => E::Bool { b: !b },
        E::Un {
            op: SpecTecUnOp::Not,
            e2,
            ..
        } => (**e2).clone(),
        E::Cmp { op, t, e1, e2 } => {
            let flipped = match op {
                C::Eq => C::Ne,
                C::Ne => C::Eq,
                C::Lt => C::Ge,
                C::Ge => C::Lt,
                C::Gt => C::Le,
                C::Le => C::Gt,
            };
            E::Cmp {
                op: flipped,
                t: t.clone(),
                e1: e1.clone(),
                e2: e2.clone(),
            }
        }
        E::Bin {
            op: B::And,
            t,
            e1,
            e2,
        } => E::Bin {
            op: B::Or,
            t: t.clone(),
            e1: Box::new(negate(e1)),
            e2: Box::new(negate(e2)),
        },
        E::Bin {
            op: B::Or,
            t,
            e1,
            e2,
        } => E::Bin {
            op: B::And,
            t: t.clone(),
            e1: Box::new(negate(e1)),
            e2: Box::new(negate(e2)),
        },
        E::Bin {
            op: B::Impl,
            t,
            e1,
            e2,
        } => E::Bin {
            op: B::And,
            t: t.clone(),
            e1: e1.clone(),
            e2: Box::new(negate(e2)),
        },
        other => E::Un {
            op: SpecTecUnOp::Not,
            t: bool_t(),
            e2: Box::new(other.clone()),
        },
    }
}

/// A lower bound on the length of the list a (collapsed) list pattern
/// matches: literal segments count, everything else contributes 0.
fn min_list_len(e: &SpecTecExp) -> usize {
    use SpecTecExp as E;
    match e {
        E::List { es } => es.len(),
        E::Cat { e1, e2 } => min_list_len(e1) + min_list_len(e2),
        _ => 0,
    }
}

/// The leading literal elements of a (collapsed) list pattern: the elements
/// of its initial literal-`List` segments, stopping at the first non-literal
/// segment (whose alignment is unknown).
fn leading_elems(e: &SpecTecExp) -> Vec<&SpecTecExp> {
    use SpecTecExp as E;
    let mut segs = Vec::new();
    fn segments<'e>(e: &'e SpecTecExp, out: &mut Vec<&'e SpecTecExp>) {
        if let SpecTecExp::Cat { e1, e2 } = e {
            segments(e1, out);
            segments(e2, out);
        } else {
            out.push(e);
        }
    }
    segments(e, &mut segs);
    let mut out = Vec::new();
    for s in segs {
        if let E::List { es } = s {
            out.extend(es.iter());
        } else {
            break;
        }
    }
    out
}

/// Conservative pattern disjointness: `true` only when the two (collapsed)
/// patterns provably cannot match the same argument (rigid-head clash).
fn exp_disjoint(a: &SpecTecExp, b: &SpecTecExp) -> bool {
    use SpecTecExp as E;
    match (a, b) {
        (E::Case { op: o1, e1: p1 }, E::Case { op: o2, e1: p2 }) => {
            mixop_key(o1) != mixop_key(o2) || exp_disjoint(p1, p2)
        }
        // Only same-kind literal inequality is a clash: cross-kind literals
        // can denote the same value (`Nat 2` vs `Int 2`), and `Rat`/`Real`
        // carry unnormalised strings.
        (E::Num { n: n1 }, E::Num { n: n2 }) => {
            use covalence_spectec::ast::SpecTecNum as N;
            match (n1, n2) {
                (N::Nat(a), N::Nat(b)) => a != b,
                (N::Int(a), N::Int(b)) => a != b,
                _ => false,
            }
        }
        (E::Bool { b: b1 }, E::Bool { b: b2 }) => b1 != b2,
        (E::Text { t: t1 }, E::Text { t: t2 }) => t1 != t2,
        (E::Opt { eo: None }, E::Opt { eo: Some(_) }) => true,
        (E::Opt { eo: Some(_) }, E::Opt { eo: None }) => true,
        (E::Opt { eo: Some(p1) }, E::Opt { eo: Some(p2) }) => exp_disjoint(p1, p2),
        (E::List { es: a1 }, E::List { es: a2 }) => {
            a1.len() != a2.len() || a1.iter().zip(a2).any(|(x, y)| exp_disjoint(x, y))
        }
        // An exact-length list vs a concatenation with a longer literal core
        // (e.g. `[]` vs `[h] ++ t*`) cannot match the same argument.
        (E::List { es }, cat @ E::Cat { .. }) | (cat @ E::Cat { .. }, E::List { es }) => {
            min_list_len(cat) > es.len()
        }
        // Two concatenations whose *leading literal elements* clash (e.g.
        // `[CASE_A x] ++ t` vs `[CASE_B y] ++ t'`) cannot match the same
        // argument: both prefixes align from position 0.
        (E::Cat { .. }, E::Cat { .. }) => {
            let (pa, pb) = (leading_elems(a), leading_elems(b));
            pa.iter().zip(pb.iter()).any(|(x, y)| exp_disjoint(x, y))
        }
        (E::Tup { es: a1 }, E::Tup { es: a2 }) => {
            a1.len() == a2.len() && a1.iter().zip(a2).any(|(x, y)| exp_disjoint(x, y))
        }
        (E::Str { efs: a1 }, E::Str { efs: a2 }) if a1.len() == a2.len() => {
            a1.iter().zip(a2).any(|(x, y)| match (x, y) {
                (
                    SpecTecExpField::Field { at: at1, e: e1 },
                    SpecTecExpField::Field { at: at2, e: e2 },
                ) => at1 == at2 && exp_disjoint(e1, e2),
            })
        }
        // `jsizenn` is the size projection on the four rigid integer-lane
        // constructors, hence injective there.
        (E::Call { x: x1, as1: a1 }, E::Call { x: x2, as1: a2 })
            if x1 == "jsizenn" && x2 == "jsizenn" && a1.len() == 1 && a2.len() == 1 =>
        {
            matches!(
                (&a1[0], &a2[0]),
                (SpecTecArg::Exp { e: e1 }, SpecTecArg::Exp { e: e2 })
                    if exp_disjoint(e1, e2)
            )
        }
        _ => false,
    }
}

fn args_disjoint(a: &[SpecTecArg], b: &[SpecTecArg]) -> bool {
    a.len() == b.len()
        && a.iter().zip(b).any(|(x, y)| match (x, y) {
            (SpecTecArg::Exp { e: e1 }, SpecTecArg::Exp { e: e2 }) => exp_disjoint(e1, e2),
            (SpecTecArg::Def { x: x1 }, SpecTecArg::Def { x: x2 }) => x1 != x2,
            _ => false,
        })
}

// ============================================================================
// Clause-order semantics (module docs: *Clause order*)
// ============================================================================

/// Flatten a guard into its `∧`-conjuncts.
fn split_conj<'e>(e: &'e SpecTecExp, out: &mut Vec<&'e SpecTecExp>) {
    if let SpecTecExp::Bin {
        op: SpecTecBinOp::And,
        e1,
        e2,
        ..
    } = e
    {
        split_conj(e1, out);
        split_conj(e2, out);
    } else {
        out.push(e);
    }
}

/// Canonical comparison form: `Ge(a,b) → Le(b,a)`, `Gt(a,b) → Lt(b,a)`
/// (operand-swap normalisation so mirror-image guards compare equal).
fn canon_cmp(e: &SpecTecExp) -> SpecTecExp {
    use SpecTecCmpOp as C;
    if let SpecTecExp::Cmp { op, t, e1, e2 } = e {
        let (op, e1, e2) = match op {
            C::Ge => (C::Le, e2.clone(), e1.clone()),
            C::Gt => (C::Lt, e2.clone(), e1.clone()),
            other => (other.clone(), e1.clone(), e2.clone()),
        };
        return SpecTecExp::Cmp {
            op,
            t: t.clone(),
            e1,
            e2,
        };
    }
    e.clone()
}

/// Syntactic condition equivalence up to comparison canonicalisation
/// (`Ge`/`Gt` operand swaps; `Eq`/`Ne` operand symmetry).
fn cond_equiv(a: &SpecTecExp, b: &SpecTecExp) -> bool {
    use SpecTecCmpOp as C;
    use SpecTecExp as E;
    let (ca, cb) = (canon_cmp(a), canon_cmp(b));
    if ca == cb {
        return true;
    }
    match (&ca, &cb) {
        (
            E::Cmp {
                op: o1,
                t: t1,
                e1: a1,
                e2: a2,
            },
            E::Cmp {
                op: o2,
                t: t2,
                e1: b1,
                e2: b2,
            },
        ) if o1 == o2 && t1 == t2 && matches!(o1, C::Eq | C::Ne) => a1 == b2 && a2 == b1,
        _ => false,
    }
}

/// Whether two guard sets are **complementary**: some conjunct of one is the
/// exact syntactic negation of a conjunct of the other (up to
/// [`cond_equiv`]). Two identical-pattern clauses with complementary guards
/// provably cannot both apply, so no order premise is needed — the
/// `signed_`/`imin_`/`imax_` strict-dual shape. Sound only for
/// identical-pattern siblings (variables correspond by name).
fn guards_complementary(a: &[SpecTecExp], b: &[SpecTecExp]) -> bool {
    fn dnf(e: &SpecTecExp) -> Option<Vec<Vec<&SpecTecExp>>> {
        match e {
            SpecTecExp::Bin {
                op: SpecTecBinOp::And,
                e1,
                e2,
                ..
            } => {
                let (left, right) = (dnf(e1)?, dnf(e2)?);
                if left.len().saturating_mul(right.len()) > 64 {
                    return None;
                }
                Some(
                    left.into_iter()
                        .flat_map(|a| {
                            right.iter().map(move |b| {
                                let mut branch = a.clone();
                                branch.extend(b.iter().copied());
                                branch
                            })
                        })
                        .collect(),
                )
            }
            SpecTecExp::Bin {
                op: SpecTecBinOp::Or,
                e1,
                e2,
                ..
            } => {
                let (mut left, right) = (dnf(e1)?, dnf(e2)?);
                if left.len() + right.len() > 64 {
                    return None;
                }
                left.extend(right);
                Some(left)
            }
            atom => Some(vec![vec![atom]]),
        }
    }
    fn guards_dnf(gs: &[SpecTecExp]) -> Option<Vec<Vec<&SpecTecExp>>> {
        let mut out = vec![Vec::new()];
        for guard in gs {
            let branches = dnf(guard)?;
            if out.len().saturating_mul(branches.len()) > 64 {
                return None;
            }
            out = out
                .into_iter()
                .flat_map(|a| {
                    branches.iter().map(move |b| {
                        let mut branch = a.clone();
                        branch.extend(b.iter().copied());
                        branch
                    })
                })
                .collect();
        }
        Some(out)
    }

    let (Some(ca), Some(cb)) = (guards_dnf(a), guards_dnf(b)) else {
        return false;
    };
    let atoms_disjoint = |ga: &SpecTecExp, gb: &SpecTecExp| {
        if cond_equiv(&negate(ga), gb) || cond_equiv(ga, &negate(gb)) {
            return true;
        }
        // Equalities with a common side and structurally disjoint rigid
        // values cannot both hold. Alias expansion exposes this exact shape
        // for I32/I64-indexed table and memory records.
        let equality_values_disjoint = |a: &SpecTecExp, b: &SpecTecExp| {
            let (
                SpecTecExp::Cmp {
                    op: SpecTecCmpOp::Eq,
                    e1: a1,
                    e2: a2,
                    ..
                },
                SpecTecExp::Cmp {
                    op: SpecTecCmpOp::Eq,
                    e1: b1,
                    e2: b2,
                    ..
                },
            ) = (a, b)
            else {
                return false;
            };
            (a1 == b1 && exp_disjoint(a2, b2))
                || (a1 == b2 && exp_disjoint(a2, b1))
                || (a2 == b1 && exp_disjoint(a1, b2))
                || (a2 == b2 && exp_disjoint(a1, b1))
        };
        if equality_values_disjoint(ga, gb) {
            return true;
        }
        let (ga, gb) = (canon_cmp(ga), canon_cmp(gb));
        let (
            SpecTecExp::Cmp {
                op: SpecTecCmpOp::Lt,
                t: ta,
                e1: xa,
                e2: ua,
            },
            SpecTecExp::Cmp {
                op: SpecTecCmpOp::Le,
                t: tb,
                e1: lb,
                e2: xb,
            },
        ) = (&ga, &gb)
        else {
            // Try the symmetric ordering of the two atoms.
            let (
                SpecTecExp::Cmp {
                    op: SpecTecCmpOp::Le,
                    t: ta,
                    e1: la,
                    e2: xa,
                },
                SpecTecExp::Cmp {
                    op: SpecTecCmpOp::Lt,
                    t: tb,
                    e1: xb,
                    e2: ub,
                },
            ) = (&ga, &gb)
            else {
                return false;
            };
            return ta == tb
                && xa == xb
                && matches!(
                    (&**la, &**ub),
                    (
                        SpecTecExp::Num {
                            n: SpecTecNum::Nat(lower)
                        },
                        SpecTecExp::Num {
                            n: SpecTecNum::Nat(upper)
                        }
                    ) if upper <= lower
                );
        };
        ta == tb
            && xa == xb
            && matches!(
                (&**lb, &**ua),
                (
                    SpecTecExp::Num {
                        n: SpecTecNum::Nat(lower)
                    },
                    SpecTecExp::Num {
                        n: SpecTecNum::Nat(upper)
                    }
                ) if upper <= lower
            )
    };
    ca.iter().all(|ba| {
        cb.iter().all(|bb| {
            ba.iter()
                .any(|ga| bb.iter().any(|gb| atoms_disjoint(ga, gb)))
        })
    })
}

/// Contradictory call-result guards under variable equalities forced by two
/// overlapping rigid patterns.
///
/// A nonlinear earlier pattern can align one variable with two current
/// variables. On their overlap, `halfop(...)=none` and
/// `halfop(...)=some half` are contradictory even when their raw argument
/// syntax uses those different names. Only variable-to-variable alignments
/// through identical rigid structure are admitted.
fn result_guards_disjoint_under_patterns(
    prior: &[SpecTecArg],
    current: &[SpecTecArg],
    prior_guards: &[SpecTecExp],
    current_guards: &[SpecTecExp],
) -> bool {
    use super::else_::subst_vars;
    use SpecTecExp as E;

    fn align(a: &E, b: &E, pairs: &mut Vec<(String, String)>) -> bool {
        match (a, b) {
            (E::Var { id: a }, E::Var { id: b }) => {
                pairs.push((a.clone(), b.clone()));
                true
            }
            (E::Case { op: ao, e1: ae }, E::Case { op: bo, e1: be }) if ao == bo => {
                align(ae, be, pairs)
            }
            (E::Tup { es: a }, E::Tup { es: b }) | (E::List { es: a }, E::List { es: b })
                if a.len() == b.len() =>
            {
                a.iter().zip(b).all(|(a, b)| align(a, b, pairs))
            }
            _ => a == b,
        }
    }

    if prior.len() != current.len() {
        return false;
    }
    let mut pairs = Vec::new();
    for (a, b) in prior.iter().zip(current) {
        match (a, b) {
            (SpecTecArg::Exp { e: a }, SpecTecArg::Exp { e: b }) => {
                if !align(a, b, &mut pairs) {
                    return false;
                }
            }
            (a, b) if a == b => {}
            _ => return false,
        }
    }

    // Tiny deterministic union-find by class merging.
    let mut classes: Vec<BTreeSet<String>> = Vec::new();
    for (a, b) in pairs {
        let hits: Vec<usize> = classes
            .iter()
            .enumerate()
            .filter_map(|(i, c)| (c.contains(&a) || c.contains(&b)).then_some(i))
            .collect();
        let mut merged = BTreeSet::from([a, b]);
        for i in hits.into_iter().rev() {
            merged.extend(classes.remove(i));
        }
        classes.push(merged);
    }
    let mut subst = BTreeMap::new();
    for class in classes {
        let Some(rep) = class.first().cloned() else {
            continue;
        };
        for name in class {
            subst.insert(name, E::Var { id: rep.clone() });
        }
    }

    let mut pa = Vec::new();
    let mut ca = Vec::new();
    for g in prior_guards {
        split_conj(g, &mut pa);
    }
    for g in current_guards {
        split_conj(g, &mut ca);
    }
    fn call_result(e: &E) -> Option<(&E, &E)> {
        let E::Cmp {
            op: SpecTecCmpOp::Eq,
            e1,
            e2,
            ..
        } = e
        else {
            return None;
        };
        if matches!(&**e1, E::Call { .. }) {
            Some((e1, e2))
        } else if matches!(&**e2, E::Call { .. }) {
            Some((e2, e1))
        } else {
            None
        }
    }
    pa.into_iter().any(|p| {
        ca.iter().any(|c| {
            let (Some((pc, pr)), Some((cc, cr))) = (call_result(p), call_result(c)) else {
                return false;
            };
            let (Ok(pc), Ok(cc)) = (subst_vars(pc, &subst), subst_vars(cc, &subst)) else {
                return false;
            };
            pc == cc && exp_disjoint(pr, cr)
        })
    })
}

/// Project equality-defined existential witnesses out of a guard conjunction.
///
/// `∃x. x = t ∧ G(x)` is exactly `G(t)` when `x ∉ FV(t)`. SpecTec uses this
/// shape heavily for intermediate bytes/lanes. Repeating the rewrite turns
/// many apparently existential predecessor guards into ordinary conditions
/// over the current clause's pattern variables. Capture-sensitive
/// substitution refuses iterated/bound shapes rather than guessing.
pub(super) fn project_guard_witnesses(
    guards: &[SpecTecExp],
    pattern_vars: &[String],
) -> Option<Vec<SpecTecExp>> {
    use super::else_::subst_vars;
    use SpecTecExp as E;

    let mut atoms = Vec::new();
    for g in guards {
        split_conj(g, &mut atoms);
    }
    let mut atoms: Vec<SpecTecExp> = atoms.into_iter().cloned().collect();
    loop {
        let mut witness = None;
        'find: for (i, atom) in atoms.iter().enumerate() {
            let E::Cmp {
                op: SpecTecCmpOp::Eq,
                e1,
                e2,
                ..
            } = atom
            else {
                continue;
            };
            for (var, value) in [(&**e1, &**e2), (&**e2, &**e1)] {
                // A list metavariable in expression position is printed by
                // the middle-end as the identity iterator
                // `v*{v <- vs}`. It denotes `vs` itself and is therefore an
                // equality-defined witness on exactly the same footing as a
                // bare variable.
                let id = match var {
                    E::Var { id } => id,
                    E::Iter {
                        e1,
                        it: covalence_spectec::ast::SpecTecIter::List,
                        xes,
                    } if xes.len() == 1 => {
                        let E::Var { id: body } = &**e1 else {
                            continue;
                        };
                        let covalence_spectec::ast::SpecTecIterExp::Dom { x, e } = &xes[0];
                        let E::Var { id } = e else {
                            continue;
                        };
                        if body != x {
                            continue;
                        }
                        id
                    }
                    _ => continue,
                };
                if pattern_vars.contains(id) {
                    continue;
                }
                let mut value_vars = Vec::new();
                collect_metavars(value, &mut value_vars);
                if !value_vars.contains(id) {
                    witness = Some((i, id.clone(), value.clone()));
                    break 'find;
                }
            }
        }
        let Some((i, var, value)) = witness else {
            break;
        };
        atoms.remove(i);
        let mut all_vars = Vec::new();
        for atom in &atoms {
            collect_metavars(atom, &mut all_vars);
        }
        collect_metavars(&value, &mut all_vars);
        let mut map: BTreeMap<String, SpecTecExp> = all_vars
            .into_iter()
            .map(|id| (id.clone(), E::Var { id }))
            .collect();
        map.insert(var, value);
        atoms = atoms
            .iter()
            .map(|a| subst_vars(a, &map).ok())
            .collect::<Option<_>>()?;
    }

    let mut remaining = Vec::new();
    for atom in &atoms {
        collect_metavars(atom, &mut remaining);
    }
    remaining
        .iter()
        .all(|v| pattern_vars.contains(v))
        .then_some(atoms)
}

/// Negate a projected guard conjunction.
fn negate_projected_guards(guards: &[SpecTecExp], pattern_vars: &[String]) -> Option<SpecTecExp> {
    let projected = project_guard_witnesses(guards, pattern_vars)?;
    let mut it = projected.iter();
    let Some(first) = it.next() else {
        return Some(SpecTecExp::Bool { b: false });
    };
    let mut out = negate(first);
    for g in it {
        out = SpecTecExp::Bin {
            op: SpecTecBinOp::Or,
            t: SpecTecOpTyp::Bool(SpecTecBoolTyp::Bool),
            e1: Box::new(out),
            e2: Box::new(negate(g)),
        };
    }
    Some(out)
}

/// Whether firing this clause anywhere on its overlap with `prior` can only
/// re-derive facts the earlier clause derives itself: the patterns
/// correspond with one side purely more general, and the two RHSs are
/// **literally equal** under the correspondence (the `idiv_` S-`eps` legs;
/// `utf8`'s general clause is *not* caught — its RHS differs structurally).
/// `false` is always safe.
fn confluent_overlap(prior: &Earlier, cargs: &[SpecTecArg], crhs: &SpecTecExp) -> bool {
    use super::else_::{Corr, correspond, subst_vars};
    if prior.args.len() != cargs.len() {
        return false;
    }
    let mut pes = Vec::new();
    let mut oes = Vec::new();
    for (a, b) in prior.args.iter().zip(cargs) {
        match (a, b) {
            (SpecTecArg::Exp { e: ea }, SpecTecArg::Exp { e: eb }) => {
                pes.push(ea.clone());
                oes.push(eb.clone());
            }
            (x, y) if x == y => {}
            _ => return false,
        }
    }
    let pa = SpecTecExp::Tup { es: pes };
    let oa = SpecTecExp::Tup { es: oes };
    // Prior purely more general: its RHS carried onto our instances.
    if let Corr::Overlap(map) = correspond(&pa, &oa)
        && let Ok(prhs) = subst_vars(&prior.rhs, &map)
        && prhs == *crhs
    {
        return true;
    }
    // We are purely more general: our RHS restricted to prior's instances.
    if let Corr::Overlap(map) = correspond(&oa, &pa)
        && let Ok(orhs) = subst_vars(crhs, &map)
        && orhs == prior.rhs
    {
        return true;
    }
    false
}

/// Recognise the exact singleton instance of a recursive map/concatenate
/// equation.
///
/// SpecTec's `utf8` starts with
///
/// ```text
/// utf8(ch*) = concat((utf8([ch]))*{ch <- ch*})
/// ```
///
/// before its four singleton equations.  On a singleton input the first
/// equation lowers to `utf8([ch], out) ==> utf8([ch], out)`: the star family
/// produces the singleton list `[out]`, and `ev.cat([], [out], out)` is the
/// identity case.  It therefore contributes no fact to the least graph
/// relation and cannot shadow a later singleton equation.  Refuse every
/// variation of this shape rather than treating general recursive overlaps
/// as confluent.
fn recursive_map_singleton_noop(dec_name: &str, prior: &Earlier, current: &[SpecTecArg]) -> bool {
    use SpecTecExp as E;

    let (
        [
            SpecTecArg::Exp {
                e: E::Var { id: domain },
            },
        ],
        [
            SpecTecArg::Exp {
                e: E::List { es: singleton },
            },
        ],
    ) = (&prior.args[..], current)
    else {
        return false;
    };
    if singleton.len() != 1 {
        return false;
    }

    let E::Call { x, as1 } = &prior.rhs else {
        return false;
    };
    if x != "concat_" || as1.len() != 2 || !matches!(as1[0], SpecTecArg::Typ { .. }) {
        return false;
    }
    let SpecTecArg::Exp {
        e: E::Iter {
            e1,
            it: SpecTecIter::List,
            xes,
        },
    } = &as1[1]
    else {
        return false;
    };
    let [
        SpecTecIterExp::Dom {
            x: binder,
            e: E::Var { id: iter_domain },
        },
    ] = &xes[..]
    else {
        return false;
    };
    if iter_domain != domain {
        return false;
    }
    let E::Call {
        x: recursive,
        as1: recursive_args,
    } = &**e1
    else {
        return false;
    };
    matches!(
        &recursive_args[..],
        [SpecTecArg::Exp {
            e: E::List { es }
        }] if recursive == dec_name
            && matches!(&es[..], [E::Var { id }] if id == binder)
    )
}

/// What the clause-order semantics require of this clause w.r.t. ONE earlier
/// sibling (see the module docs' *Clause order* bullet).
enum OrderAction {
    /// Inject the negation of the sibling's guard conjunction as an ordinary
    /// condition (identical patterns, pure pattern-variable `If` guards).
    Negate(SpecTecExp),
    /// The complement is inexpressible: a censused opaque premise.
    Opaque(&'static str),
}

/// Exact complement of common ordered-pattern shapes:
///
/// - a rigid numeric literal followed by a numeric wildcard; and
/// `[CASE payload] ++ tail` followed by `[head] ++ tail` (and its direct
/// `CASE payload`/`head` counterpart).  The earlier pattern excludes exactly
/// one constructor tag; its payload is otherwise unconstrained, so
/// `head =/= CASE payload` lowers to the head-level `ev.neq` relation and is
/// independent of the fresh payload metavariable.
///
/// This deliberately refuses arbitrary pattern differences.  In particular,
/// two differently named variables are both wildcards, not a disequality.
fn tag_pattern_complement(prior: &SpecTecExp, current: &SpecTecExp) -> Option<SpecTecExp> {
    use SpecTecExp as E;
    if let (E::Num { n }, head @ E::Var { .. }) = (prior, current) {
        let nt = match n {
            SpecTecNum::Nat(_) => SpecTecNumTyp::Nat,
            SpecTecNum::Int(_) => SpecTecNumTyp::Int,
            SpecTecNum::Rat(_) => SpecTecNumTyp::Rat,
            SpecTecNum::Real(_) => SpecTecNumTyp::Real,
        };
        return Some(E::Cmp {
            op: SpecTecCmpOp::Ne,
            t: SpecTecOpTyp::Num(nt),
            e1: Box::new(head.clone()),
            e2: Box::new(prior.clone()),
        });
    }
    let (case, head) = match (prior, current) {
        (case @ E::Case { .. }, head @ E::Var { .. }) => (case, head),
        (
            E::Cat {
                e1: prior_prefix,
                e2: prior_tail,
            },
            E::Cat {
                e1: current_prefix,
                e2: current_tail,
            },
        ) if prior_tail == current_tail => match (&**prior_prefix, &**current_prefix) {
            (E::List { es: ps }, E::List { es: cs })
                if ps.len() == 1
                    && cs.len() == 1
                    && matches!(ps[0], E::Case { .. })
                    && matches!(cs[0], E::Var { .. }) =>
            {
                (&ps[0], &cs[0])
            }
            _ => return None,
        },
        _ => return None,
    };
    Some(E::Cmp {
        op: SpecTecCmpOp::Ne,
        // `cond_ne` is structural and does not inspect the annotation.  Bool
        // is the neutral non-numeric choice and avoids the arithmetic path.
        t: SpecTecOpTyp::Bool(SpecTecBoolTyp::Bool),
        e1: Box::new(head.clone()),
        e2: Box::new(case.clone()),
    })
}

/// Exact ordered-pattern complement when all argument positions are either
/// syntactically equal, wildcard-renamings, or one supported tag
/// discrimination.  Multiple tag discriminations are joined by `∨`, since a
/// prior tuple-pattern fails when any component fails.
fn args_tag_pattern_complement(prior: &[SpecTecArg], current: &[SpecTecArg]) -> Option<SpecTecExp> {
    if prior.len() != current.len() {
        return None;
    }
    let mut discriminants = Vec::new();
    for (p, c) in prior.iter().zip(current) {
        match (p, c) {
            (SpecTecArg::Exp { e: pe }, SpecTecArg::Exp { e: ce }) if pe == ce => {}
            (
                SpecTecArg::Exp {
                    e: SpecTecExp::Var { .. },
                },
                SpecTecArg::Exp {
                    e: SpecTecExp::Var { .. },
                },
            ) => {}
            (SpecTecArg::Exp { e: pe }, SpecTecArg::Exp { e: ce }) => {
                discriminants.push(tag_pattern_complement(pe, ce)?);
            }
            (x, y) if x == y => {}
            _ => return None,
        }
    }
    let mut ds = discriminants.into_iter();
    let mut out = ds.next()?;
    for d in ds {
        out = SpecTecExp::Bin {
            op: SpecTecBinOp::Or,
            t: SpecTecOpTyp::Bool(SpecTecBoolTyp::Bool),
            e1: Box::new(out),
            e2: Box::new(d),
        };
    }
    Some(out)
}

/// Align variables in two otherwise-identical pattern trees.
///
/// This is deliberately narrower than general unification: both sides must
/// have the same rigid/list structure and every difference must be a
/// variable rename.  The resulting prior-variable → current-variable map is
/// enough to transport an exact source-sort membership constraint.
fn align_pattern_vars(
    prior: &SpecTecExp,
    current: &SpecTecExp,
    out: &mut BTreeMap<String, String>,
) -> bool {
    use SpecTecExp as E;
    match (prior, current) {
        (E::Var { id: p }, E::Var { id: c }) => match out.get(p) {
            Some(old) => old == c,
            None => {
                out.insert(p.clone(), c.clone());
                true
            }
        },
        (E::Case { op: po, e1: pe }, E::Case { op: co, e1: ce }) if po == co => {
            align_pattern_vars(pe, ce, out)
        }
        (E::Tup { es: ps }, E::Tup { es: cs }) | (E::List { es: ps }, E::List { es: cs })
            if ps.len() == cs.len() =>
        {
            ps.iter()
                .zip(cs)
                .all(|(p, c)| align_pattern_vars(p, c, out))
        }
        (E::Cat { e1: p1, e2: p2 }, E::Cat { e1: c1, e2: c2 }) => {
            align_pattern_vars(p1, c1, out) && align_pattern_vars(p2, c2, out)
        }
        (E::Opt { eo: Some(p) }, E::Opt { eo: Some(c) }) => align_pattern_vars(p, c, out),
        (E::Opt { eo: None }, E::Opt { eo: None }) => true,
        _ => prior == current,
    }
}

/// Exact complement contributed by source-sort-constrained wildcard
/// patterns.
///
/// A source pattern variable of catalogued variant sort `S` matches exactly
/// the finite set of constructor heads in `S`.  When a later pattern has the
/// same structure modulo variable renaming, failure of the earlier pattern
/// is therefore the disjunction, over aligned variables, of “the current
/// head is not in `S`”.  Membership failure for one variable is a conjunction
/// of head-level `Ne` tests against every constructor in `S`.
///
/// The representative case payload is intentionally empty: `cond_ne` lowers
/// case disequality through `ev.neq`, whose case clauses compare constructor
/// heads only.  Payloads are irrelevant to sort membership.
fn args_sort_pattern_complement(
    prior: &Earlier,
    current: &[SpecTecArg],
    cat: &super::super::syntax::CaseCatalogue,
) -> Option<SpecTecExp> {
    use SpecTecExp as E;

    if prior.args.len() != current.len() {
        return None;
    }
    let mut aligned = BTreeMap::new();
    for (p, c) in prior.args.iter().zip(current) {
        match (p, c) {
            (SpecTecArg::Exp { e: pe }, SpecTecArg::Exp { e: ce }) => {
                if !align_pattern_vars(pe, ce, &mut aligned) {
                    return None;
                }
            }
            (p, c) if p == c => {}
            _ => return None,
        }
    }

    let ne = |var: &str, key: &str| E::Cmp {
        op: SpecTecCmpOp::Ne,
        t: SpecTecOpTyp::Bool(SpecTecBoolTyp::Bool),
        e1: Box::new(E::Var { id: var.into() }),
        e2: Box::new(super::sortguard::nullary_case(key)),
    };
    let and = |left, right| E::Bin {
        op: SpecTecBinOp::And,
        t: SpecTecOpTyp::Bool(SpecTecBoolTyp::Bool),
        e1: Box::new(left),
        e2: Box::new(right),
    };
    let or = |left, right| E::Bin {
        op: SpecTecBinOp::Or,
        t: SpecTecOpTyp::Bool(SpecTecBoolTyp::Bool),
        e1: Box::new(left),
        e2: Box::new(right),
    };

    let mut failures = Vec::new();
    for guard in &prior.sort_guards {
        if guard.kind != super::sortguard::GuardKind::Plain {
            continue;
        }
        let Some(current_var) = aligned.get(&guard.var) else {
            continue;
        };
        let cases = super::sortguard::sort_case_list(cat, &guard.sort)?;
        let mut keys = cases.into_iter().map(|(key, _)| key);
        let Some(first) = keys.next() else {
            continue;
        };
        let mut outside = ne(current_var, &first);
        for key in keys {
            outside = and(outside, ne(current_var, &key));
        }
        failures.push(outside);
    }

    let mut failures = failures.into_iter();
    let mut out = failures.next()?;
    for failure in failures {
        out = or(out, failure);
    }
    Some(out)
}

/// Negate an earlier guarded clause after transporting a purely-more-general
/// pattern onto the current one.
///
/// If `prior(p)` unifies directionally with `current(q)`, every current match
/// is a prior-pattern match under the returned substitution.  Its remaining
/// applicability condition is therefore exactly the substituted guard
/// conjunction.  This covers the real `$ordered` split-list clause without
/// pretending that arbitrary partially-overlapping patterns are comparable.
fn mapped_guard_complement(
    prior: &Earlier,
    current: &[SpecTecArg],
    pattern_vars: &[String],
) -> Option<SpecTecExp> {
    use super::else_::{Corr, correspond, subst_vars};

    if prior.args.len() != current.len() {
        return None;
    }
    let prior_exps: Vec<SpecTecExp> = prior
        .args
        .iter()
        .map(|a| match a {
            SpecTecArg::Exp { e } => Some(e.clone()),
            _ => None,
        })
        .collect::<Option<_>>()?;
    let current_exps: Vec<SpecTecExp> = current
        .iter()
        .map(|a| match a {
            SpecTecArg::Exp { e } => Some(e.clone()),
            _ => None,
        })
        .collect::<Option<_>>()?;
    let Corr::Overlap(map) = correspond(
        &SpecTecExp::Tup { es: prior_exps },
        &SpecTecExp::Tup { es: current_exps },
    ) else {
        return None;
    };
    let guards: Vec<SpecTecExp> = prior
        .guards
        .iter()
        .map(|guard| subst_vars(guard, &map).ok())
        .collect::<Option<_>>()?;
    negate_projected_guards(&guards, pattern_vars)
}

/// Whether exact `ev.sort.*` memberships make two otherwise-overlapping
/// patterns disjoint. This is deliberately limited to plain values:
/// `sort.list.*` and `sort.opt.*` always overlap at `[]` / `none`.
fn sort_patterns_disjoint(
    prior: &Earlier,
    current: &[SpecTecArg],
    current_guards: &[super::sortguard::Guard],
    cat: &super::super::syntax::CaseCatalogue,
) -> bool {
    use super::else_::{Corr, correspond};
    use super::sortguard::GuardKind;

    let exps = |args: &[SpecTecArg]| -> Option<Vec<SpecTecExp>> {
        args.iter()
            .map(|a| match a {
                SpecTecArg::Exp { e } => Some(e.clone()),
                _ => None,
            })
            .collect()
    };
    let (Some(ps), Some(cs)) = (exps(&prior.args), exps(current)) else {
        return false;
    };
    let Corr::Overlap(map) = correspond(&SpecTecExp::Tup { es: ps }, &SpecTecExp::Tup { es: cs })
    else {
        return false;
    };

    let keys = |sort: &str| {
        super::sortguard::sort_case_list(cat, sort)
            .map(|xs| xs.into_iter().map(|(key, _)| key).collect::<BTreeSet<_>>())
    };
    for pg in &prior.sort_guards {
        if pg.kind != GuardKind::Plain {
            continue;
        }
        let Some(mapped) = map.get(&pg.var) else {
            continue;
        };
        match mapped {
            SpecTecExp::Case { op, .. } => {
                let Some(pkeys) = keys(&pg.sort) else {
                    continue;
                };
                if !pkeys.contains(&mixop_key(op)) {
                    return true;
                }
            }
            SpecTecExp::Var { id } => {
                for cg in current_guards {
                    if cg.kind != GuardKind::Plain || cg.var != *id {
                        continue;
                    }
                    let (Some(pkeys), Some(ckeys)) = (keys(&pg.sort), keys(&cg.sort)) else {
                        continue;
                    };
                    if pkeys.is_disjoint(&ckeys) {
                        return true;
                    }
                }
            }
            _ => {}
        }
    }
    false
}

/// Source parameter declarations are a second exact sort channel alongside
/// `Sub`-restoration guards. They need no emitted premise when the variable
/// remains in a pinning pattern, but ordered applicability must still see
/// them: two source-typed wildcards with disjoint variant sets do not overlap
/// at any well-sorted SpecTec point.
fn declared_pattern_sorts(ps: &[SpecTecParam]) -> Vec<super::sortguard::Guard> {
    use super::sortguard::{Guard, GuardKind};
    ps.iter()
        .filter_map(|p| match p {
            SpecTecParam::Exp {
                x,
                t: SpecTecTyp::Var { x: sort, .. },
            } => Some(Guard {
                var: x.clone(),
                sort: sort.clone(),
                kind: GuardKind::Plain,
            }),
            _ => None,
        })
        .collect()
}

/// Compute the order action against one earlier sibling. `None` = provably
/// nothing needed (disjoint / complementary / confluent). `explicit_else`
/// only selects the finer census labels for source-`Else` clauses.
fn order_action(
    dec_name: &str,
    prior: &Earlier,
    cargs: &[SpecTecArg],
    crhs: &SpecTecExp,
    own_guards: &[SpecTecExp],
    pattern_vars: &[String],
    sort_guards: &[super::sortguard::Guard],
    cat: &super::super::syntax::CaseCatalogue,
    explicit_else: bool,
) -> Option<OrderAction> {
    if args_disjoint(&prior.args, cargs) || sort_patterns_disjoint(prior, cargs, sort_guards, cat) {
        return None;
    }
    let identical = prior.args == cargs;
    if identical && guards_complementary(&prior.guards, own_guards) {
        return None;
    }
    if result_guards_disjoint_under_patterns(&prior.args, cargs, &prior.guards, own_guards) {
        return None;
    }
    if confluent_overlap(prior, cargs, crhs) {
        return None;
    }
    if recursive_map_singleton_noop(dec_name, prior, cargs) {
        return None;
    }
    let label = |else_label: &'static str| -> &'static str {
        if explicit_else { else_label } else { "order" }
    };
    if !identical {
        if prior.only_if
            && !prior.guards.is_empty()
            && let Some(complement) = mapped_guard_complement(prior, cargs, pattern_vars)
        {
            return Some(OrderAction::Negate(complement));
        }
        if prior.only_if
            && prior.guards.is_empty()
            && let Some(complement) = args_tag_pattern_complement(&prior.args, cargs)
                .or_else(|| args_sort_pattern_complement(prior, cargs, cat))
        {
            return Some(OrderAction::Negate(complement));
        }
        // Discrimination by pattern; the complement is a pattern disequality
        // we cannot state yet.
        return Some(OrderAction::Opaque(label("else-pattern")));
    }
    if !prior.only_if {
        return Some(OrderAction::Opaque(label("else-nonif-guard")));
    }
    if prior.guards.is_empty() {
        return Some(OrderAction::Opaque(label("else-unguarded")));
    }
    match negate_projected_guards(&prior.guards, pattern_vars) {
        Some(neg) => Some(OrderAction::Negate(neg)),
        // General ¬∃ is not expressible as a ∀-clause premise.
        None => Some(OrderAction::Opaque(label("else-existential"))),
    }
}

/// Rewrite every `Call`'s callee / `Def`-argument name through the
/// monomorphisation environment — the **condition-side mirror** of
/// [`ClauseCx::lift`]'s resolution. Conditions go to the flattener whole
/// (it owns condition-internal calls), so an unresolved `$f_(…)` inside an
/// `If` would otherwise flatten against the nonexistent tag `fn.f_` —
/// silently underivable and uncensused. Unresolved def-param names are
/// collected for the `dec.def-param` census.
fn subst_def_calls(
    e: &SpecTecExp,
    env: &BTreeMap<String, String>,
    def_params: &BTreeSet<String>,
    unresolved: &mut BTreeSet<String>,
) -> SpecTecExp {
    use SpecTecExp as E;
    macro_rules! go {
        ($e:expr) => {
            subst_def_calls($e, env, def_params, unresolved)
        };
    }
    match e {
        E::Call { x, as1 } => {
            let callee = match env.get(x) {
                Some(r) => r.clone(),
                None => {
                    if def_params.contains(x) {
                        unresolved.insert(x.clone());
                    }
                    x.clone()
                }
            };
            E::Call {
                x: callee,
                as1: as1
                    .iter()
                    .map(|a| match a {
                        SpecTecArg::Exp { e } => SpecTecArg::Exp {
                            e: subst_def_calls(e, env, def_params, unresolved),
                        },
                        SpecTecArg::Def { x: op } => SpecTecArg::Def {
                            x: match env.get(op) {
                                Some(r) => r.clone(),
                                None => {
                                    if def_params.contains(op) {
                                        unresolved.insert(op.clone());
                                    }
                                    op.clone()
                                }
                            },
                        },
                        other => other.clone(),
                    })
                    .collect(),
            }
        }
        E::Var { .. } | E::Bool { .. } | E::Num { .. } | E::Text { .. } => e.clone(),
        E::Un { op, t, e2 } => E::Un {
            op: op.clone(),
            t: t.clone(),
            e2: Box::new(go!(e2)),
        },
        E::Bin { op, t, e1, e2 } => E::Bin {
            op: op.clone(),
            t: t.clone(),
            e1: Box::new(go!(e1)),
            e2: Box::new(go!(e2)),
        },
        E::Cmp { op, t, e1, e2 } => E::Cmp {
            op: op.clone(),
            t: t.clone(),
            e1: Box::new(go!(e1)),
            e2: Box::new(go!(e2)),
        },
        E::Idx { e1, e2 } => E::Idx {
            e1: Box::new(go!(e1)),
            e2: Box::new(go!(e2)),
        },
        E::Slice { e1, e2, e3 } => E::Slice {
            e1: Box::new(go!(e1)),
            e2: Box::new(go!(e2)),
            e3: Box::new(go!(e3)),
        },
        E::Upd { e1, path, e2 } => E::Upd {
            e1: Box::new(go!(e1)),
            path: path.clone(),
            e2: Box::new(go!(e2)),
        },
        E::Ext { e1, path, e2 } => E::Ext {
            e1: Box::new(go!(e1)),
            path: path.clone(),
            e2: Box::new(go!(e2)),
        },
        E::Str { efs } => E::Str {
            efs: efs
                .iter()
                .map(|SpecTecExpField::Field { at, e }| SpecTecExpField::Field {
                    at: at.clone(),
                    e: subst_def_calls(e, env, def_params, unresolved),
                })
                .collect(),
        },
        E::Dot { e1, at } => E::Dot {
            e1: Box::new(go!(e1)),
            at: at.clone(),
        },
        E::Comp { e1, e2 } => E::Comp {
            e1: Box::new(go!(e1)),
            e2: Box::new(go!(e2)),
        },
        E::Mem { e1, e2 } => E::Mem {
            e1: Box::new(go!(e1)),
            e2: Box::new(go!(e2)),
        },
        E::Len { e1 } => E::Len {
            e1: Box::new(go!(e1)),
        },
        E::Tup { es } => E::Tup {
            es: es.iter().map(|e| go!(e)).collect(),
        },
        E::Iter { e1, it, xes } => E::Iter {
            e1: Box::new(go!(e1)),
            it: it.clone(),
            xes: xes
                .iter()
                .map(|SpecTecIterExp::Dom { x, e }| SpecTecIterExp::Dom {
                    x: x.clone(),
                    e: subst_def_calls(e, env, def_params, unresolved),
                })
                .collect(),
        },
        E::Proj { e1, i } => E::Proj {
            e1: Box::new(go!(e1)),
            i: *i,
        },
        E::Case { op, e1 } => E::Case {
            op: op.clone(),
            e1: Box::new(go!(e1)),
        },
        E::Uncase { e1, op } => E::Uncase {
            e1: Box::new(go!(e1)),
            op: op.clone(),
        },
        E::Opt { eo } => E::Opt {
            eo: eo.as_ref().map(|b| Box::new(go!(b))),
        },
        E::Unopt { e1 } => E::Unopt {
            e1: Box::new(go!(e1)),
        },
        E::List { es } => E::List {
            es: es.iter().map(|e| go!(e)).collect(),
        },
        E::Lift { e1 } => E::Lift {
            e1: Box::new(go!(e1)),
        },
        E::Cat { e1, e2 } => E::Cat {
            e1: Box::new(go!(e1)),
            e2: Box::new(go!(e2)),
        },
        E::Cvt { nt1, nt2, e1 } => E::Cvt {
            nt1: nt1.clone(),
            nt2: nt2.clone(),
            e1: Box::new(go!(e1)),
        },
        E::Sub { t1, t2, e1 } => E::Sub {
            t1: t1.clone(),
            t2: t2.clone(),
            e1: Box::new(go!(e1)),
        },
    }
}

// ============================================================================
// Coarse-node and opaque-premise detection (term inspection)
// ============================================================================

/// Whether an encoded term contains a **collision-prone** node: a residual
/// `iter.*` head (iteration binders dropped) or an unevaluated `upd.*`/`ext.*`
/// head carrying an index/slice access path (post the `ev.upd`/`ev.ext` write
/// families, only `Slice`-path writes — `$with_mem` — still encode coarsely;
/// their index/slice sub-expressions are encoded children since R1-F2, but
/// the node itself is not a *value* encoding, so a conclusion carrying it
/// must not fire).
fn has_coarse_node(t: &Term) -> bool {
    if let Some(v) = t.as_free() {
        if let Some(rest) = v.name().strip_prefix("st$c$") {
            if rest.starts_with("iter.") {
                return true;
            }
            if (rest.starts_with("upd.") || rest.starts_with("ext."))
                && (rest.contains(".idx") || rest.contains(".slice"))
            {
                return true;
            }
        }
    }
    if let Some((f, a)) = t.as_app() {
        return has_coarse_node(f) || has_coarse_node(a);
    }
    if let Some((_, b)) = t.as_abs() {
        return has_coarse_node(b);
    }
    false
}

/// If `t` is an opaque judgement `app(st$c$rel.opaque.<reason>, body)`, return
/// the reason.
pub(super) fn opaque_reason(t: &Term) -> Option<String> {
    let (f, _body) = t.as_app()?;
    let (h, c) = f.as_app()?;
    if h.as_free()?.name() != "st$app" {
        return None;
    }
    c.as_free()?
        .name()
        .strip_prefix("st$c$rel.opaque.")
        .map(str::to_owned)
}

// ============================================================================
// Pass 2: the per-clause lowering context (lift calls/cats, encode, assemble)
// ============================================================================

struct ClauseCx<'a> {
    fl: &'a mut dyn CondFlattener,
    /// Monomorphisation environment: `Def`-param name → concrete op name.
    env: &'a BTreeMap<String, String>,
    /// `Def`-param names in scope (to detect unresolved higher-order calls).
    def_params: &'a BTreeSet<String>,
    /// Metavariables, first-seen order (the clause's quantifier order).
    mv: Vec<String>,
    /// Premises in antecedent order; the flag marks premises built *here*
    /// (subject to the numeric wrap) vs flattener-produced ones.
    prems: Vec<(LowerPrem, bool)>,
    /// `Cat` placeholder substitutions (`cat%i` → resolved spine term),
    /// applied at assembly time in record (innermost-first) order.
    subs: Vec<(String, Term)>,
    fresh: usize,
    needs_cat: bool,
    /// Structural opaque residue this clause acquired (reason strings).
    my_reasons: BTreeSet<String>,
}

impl<'a> ClauseCx<'a> {
    fn add_mv(&mut self, id: &str) {
        if !self.mv.iter().any(|s| s == id) {
            self.mv.push(id.to_owned());
        }
    }

    fn fresh_id(&mut self, prefix: &str) -> String {
        let id = format!("{prefix}%{}", self.fresh);
        self.fresh += 1;
        id
    }

    fn my_prem(&mut self, t: Term) {
        self.prems.push((LowerPrem::Judgement(t), true));
    }

    fn opaque_prem(&mut self, reason: &str, body: Term) -> Result<()> {
        self.my_reasons.insert(format!("dec.{reason}"));
        let j = opaque(&format!("dec.{reason}"), body)?;
        self.my_prem(j);
        Ok(())
    }

    /// Encode via the flattener, merging its premises and fresh metavars.
    fn fexpr(&mut self, e: &SpecTecExp) -> Result<Term> {
        let (t, flat) = self.fl.expr(e)?;
        for m in flat.new_metavars {
            self.add_mv(&m);
        }
        for p in flat.prems {
            self.prems.push((p, false));
        }
        Ok(t)
    }

    /// Encode a **result**-position expression (the RHS) via the flattener's
    /// [`CondFlattener::expr_result`] — structural operators may become
    /// `ev.*` premises (see the module docs).
    fn fexpr_result(&mut self, e: &SpecTecExp) -> Result<Term> {
        let (t, flat) = self.fl.expr_result(e)?;
        for m in flat.new_metavars {
            self.add_mv(&m);
        }
        for p in flat.prems {
            self.prems.push((p, false));
        }
        Ok(t)
    }

    /// Flatten a condition via the flattener, merging its output.
    ///
    /// `Def`-param callee names are pre-substituted through the
    /// monomorphisation environment first ([`subst_def_calls`] — the
    /// condition-side mirror of [`ClauseCx::lift`]): conditions reach the
    /// flattener whole, and its `call_fn_name` knows nothing of the active
    /// instantiation, so an unresolved `$f_(…)` would silently flatten
    /// against the nonexistent tag `fn.f_`. Unresolved def-param callees are
    /// censused as `dec.def-param` (never silent).
    fn fcond(&mut self, e: &SpecTecExp) -> Result<()> {
        let mut unresolved = BTreeSet::new();
        let e = subst_def_calls(e, self.env, self.def_params, &mut unresolved);
        for x in unresolved {
            self.opaque_prem("def-param", con(format!("defcallee.{x}")))?;
        }
        let flat = self.fl.cond(&e)?;
        for m in flat.new_metavars {
            self.add_mv(&m);
        }
        for p in flat.prems {
            self.prems.push((p, false));
        }
        Ok(())
    }

    /// The lift pass: replace every `Call` with a fresh metavar + `fn.<g>`
    /// premise (innermost first), and every `Cat` with a placeholder var whose
    /// resolved spine term (direct appends for literal-`List` segments,
    /// `ev.cat` premises otherwise) is recorded in `subs`. Registers every
    /// `Var` in encoding position as a clause metavariable. Input must be
    /// collapsed.
    fn lift(&mut self, e: &SpecTecExp) -> Result<SpecTecExp> {
        use SpecTecExp as E;
        match e {
            E::Var { id } => {
                self.add_mv(id);
                Ok(e.clone())
            }
            E::Bool { .. } | E::Num { .. } | E::Text { .. } => Ok(e.clone()),
            E::Call { x, as1 } => {
                // The callee itself may be a `Def` param (a combinator body's
                // `$f_(…)` call): resolve it through the instantiation.
                let callee = match self.env.get(x) {
                    Some(res) => res.clone(),
                    None => {
                        if self.def_params.contains(x) {
                            self.opaque_prem("def-param", con(format!("defcallee.{x}")))?;
                        }
                        x.clone()
                    }
                };
                let mut arg_terms = Vec::new();
                let mut ops: Vec<String> = Vec::new();
                for a in as1 {
                    match a {
                        SpecTecArg::Exp { e } => {
                            let r = self.lift(e)?;
                            let t = self.fexpr(&r)?;
                            arg_terms.push(t);
                        }
                        SpecTecArg::Typ { .. } => {} // dropped (see module docs)
                        SpecTecArg::Def { x: op } => {
                            if let Some(res) = self.env.get(op) {
                                ops.push(res.clone());
                            } else {
                                if self.def_params.contains(op) {
                                    // Unresolved higher-order call (an
                                    // uninstantiated combinator body).
                                    self.opaque_prem("def-param", con(format!("defarg.{op}")))?;
                                }
                                ops.push(op.clone());
                            }
                        }
                        SpecTecArg::Gram { .. } => {
                            self.opaque_prem("gram-arg", con("gramarg"))?;
                        }
                    }
                }
                // `$` is the mono-tag separator: an id containing it would
                // make the tag ambiguous (R1-F5).
                debug_assert!(
                    !callee.contains('$') && ops.iter().all(|o| !o.contains('$')),
                    "Def-arg id contains '$' (ambiguous mono tag): {callee} {ops:?}"
                );
                let tag_name = if ops.is_empty() {
                    callee
                } else {
                    format!("{callee}${}", ops.join("$"))
                };
                let r = self.fresh_id("call");
                self.add_mv(&r);
                let prem = fn_graph(&tag_name, &arg_terms, &metavar(&r))?;
                self.my_prem(prem);
                Ok(E::Var { id: r })
            }
            E::Cat { .. } => {
                // Flatten the concatenation chain into segments.
                let mut segs = Vec::new();
                fn segments<'e>(e: &'e SpecTecExp, out: &mut Vec<&'e SpecTecExp>) {
                    if let SpecTecExp::Cat { e1, e2 } = e {
                        segments(e1, out);
                        segments(e2, out);
                    } else {
                        out.push(e);
                    }
                }
                segments(e, &mut segs);
                let mut cur: Option<Term> = None;
                for seg in segs {
                    let ls = self.lift(seg)?;
                    match (&ls, cur.take()) {
                        (E::List { es }, Some(mut c)) => {
                            // Exact append: extend the running snoc spine.
                            for el in es.clone() {
                                let et = self.fexpr(&el)?;
                                c = encode::app(c, et)?;
                            }
                            cur = Some(c);
                        }
                        (_, Some(c)) => {
                            let t = self.fexpr(&ls)?;
                            let mid = self.fresh_id("cat");
                            self.add_mv(&mid);
                            self.needs_cat = true;
                            self.my_prem(ev_graph("cat", &[c, t], &metavar(&mid))?);
                            cur = Some(metavar(&mid));
                        }
                        (_, None) => cur = Some(self.fexpr(&ls)?),
                    }
                }
                let out = self.fresh_id("catout");
                // NOT a metavariable: substituted away at assembly.
                self.subs
                    .push((out.clone(), cur.expect("cat has ≥2 segments")));
                Ok(E::Var { id: out })
            }
            E::Un { op, t, e2 } => Ok(E::Un {
                op: op.clone(),
                t: t.clone(),
                e2: Box::new(self.lift(e2)?),
            }),
            E::Bin { op, t, e1, e2 } => Ok(E::Bin {
                op: op.clone(),
                t: t.clone(),
                e1: Box::new(self.lift(e1)?),
                e2: Box::new(self.lift(e2)?),
            }),
            E::Cmp { op, t, e1, e2 } => Ok(E::Cmp {
                op: op.clone(),
                t: t.clone(),
                e1: Box::new(self.lift(e1)?),
                e2: Box::new(self.lift(e2)?),
            }),
            E::Idx { e1, e2 } => Ok(E::Idx {
                e1: Box::new(self.lift(e1)?),
                e2: Box::new(self.lift(e2)?),
            }),
            E::Slice { e1, e2, e3 } => Ok(E::Slice {
                e1: Box::new(self.lift(e1)?),
                e2: Box::new(self.lift(e2)?),
                e3: Box::new(self.lift(e3)?),
            }),
            E::Upd { e1, path, e2 } => Ok(E::Upd {
                e1: Box::new(self.lift(e1)?),
                path: path.clone(),
                e2: Box::new(self.lift(e2)?),
            }),
            E::Ext { e1, path, e2 } => Ok(E::Ext {
                e1: Box::new(self.lift(e1)?),
                path: path.clone(),
                e2: Box::new(self.lift(e2)?),
            }),
            E::Str { efs } => {
                let mut out = Vec::with_capacity(efs.len());
                for SpecTecExpField::Field { at, e } in efs {
                    out.push(SpecTecExpField::Field {
                        at: at.clone(),
                        e: self.lift(e)?,
                    });
                }
                Ok(E::Str { efs: out })
            }
            E::Dot { e1, at } => Ok(E::Dot {
                e1: Box::new(self.lift(e1)?),
                at: at.clone(),
            }),
            E::Comp { e1, e2 } => Ok(E::Comp {
                e1: Box::new(self.lift(e1)?),
                e2: Box::new(self.lift(e2)?),
            }),
            E::Mem { e1, e2 } => Ok(E::Mem {
                e1: Box::new(self.lift(e1)?),
                e2: Box::new(self.lift(e2)?),
            }),
            E::Len { e1 } => Ok(E::Len {
                e1: Box::new(self.lift(e1)?),
            }),
            E::Tup { es } => Ok(E::Tup {
                es: es.iter().map(|x| self.lift(x)).collect::<Result<_>>()?,
            }),
            E::Iter { .. } => {
                // Keep the iterator and any calls in its body intact: the
                // shared flattener owns mapped iteration as one evaluator
                // relation. Lifting the body call first would erase the map
                // dependency and leave a collision-prone raw `iter.*` node
                // in the graph conclusion.
                let mut unresolved = BTreeSet::new();
                let mapped = subst_def_calls(e, self.env, self.def_params, &mut unresolved);
                for x in unresolved {
                    self.opaque_prem("def-param", con(format!("defcallee.{x}")))?;
                }
                Ok(mapped)
            }
            E::Proj { e1, i } => Ok(E::Proj {
                e1: Box::new(self.lift(e1)?),
                i: *i,
            }),
            E::Case { op, e1 } => Ok(E::Case {
                op: op.clone(),
                e1: Box::new(self.lift(e1)?),
            }),
            E::Uncase { e1, op } => Ok(E::Uncase {
                e1: Box::new(self.lift(e1)?),
                op: op.clone(),
            }),
            E::Opt { eo } => Ok(E::Opt {
                eo: match eo {
                    None => None,
                    Some(b) => Some(Box::new(self.lift(b)?)),
                },
            }),
            E::Unopt { e1 } => Ok(E::Unopt {
                e1: Box::new(self.lift(e1)?),
            }),
            E::List { es } => Ok(E::List {
                es: es.iter().map(|x| self.lift(x)).collect::<Result<_>>()?,
            }),
            E::Lift { e1 } => Ok(E::Lift {
                e1: Box::new(self.lift(e1)?),
            }),
            E::Cvt { nt1, nt2, e1 } => Ok(E::Cvt {
                nt1: nt1.clone(),
                nt2: nt2.clone(),
                e1: Box::new(self.lift(e1)?),
            }),
            E::Sub { e1, .. } => self.lift(e1), // unreachable post-collapse
        }
    }
}

/// Wrap every numeric metavariable `n` as `app(st$c$num.nat, st$v$n)` in a
/// judgement-spine term (the numeric-metavar discipline).
fn wrap_numeric(t: &Term, nums: &BTreeSet<String>) -> Result<Term> {
    let mut acc = t.clone();
    for x in nums {
        let v = Var::new(metavar_name(x), phi());
        let rep = encode::app(con("num.nat"), metavar(x))?;
        acc = subst_free(&acc, &v, &rep);
    }
    Ok(acc)
}

// ============================================================================
// Clause lowering
// ============================================================================

/// A previously-seen clause of the same Dec (for the clause-order
/// machinery — module docs, *Clause order*).
struct Earlier {
    /// Collapsed LHS args.
    args: Vec<SpecTecArg>,
    /// Collapsed `If` guards.
    guards: Vec<SpecTecExp>,
    /// Collapsed RHS (for the confluent-overlap check).
    rhs: SpecTecExp,
    /// Whether every premise of the clause was an `If` (negating only the
    /// guards is exact only in that case).
    only_if: bool,
    /// Exact source-sort membership premises attached after lowering.
    sort_guards: Vec<super::sortguard::Guard>,
}

struct LoweredClause {
    clause: Clause,
    /// Per-site star clauses defining any iterated premises of this Dec
    /// clause. Appended after the ordinary/expanded clauses of the Dec.
    aux: Vec<Clause>,
    reasons: BTreeSet<String>,
    coarse_premise: bool,
}

impl LoweredClause {
    fn clean(&self) -> bool {
        self.reasons.is_empty()
    }
    fn cond_only(&self) -> bool {
        !self.reasons.is_empty()
            && self
                .reasons
                .iter()
                .all(|r| r == "cond" || r.starts_with("cond."))
    }
}

fn lower_clause(
    tag_name: &str,
    star_site_name: &str,
    clause: &SpecTecClause,
    earlier: &[Earlier],
    dec_params: &[SpecTecParam],
    env: &BTreeMap<String, String>,
    def_params: &BTreeSet<String>,
    sort_guards: &[super::sortguard::Guard],
    cat: &super::super::syntax::CaseCatalogue,
    flattener: &mut dyn CondFlattener,
    probe: bool,
) -> Result<(LoweredClause, Earlier)> {
    let SpecTecClause::Clause { ps, as_, e, prs } = clause;
    let mut order_sorts = declared_pattern_sorts(dec_params);
    order_sorts.extend(declared_pattern_sorts(ps));
    order_sorts.extend_from_slice(sort_guards);
    order_sorts
        .sort_by(|a, b| (&a.var, &a.sort, a.kind.tag("")).cmp(&(&b.var, &b.sort, b.kind.tag(""))));
    order_sorts.dedup_by(|a, b| a.var == b.var && a.sort == b.sort && a.kind == b.kind);

    // Pass 1: collapse.
    let cargs: Vec<SpecTecArg> = as_.iter().map(collapse_arg).collect();
    let crhs = collapse(e);

    // Clause-order plan (module docs, *Clause order*): what each earlier
    // sibling requires of this clause. Computed up front so the numeric
    // pre-scan below sees the injected negations. The expansion **probe**
    // skips the implicit-order machinery for non-`Else` clauses: order
    // residue is computed on the *expanded* patterns (expansion is exactly
    // what makes sort-overlapping `Var` patterns rigidly disjoint), so
    // pre-expansion order residue must not veto expansion.
    let has_else = prs.iter().any(|p| matches!(p, SpecTecPrem::Else));
    let own_guards: Vec<SpecTecExp> = prs
        .iter()
        .filter_map(|p| match p {
            SpecTecPrem::If { e } => Some(collapse(e)),
            _ => None,
        })
        .collect();
    let mut pattern_vars = Vec::new();
    for a in &cargs {
        if let SpecTecArg::Exp { e } = a {
            collect_metavars(e, &mut pattern_vars);
        }
    }
    let order_plan: Vec<OrderAction> = if probe && !has_else {
        Vec::new()
    } else {
        earlier
            .iter()
            .filter_map(|p| {
                order_action(
                    tag_name,
                    p,
                    &cargs,
                    &crhs,
                    &own_guards,
                    &pattern_vars,
                    &order_sorts,
                    cat,
                    has_else,
                )
            })
            .collect()
    };

    // Coordinate the numeric-metavar discipline with a stateful flattener:
    // reset it and pre-scan every expression of this clause — collapsed
    // patterns, premises, RHS, plus the negated earlier-sibling guards the
    // order plan injects below, so wrapped/bare occurrences agree.
    let scan_owned: Vec<SpecTecExp> = prs
        .iter()
        .filter_map(|pr| match pr {
            SpecTecPrem::If { e } | SpecTecPrem::Rule { e, .. } => Some(collapse(e)),
            _ => None,
        })
        .chain(std::iter::once(crhs.clone()))
        .collect();
    {
        let mut scan: Vec<&SpecTecExp> = cargs
            .iter()
            .filter_map(|a| match a {
                SpecTecArg::Exp { e } => Some(e),
                _ => None,
            })
            .collect();
        scan.extend(scan_owned.iter());
        for act in &order_plan {
            if let OrderAction::Negate(neg) = act {
                scan.push(neg);
            }
        }
        flattener.begin_rule(&scan);
    }
    // Whether the flattener applies the numeric wrap itself in `expr` spines
    // (then wrapping here would double-wrap — see the wrap step below).
    let fl_wraps = flattener.wraps_numeric();

    let mut cx = ClauseCx {
        fl: flattener,
        env,
        def_params,
        mv: Vec::new(),
        prems: Vec::new(),
        subs: Vec::new(),
        fresh: 0,
        needs_cat: false,
        my_reasons: BTreeSet::new(),
    };
    let mut star_aux = Vec::new();

    // Numeric-scan inputs accumulate as we produce residues.
    let mut num_scan: Vec<SpecTecExp> = Vec::new();

    // Patterns.
    let mut arg_terms = Vec::new();
    for a in &cargs {
        match a {
            SpecTecArg::Exp { e } => {
                let r = cx.lift(e)?;
                let t = cx.fexpr(&r)?;
                num_scan.push(r);
                arg_terms.push(t);
            }
            SpecTecArg::Typ { .. } => {} // dropped (see module docs)
            SpecTecArg::Def { x } => {
                if !env.contains_key(x) && def_params.contains(x) && env.is_empty() {
                    // Uninstantiated combinator base lowering: mark once via
                    // the def-param reason (the call sites inside the body
                    // mark themselves too; this catches argument-only uses).
                    cx.opaque_prem("def-param", con(format!("defarg.{x}")))?;
                }
            }
            SpecTecArg::Gram { .. } => cx.opaque_prem("gram-arg", con("gramarg"))?,
        }
    }

    // Premises.
    for (premise_idx, pr) in prs.iter().enumerate() {
        match pr {
            SpecTecPrem::If { e } => {
                let c = collapse(e);
                num_scan.push(c.clone());
                cx.fcond(&c)?;
            }
            SpecTecPrem::Rule { x, e, .. } => {
                let c = collapse(e);
                let r = cx.lift(&c)?;
                let t = cx.fexpr(&r)?;
                num_scan.push(r);
                let j = encode::tag(x, t)?;
                cx.my_prem(j);
            }
            SpecTecPrem::Iter { .. } => {
                let site = super::star::StarSite::of_premise(
                    tag_name,
                    star_site_name,
                    premise_idx,
                    pr,
                    &cx.mv,
                )
                .expect("matched Iter premise");
                let lowered = super::star::lower_iter_premise(&site, cx.fl)?;
                for mv in lowered.new_metavars {
                    cx.add_mv(&mv);
                }
                cx.prems
                    .extend(lowered.prems.into_iter().map(|prem| (prem, false)));
                star_aux.extend(lowered.aux);
            }
            SpecTecPrem::Let { e1, e2 } => {
                // 0 occurrences in the corpus; load as opaque.
                let body = encode::encode_exp(&SpecTecExp::Tup {
                    es: vec![collapse(e1), collapse(e2)],
                })?;
                cx.opaque_prem("let-premise", body)?;
            }
            SpecTecPrem::Else => {} // consumed by the order plan above
        }
    }

    // Clause-order complements (one action per overlapping earlier sibling —
    // the `Else` semantics generalized to every clause, module docs).
    for act in &order_plan {
        match act {
            OrderAction::Negate(neg) => {
                num_scan.push(neg.clone());
                cx.fcond(neg)?;
            }
            OrderAction::Opaque(reason) => {
                cx.opaque_prem(reason, con(if has_else { "else" } else { "order" }))?;
            }
        }
    }

    // RHS — a *result* position: structural operators (accessor bodies)
    // flatten through the evaluator relations (`CondFlattener::expr_result`).
    let rrhs = cx.lift(&crhs)?;
    let rhs_term = cx.fexpr_result(&rrhs)?;
    num_scan.push(rrhs);

    // Conclusion.
    let mut concl = fn_graph(tag_name, &arg_terms, &rhs_term)?;

    // Resolve Cat placeholder substitutions (innermost-first record order;
    // later placeholders may reference earlier ones).
    let mut subs = cx.subs.clone();
    for i in 0..subs.len() {
        let (v, t) = subs[i].clone();
        let var = Var::new(metavar_name(&v), phi());
        for entry in subs.iter_mut().skip(i + 1) {
            entry.1 = subst_free(&entry.1, &var, &t);
        }
        concl = subst_free(&concl, &var, &t);
        for (p, _) in cx.prems.iter_mut() {
            match p {
                LowerPrem::Judgement(j) => *j = subst_free(j, &var, &t),
                LowerPrem::Side(s) => *s = subst_free(s, &var, &t),
            }
        }
    }

    // Numeric-metavar discipline: wrap in the conclusion and in the premises
    // built here (flattener premises are the flattener's own responsibility).
    // A flattener that wraps its own spines (`wraps_numeric`, the real
    // condition flattener) has already wrapped everything built through
    // `fexpr` — wrapping again would double-wrap, so this leg is the
    // stateless-flattener fallback only.
    if !fl_wraps {
        let mut nums = BTreeSet::new();
        for e in &num_scan {
            numeric_vars(e, &mut nums);
        }
        nums.retain(|n| cx.mv.iter().any(|m| m == n));
        if !nums.is_empty() {
            concl = wrap_numeric(&concl, &nums)?;
            for (p, mine) in cx.prems.iter_mut() {
                if *mine {
                    if let LowerPrem::Judgement(j) = p {
                        *j = wrap_numeric(j, &nums)?;
                    }
                }
            }
        }
    }

    // Coarse-spine honesty: a collision-prone conclusion must not fire.
    if has_coarse_node(&concl) {
        cx.opaque_prem("coarse-spine", con(format!("coarse.{tag_name}")))?;
    }
    let coarse_premise = cx.prems.iter().any(|(p, _)| match p {
        LowerPrem::Judgement(j) => opaque_reason(j).is_none() && has_coarse_node(j),
        LowerPrem::Side(_) => false,
    });

    // Classify residue by inspecting the final premises (both the flattener's
    // opaque escapes and our own carry `rel.opaque.<reason>` tags).
    let mut reasons = BTreeSet::new();
    for (p, _) in &cx.prems {
        if let LowerPrem::Judgement(j) = p {
            if let Some(r) = opaque_reason(j) {
                reasons.insert(r);
            }
        }
    }

    let lowered = LoweredClause {
        clause: Clause {
            metavars: cx.mv,
            prems: cx.prems.into_iter().map(|(p, _)| p).collect(),
            concl,
        },
        aux: star_aux,
        reasons,
        coarse_premise,
    };

    // Bookkeeping for later siblings' order plans.
    let only_if = prs
        .iter()
        .all(|p| matches!(p, SpecTecPrem::If { .. } | SpecTecPrem::Else));
    let earlier_entry = Earlier {
        args: cargs,
        guards: own_guards,
        rhs: crhs,
        only_if,
        sort_guards: order_sorts,
    };
    Ok((lowered, earlier_entry))
}

// ============================================================================
// Dec lowering + monomorphisation + whole-corpus census
// ============================================================================

fn dec_parts(def: &SpecTecDef) -> Option<(&str, &[SpecTecParam], &[SpecTecClause])> {
    match def {
        SpecTecDef::Dec { x, ps, clauses, .. } => Some((x, ps, clauses)),
        _ => None,
    }
}

fn collect_decs(defs: &[SpecTecDef]) -> Vec<&SpecTecDef> {
    let mut out = Vec::new();
    fn go<'a>(d: &'a SpecTecDef, out: &mut Vec<&'a SpecTecDef>) {
        match d {
            SpecTecDef::Dec { .. } => out.push(d),
            SpecTecDef::Rec { ds } => ds.iter().for_each(|x| go(x, out)),
            _ => {}
        }
    }
    defs.iter().for_each(|d| go(d, &mut out));
    out
}

fn def_param_names(
    ps: &[SpecTecParam],
    clauses: &[SpecTecClause],
) -> (Vec<String>, BTreeSet<String>) {
    let ordered: Vec<String> = ps
        .iter()
        .filter_map(|p| match p {
            SpecTecParam::Def { x, .. } => Some(x.clone()),
            _ => None,
        })
        .collect();
    let mut set: BTreeSet<String> = ordered.iter().cloned().collect();
    for c in clauses {
        let SpecTecClause::Clause { ps, .. } = c;
        for p in ps {
            if let SpecTecParam::Def { x, .. } = p {
                set.insert(x.clone());
            }
        }
    }
    (ordered, set)
}

/// Lower every clause of one Dec under a monomorphisation environment.
/// Returns the clauses, the report, and whether `ev.cat` aux clauses are
/// needed.
fn lower_dec_inner(
    name: &str,
    tag_name: &str,
    ps: &[SpecTecParam],
    clauses: &[SpecTecClause],
    env: &BTreeMap<String, String>,
    cat: &super::super::syntax::CaseCatalogue,
    flattener: &mut dyn CondFlattener,
) -> Result<(Vec<Clause>, DecReport, bool, usize)> {
    use super::sortguard;
    let (_, def_params) = def_param_names(ps, clauses);
    let mut out = Vec::with_capacity(clauses.len());
    let mut report = DecReport {
        name: name.to_owned(),
        tag: tag_name.to_owned(),
        ..DecReport::default()
    };
    let mut earlier: Vec<Earlier> = Vec::new();
    let mut needs_cat = false;
    let mut coarse_prems = 0usize;
    // On-demand sort-guard clause families (deduplicated locally too, in case
    // the flattener is a stateless one whose `request_ev` just builds).
    let mut sort_aux: Vec<Clause> = Vec::new();
    let mut sort_keys: BTreeSet<String> = BTreeSet::new();
    let mut star_aux: Vec<Clause> = Vec::new();
    for (source_idx, c) in clauses.iter().enumerate() {
        // --- Sort fix (module docs): sub-only metavariables of this source
        // clause, from the *original* (pre-collapse) expressions.
        let SpecTecClause::Clause { as_, e, prs, .. } = c;
        // Pinning positions = the LHS patterns (they survive verbatim into
        // the graph conclusion); the RHS is a *result* position (its
        // structural operators flatten into premises) and premises never pin.
        let patterns: Vec<&SpecTecExp> = as_
            .iter()
            .filter_map(|a| match a {
                SpecTecArg::Exp { e } => Some(e),
                _ => None,
            })
            .collect();
        let mut rest: Vec<&SpecTecExp> = vec![e];
        for pr in prs {
            sortguard::prem_exprs(pr, &mut rest);
        }
        let mut plan = sortguard::plan(&patterns, &rest, cat, true);
        if !plan.expansions.is_empty() {
            // Expansion is a *fireability* optimization (premise-free
            // concrete instances); a clause with opaque residue cannot fire
            // anyway, and expanding it would only duplicate that residue in
            // the census. Probe the canonical lowering: any residue => take
            // the (equally exact) guards instead.
            let probe_site = format!("dec.probe{source_idx}");
            let (probe, _) = lower_clause(
                tag_name,
                &probe_site,
                c,
                &earlier,
                ps,
                env,
                &def_params,
                &plan.guards,
                cat,
                flattener,
                true,
            )?;
            if !probe.reasons.is_empty() {
                plan = sortguard::plan(&patterns, &rest, cat, false);
            }
        }

        // Per-case expansion: the cross product over the expandable vars.
        let mut variants: Vec<SpecTecClause> = vec![c.clone()];
        for (v, keys) in &plan.expansions {
            let mut next = Vec::with_capacity(variants.len() * keys.len());
            for base in &variants {
                for k in keys {
                    next.push(sortguard::subst_clause(base, v, k));
                }
            }
            variants = next;
        }
        report.expanded += variants.len() - 1;

        // Lower each variant; aggregate source-clause-level accounting.
        report.clauses += 1;
        let mut all_clean = true;
        let mut any_structural = false;
        let mut src_reasons: BTreeSet<String> = BTreeSet::new();
        let mut src_coarse = false;
        for (variant_idx, vc) in variants.iter().enumerate() {
            // Track needs_cat via the result (lower_clause hides its cx).
            let star_site = format!("dec.clause{source_idx}.variant{variant_idx}");
            let (mut lc, e) = lower_clause(
                tag_name,
                &star_site,
                vc,
                &earlier,
                ps,
                env,
                &def_params,
                &plan.guards,
                cat,
                flattener,
                false,
            )?;
            // Attach the guard premises (a var that collapsed away entirely
            // is not a clause metavariable and constrains nothing).
            for g in &plan.guards {
                if !lc.clause.metavars.iter().any(|m| m == &g.var) {
                    continue;
                }
                for (key, cls) in sortguard::guard_families(g, cat)? {
                    let built = flattener.request_ev(&key, &|| Ok(cls.clone()))?;
                    if sort_keys.insert(key) {
                        sort_aux.extend(built);
                    }
                }
                lc.clause
                    .prems
                    .push(LowerPrem::Judgement(sortguard::guard_judgement(
                        &g.var, &g.sort, g.kind,
                    )?));
                report.sort_guards += 1;
            }
            // An unguardable sort constraint is an inexpressible premise:
            // the standard opaque hatch (0 on the bundled corpus).
            for (v, sort) in &plan.unguardable {
                let reason = "dec.sort-unguardable".to_string();
                lc.clause.prems.push(LowerPrem::Judgement(opaque(
                    &reason,
                    con(format!("sortvar.{v}.{sort}")),
                )?));
                lc.reasons.insert(reason);
            }
            if !lc.clean() {
                all_clean = false;
            }
            if !(lc.clean() || lc.cond_only()) {
                any_structural = true;
            }
            src_reasons.extend(lc.reasons.iter().cloned());
            src_coarse |= lc.coarse_premise;
            if lc.clause.prems.iter().any(|p| match p {
                LowerPrem::Judgement(j) => judgement_tag_is(j, "rel.ev.cat"),
                LowerPrem::Side(_) => false,
            }) {
                needs_cat = true;
            }
            star_aux.extend(lc.aux);
            out.push(lc.clause);
            earlier.push(e);
        }
        if all_clean {
            report.clean += 1;
        } else if !any_structural {
            report.cond_only += 1;
        } else {
            report.opaque += 1;
        }
        for r in &src_reasons {
            *report.reasons.entry(r.clone()).or_default() += 1;
        }
        if src_coarse {
            report.coarse_premises += 1;
            coarse_prems += 1;
        }
    }
    out.extend(sort_aux);
    report.iter_aux_clauses = star_aux.len();
    report.iter_sites = star_aux.len() / 2;
    super::star::assert_unique_star_tags(&star_aux);
    out.extend(star_aux);
    Ok((out, report, needs_cat, coarse_prems))
}

/// Whether a judgement term is tagged with the given relation constant
/// (`st$c$<tag>` at the head of its spine).
pub(super) fn judgement_tag_is(t: &Term, tag: &str) -> bool {
    let mut cur = t;
    loop {
        match cur.as_app() {
            Some((f, _)) => match f.as_app() {
                Some((h, c)) => {
                    if h.as_free().map(|v| v.name()) == Some("st$app")
                        && c.as_free().map(|v| v.name() == format!("st$c${tag}")) == Some(true)
                    {
                        return true;
                    }
                    cur = f;
                }
                None => return false,
            },
            None => return false,
        }
    }
}

/// Lower one `SpecTecDef::Dec` standalone: every clause becomes a [`Clause`]
/// of `fn.<name>` (plus the `ev.cat` aux pair if any clause needed it, so the
/// result is a self-contained rule set for that function and its recursion).
///
/// A higher-order Dec (with `Def` params) lowers with an **empty**
/// monomorphisation environment here — its higher-order calls acquire
/// `dec.def-param` opaque residue. Use [`spec_fn_clauses`] for the
/// call-site-driven monomorphised instances.
///
/// `cat` drives the sort fix (per-case expansion / `ev.sort.*` guards — see
/// the module docs); pass `CaseCatalogue::new(&defs)` over the whole spec so
/// the sorts a pattern references are actually catalogued.
pub fn lower_dec(
    def: &SpecTecDef,
    cat: &super::super::syntax::CaseCatalogue,
    flattener: &mut dyn CondFlattener,
) -> Result<(Vec<Clause>, DecReport)> {
    let (name, ps, clauses) = dec_parts(def).ok_or_else(|| {
        covalence_core::Error::ConnectiveRule("spectec decs: definition is not a `def`".into())
    })?;
    let env = BTreeMap::new();
    let (mut out, report, needs_cat, _) =
        lower_dec_inner(name, name, ps, clauses, &env, cat, flattener)?;
    if needs_cat {
        // Routed through the flattener seam: a pool-managing flattener
        // dedupes across the whole build (and returns `[]`); the default
        // builds the pair locally.
        out.extend(flattener.request_ev("cat", &cat_aux_clauses)?);
    }
    Ok((out, report))
}

/// All `Def`-arg call instantiations in the spec: callee → set of op-name
/// vectors. Vectors mentioning a name that is not a known Dec are counted in
/// `unresolved` and skipped (the corpus has none: every `Def` arg is a
/// constant function name, and no combinator forwards its own `Def` param).
fn collect_instantiations(
    defs: &[SpecTecDef],
    dec_names: &BTreeSet<&str>,
    unresolved: &mut usize,
) -> BTreeMap<String, BTreeSet<Vec<String>>> {
    let mut out: BTreeMap<String, BTreeSet<Vec<String>>> = BTreeMap::new();

    fn walk_exp(
        e: &SpecTecExp,
        dec_names: &BTreeSet<&str>,
        out: &mut BTreeMap<String, BTreeSet<Vec<String>>>,
        unresolved: &mut usize,
    ) {
        if let SpecTecExp::Call { x, as1 } = e {
            let ops: Vec<String> = as1
                .iter()
                .filter_map(|a| match a {
                    SpecTecArg::Def { x } => Some(x.clone()),
                    _ => None,
                })
                .collect();
            if !ops.is_empty() {
                if ops.iter().all(|o| dec_names.contains(o.as_str())) {
                    out.entry(x.clone()).or_default().insert(ops);
                } else {
                    *unresolved += 1;
                }
            }
        }
        visit_children(e, &mut |c| walk_exp(c, dec_names, out, unresolved));
    }

    fn walk_prem(
        p: &SpecTecPrem,
        dec_names: &BTreeSet<&str>,
        out: &mut BTreeMap<String, BTreeSet<Vec<String>>>,
        unresolved: &mut usize,
    ) {
        match p {
            SpecTecPrem::Rule { e, .. } | SpecTecPrem::If { e } => {
                walk_exp(e, dec_names, out, unresolved)
            }
            SpecTecPrem::Let { e1, e2 } => {
                walk_exp(e1, dec_names, out, unresolved);
                walk_exp(e2, dec_names, out, unresolved);
            }
            SpecTecPrem::Else => {}
            SpecTecPrem::Iter { pr1, .. } => walk_prem(pr1, dec_names, out, unresolved),
        }
    }

    fn walk_def(
        d: &SpecTecDef,
        dec_names: &BTreeSet<&str>,
        out: &mut BTreeMap<String, BTreeSet<Vec<String>>>,
        unresolved: &mut usize,
    ) {
        match d {
            SpecTecDef::Rel { rules, .. } => {
                for SpecTecRule::Rule { e, prs, .. } in rules {
                    walk_exp(e, dec_names, out, unresolved);
                    prs.iter()
                        .for_each(|p| walk_prem(p, dec_names, out, unresolved));
                }
            }
            SpecTecDef::Dec { clauses, .. } => {
                for SpecTecClause::Clause { as_, e, prs, .. } in clauses {
                    for a in as_ {
                        if let SpecTecArg::Exp { e } = a {
                            walk_exp(e, dec_names, out, unresolved);
                        }
                    }
                    walk_exp(e, dec_names, out, unresolved);
                    prs.iter()
                        .for_each(|p| walk_prem(p, dec_names, out, unresolved));
                }
            }
            SpecTecDef::Rec { ds } => ds
                .iter()
                .for_each(|x| walk_def(x, dec_names, out, unresolved)),
            _ => {}
        }
    }

    for d in defs {
        walk_def(d, dec_names, &mut out, unresolved);
    }
    out
}

/// Lower **every** `Dec` of a definition list into `fn.*` graph-relation
/// clauses: ordinary functions directly, higher-order combinators as
/// monomorphised `fn.<f>$<op>` instances (one per `Def`-arg instantiation
/// actually appearing in the spec), zero-clause builtins as clause-less
/// declared tags. Appends the `ev.cat` aux pair once if any clause needed it.
///
/// Loading is total: every source equation clause yields at least one emitted
/// [`Clause`] (a combinator with no call sites falls back to a base lowering
/// with `dec.def-param` opaque residue). The census reports exact buckets.
pub fn spec_fn_clauses(
    defs: &[SpecTecDef],
    flattener: &mut dyn CondFlattener,
) -> Result<(Vec<Clause>, FnCensus)> {
    let decs = collect_decs(defs);
    let dec_names: BTreeSet<&str> = decs
        .iter()
        .filter_map(|d| dec_parts(d).map(|p| p.0))
        .collect();
    let cat = super::super::syntax::CaseCatalogue::new(defs);
    let mut census = FnCensus {
        functions: decs.len(),
        ..FnCensus::default()
    };
    let insts = collect_instantiations(defs, &dec_names, &mut census.unresolved_instantiations);

    let mut clauses = Vec::new();
    let mut needs_cat = false;

    for dec in &decs {
        let Some((name, ps, cls)) = dec_parts(dec) else {
            continue;
        };
        census.spec_clauses += cls.len();
        if cls.is_empty() {
            census.builtins += 1;
            continue;
        }
        let (ordered_def_params, _) = def_param_names(ps, cls);
        // Canonical report for spec-level (per-source-clause) accounting.
        let canonical: DecReport;
        if ordered_def_params.is_empty() {
            let env = BTreeMap::new();
            let (cs, rep, nc, _) = lower_dec_inner(name, name, ps, cls, &env, &cat, flattener)?;
            needs_cat |= nc;
            census.clauses_emitted += cs.len();
            census.expanded_clauses += rep.expanded;
            census.sort_guards += rep.sort_guards;
            census.iter_sites += rep.iter_sites;
            census.iter_aux_clauses += rep.iter_aux_clauses;
            clauses.extend(cs);
            canonical = rep;
        } else {
            census.combinators += 1;
            let uses = insts.get(name).cloned().unwrap_or_default();
            let mut first: Option<DecReport> = None;
            if uses.is_empty() {
                // No call sites: base fallback so loading stays total.
                let env = BTreeMap::new();
                let (cs, rep, nc, _) = lower_dec_inner(name, name, ps, cls, &env, &cat, flattener)?;
                needs_cat |= nc;
                census.clauses_emitted += cs.len();
                census.expanded_clauses += rep.expanded;
                census.sort_guards += rep.sort_guards;
                census.iter_sites += rep.iter_sites;
                census.iter_aux_clauses += rep.iter_aux_clauses;
                clauses.extend(cs);
                first = Some(rep);
            } else {
                for ops in &uses {
                    if ops.len() != ordered_def_params.len() {
                        census.unresolved_instantiations += 1;
                        continue;
                    }
                    let env: BTreeMap<String, String> = ordered_def_params
                        .iter()
                        .cloned()
                        .zip(ops.iter().cloned())
                        .collect();
                    // `$` is the mono-tag separator (R1-F5).
                    debug_assert!(
                        !name.contains('$') && ops.iter().all(|o| !o.contains('$')),
                        "Def-arg id contains '$' (ambiguous mono tag): {name} {ops:?}"
                    );
                    let tag_name = format!("{name}${}", ops.join("$"));
                    let (cs, rep, nc, _) =
                        lower_dec_inner(name, &tag_name, ps, cls, &env, &cat, flattener)?;
                    needs_cat |= nc;
                    census.mono_instances += 1;
                    census.clauses_emitted += cs.len();
                    census.expanded_clauses += rep.expanded;
                    census.sort_guards += rep.sort_guards;
                    census.iter_sites += rep.iter_sites;
                    census.iter_aux_clauses += rep.iter_aux_clauses;
                    clauses.extend(cs);
                    if first.is_none() {
                        first = Some(rep);
                    } else {
                        census.reports.push(rep);
                    }
                }
            }
            canonical = first.expect("combinator lowered at least once");
        }
        census.spec_loaded += canonical.clauses;
        census.spec_clean += canonical.clean;
        census.spec_cond_only += canonical.cond_only;
        census.spec_opaque += canonical.opaque;
        census.coarse_premises += canonical.coarse_premises;
        if canonical.clean == canonical.clauses {
            census.fns_fully_clean += 1;
        }
        for (r, n) in &canonical.reasons {
            *census.reasons.entry(r.clone()).or_default() += n;
        }
        census.reports.push(canonical);
    }

    if needs_cat {
        // Via the flattener seam (deduplicated into a shared pool when the
        // flattener manages one — `aux_clauses` is then 0 here and the pair
        // is drained by the integration layer instead).
        let aux = flattener.request_ev("cat", &cat_aux_clauses)?;
        census.aux_clauses = aux.len();
        clauses.extend(aux);
    }
    Ok((clauses, census))
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::super::{Flattened, PureFlattener, rule_set_of};
    use super::*;
    use crate::init::ext::TermExt;
    use crate::init::nat;
    use crate::metalogic::{self, Premise, derive_mixed};
    use crate::wasm::syntax::CaseCatalogue;
    use covalence_hol_eval::EvalThm as Thm;
    use covalence_hol_eval::mk_nat;
    use covalence_spectec::ast::{MixOp, SpecTecNum, SpecTecTyp};

    fn var(id: &str) -> SpecTecExp {
        SpecTecExp::Var { id: id.into() }
    }
    fn num(n: u64) -> SpecTecExp {
        SpecTecExp::Num {
            n: SpecTecNum::Nat(n),
        }
    }
    fn mixop(s: &str) -> MixOp {
        MixOp::new(vec![s.to_string()])
    }
    fn case(tag: &str, payload: SpecTecExp) -> SpecTecExp {
        SpecTecExp::Case {
            op: mixop(tag),
            e1: Box::new(payload),
        }
    }
    fn unit() -> SpecTecExp {
        SpecTecExp::Tup { es: vec![] }
    }
    fn list(es: Vec<SpecTecExp>) -> SpecTecExp {
        SpecTecExp::List { es }
    }
    fn exp_arg(e: SpecTecExp) -> SpecTecArg {
        SpecTecArg::Exp { e }
    }
    fn nat_typ() -> SpecTecTyp {
        SpecTecTyp::Num(SpecTecNumTyp::Nat)
    }

    fn assert_genuine(thm: &Thm) {
        assert!(thm.hyps().is_empty(), "hypothesis-free");
    }

    /// Find the Dec named `name` in a definition list.
    fn find_dec<'a>(defs: &'a [SpecTecDef], name: &str) -> &'a SpecTecDef {
        collect_decs(defs)
            .into_iter()
            .find(|d| dec_parts(d).map(|p| p.0) == Some(name))
            .unwrap_or_else(|| panic!("no Dec named {name}"))
    }

    /// A test flattener implementing just enough of the real condition leg for
    /// ground discharge: nat comparisons and encoded-equality conditions as
    /// `Side` antecedents over bare metavars, nat `Bin` arithmetic in `expr`
    /// position as a fresh **wrapped** result metavar plus a `Side` equation
    /// (the numeric-metavar discipline from the flattener's side). Everything
    /// else falls back to [`PureFlattener`] behaviour.
    #[derive(Default)]
    struct ArithFlattener {
        fresh: usize,
    }

    impl ArithFlattener {
        /// A bare-`nat` operand term (numeric currency).
        fn bare(&mut self, e: &SpecTecExp) -> Option<Term> {
            match e {
                SpecTecExp::Var { id } => Some(metavar(id)),
                SpecTecExp::Num {
                    n: SpecTecNum::Nat(u),
                } => Some(mk_nat(*u)),
                _ => None,
            }
        }
    }

    impl CondFlattener for ArithFlattener {
        fn cond(&mut self, cond: &SpecTecExp) -> Result<Flattened> {
            use SpecTecCmpOp as C;
            if let SpecTecExp::Cmp { op, t, e1, e2 } = cond {
                let side = if is_nat_op(t) {
                    let (a, b) = match (self.bare(e1), self.bare(e2)) {
                        (Some(a), Some(b)) => (a, b),
                        _ => return PureFlattener.cond(cond),
                    };
                    let lt = nat::nat_lt();
                    let le = nat::nat_le();
                    match op {
                        C::Eq => a.equals(b)?,
                        C::Ne => a.equals(b)?.not()?,
                        C::Lt => lt.apply(a)?.apply(b)?,
                        C::Le => le.apply(a)?.apply(b)?,
                        C::Gt => lt.apply(b)?.apply(a)?,
                        C::Ge => le.apply(b)?.apply(a)?,
                    }
                } else {
                    // Structural (en)coding equality: exact because the
                    // encoding is injective on the compared fragment.
                    let a = encode::encode_exp(e1)?;
                    let b = encode::encode_exp(e2)?;
                    match op {
                        C::Eq => a.equals(b)?,
                        C::Ne => a.equals(b)?.not()?,
                        _ => return PureFlattener.cond(cond),
                    }
                };
                return Ok(Flattened {
                    prems: vec![LowerPrem::Side(side)],
                    new_metavars: vec![],
                });
            }
            PureFlattener.cond(cond)
        }

        fn expr(&mut self, e: &SpecTecExp) -> Result<(Term, Flattened)> {
            if let SpecTecExp::Bin { op, t, e1, e2 } = e {
                if is_nat_op(t) {
                    if let (Some(a), Some(b)) = (self.bare(e1), self.bare(e2)) {
                        let f = match op {
                            SpecTecBinOp::Add => nat::nat_add(),
                            SpecTecBinOp::Sub => nat::nat_sub(),
                            SpecTecBinOp::Mul => nat::nat_mul(),
                            _ => return PureFlattener.expr(e),
                        };
                        let s = format!("arith%{}", self.fresh);
                        self.fresh += 1;
                        let side = metavar(&s).equals(f.apply(a)?.apply(b)?)?;
                        let term = encode::app(con("num.nat"), metavar(&s))?;
                        return Ok((
                            term,
                            Flattened {
                                prems: vec![LowerPrem::Side(side)],
                                new_metavars: vec![s],
                            },
                        ));
                    }
                }
            }
            PureFlattener.expr(e)
        }
    }

    /// The encoding of a ground nat list `[n₀ … nₖ]` (the snoc spine).
    fn ground_list(ns: &[u64]) -> Term {
        encode::encode_exp(&list(ns.iter().map(|n| num(*n)).collect())).unwrap()
    }
    /// The encoding of a nat literal (`app(num.nat, ⌜n⌝)`).
    fn ground_nat(n: u64) -> Term {
        encode::encode_exp(&num(n)).unwrap()
    }

    /// Prove a closed side antecedent by kernel computation.
    fn side(t: Term) -> Premise {
        Premise::Side(t.prove_true().unwrap_or_else(|e| {
            panic!("side condition should compute: {t} ({e})");
        }))
    }

    // ------------------------------------------------------------------
    // The real spec `sum` (cons pattern + recursive call + nat arithmetic):
    // derive fn.sum([1,2], 3) bottom-up through the kernel.
    // ------------------------------------------------------------------
    #[test]
    fn real_sum_derives_ground_instance() {
        let defs = crate::wasm::spec::wasm_spec();
        let sum = find_dec(&defs, "sum");
        let mut fl = ArithFlattener::default();
        let (cls, report) = lower_dec(sum, &CaseCatalogue::new(&defs), &mut fl).unwrap();
        // 2 spec clauses + the ev.cat pair.
        assert_eq!(report.clauses, 2);
        assert_eq!(report.clean, 2, "sum lowers cleanly: {:?}", report.reasons);
        assert_eq!(cls.len(), 4);
        let rs = rule_set_of(cls.clone());
        let n = rs.n_clauses().unwrap();
        assert_eq!(n, 4);

        // Clause 1 shape: metavars [n, n'*, cat%…, call%…, arith%…]; premises
        // [ev.cat, fn.sum, Side].
        assert_eq!(cls[1].metavars.len(), 5);
        assert_eq!(cls[1].prems.len(), 3);

        let nat_e = |k: u64| ground_nat(k);
        let add = |a: Term, b: Term| nat::nat_add().apply(a).unwrap().apply(b).unwrap();

        // ev.cat indices: 2 = base, 3 = step.
        let evcat_base = |ys: Term| derive_mixed(&rs, 2, n, &[ys], vec![]).unwrap();
        // fn.sum([]) = 0 (clause 0, no metavars).
        let d_nil = derive_mixed(&rs, 0, n, &[], vec![]).unwrap();
        assert_genuine(&d_nil);
        assert_eq!(
            d_nil.concl(),
            &metalogic::derivable(
                &rs,
                &fn_graph("sum", &[ground_list(&[])], &nat_e(0)).unwrap()
            )
            .unwrap()
        );

        // fn.sum([2]) = 2: clause 1 with n:=2, n'*:=[], cat:=[2], call:=0,
        // arith:=2.
        let d2 = derive_mixed(
            &rs,
            1,
            n,
            &[
                mk_nat(2u64),
                ground_list(&[]),
                ground_list(&[2]),
                mk_nat(0u64),
                mk_nat(2u64),
            ],
            vec![
                Premise::Derivation(evcat_base(ground_list(&[2]))),
                Premise::Derivation(d_nil.clone()),
                side(
                    mk_nat(2u64)
                        .equals(add(mk_nat(2u64), mk_nat(0u64)))
                        .unwrap(),
                ),
            ],
        )
        .unwrap();
        assert_genuine(&d2);
        assert_eq!(
            d2.concl(),
            &metalogic::derivable(
                &rs,
                &fn_graph("sum", &[ground_list(&[2])], &nat_e(2)).unwrap()
            )
            .unwrap()
        );

        // ev.cat([1], [2], [1,2]) via base + step (evalrel layout: metavars
        // [%xs, %ys, %y, %r], concl cat(xs, ys·y, r·y)).
        let cat_12 = derive_mixed(
            &rs,
            3,
            n,
            &[
                ground_list(&[1]),
                ground_list(&[]),
                ground_nat(2),
                ground_list(&[1]),
            ],
            vec![Premise::Derivation(evcat_base(ground_list(&[1])))],
        )
        .unwrap();

        // fn.sum([1,2]) = 3.
        let d12 = derive_mixed(
            &rs,
            1,
            n,
            &[
                mk_nat(1u64),
                ground_list(&[2]),
                ground_list(&[1, 2]),
                mk_nat(2u64),
                mk_nat(3u64),
            ],
            vec![
                Premise::Derivation(cat_12),
                Premise::Derivation(d2),
                side(
                    mk_nat(3u64)
                        .equals(add(mk_nat(1u64), mk_nat(2u64)))
                        .unwrap(),
                ),
            ],
        )
        .unwrap();
        assert_genuine(&d12);
        assert_eq!(
            d12.concl(),
            &metalogic::derivable(
                &rs,
                &fn_graph("sum", &[ground_list(&[1, 2])], &nat_e(3)).unwrap()
            )
            .unwrap()
        );
    }

    // ------------------------------------------------------------------
    // Real spec `size` (pattern dispatch on Case): both branches derive.
    // ------------------------------------------------------------------
    #[test]
    fn real_size_pattern_dispatch_derives() {
        let defs = crate::wasm::spec::wasm_spec();
        let size = find_dec(&defs, "size");
        let mut fl = PureFlattener;
        let (cls, report) = lower_dec(size, &CaseCatalogue::new(&defs), &mut fl).unwrap();
        assert_eq!(report.clauses, 4);
        assert_eq!(report.clean, 4);
        let rs = rule_set_of(cls.clone());
        let n = rs.n_clauses().unwrap();

        // Ground Case patterns: no metavars, no premises.
        for (idx, tag, bits) in [(0usize, "I32", 32u64), (1, "I64", 64), (3, "F64", 64)] {
            assert!(cls[idx].metavars.is_empty());
            let d = derive_mixed(&rs, idx, n, &[], vec![]).unwrap();
            assert_genuine(&d);
            let expected = fn_graph(
                "size",
                &[encode::encode_exp(&case(tag, unit())).unwrap()],
                &ground_nat(bits),
            )
            .unwrap();
            assert_eq!(d.concl(), &metalogic::derivable(&rs, &expected).unwrap());
        }
    }

    // ------------------------------------------------------------------
    // Real spec `min` (Else negation): both the guarded clause and the
    // negated-Else clause derive ground instances.
    // ------------------------------------------------------------------
    #[test]
    fn real_min_else_negation_derives() {
        let defs = crate::wasm::spec::wasm_spec();
        let min = find_dec(&defs, "min");
        let mut fl = ArithFlattener::default();
        let (cls, report) = lower_dec(min, &CaseCatalogue::new(&defs), &mut fl).unwrap();
        assert_eq!(report.clauses, 2);
        assert_eq!(
            report.clean, 2,
            "min (incl. Else) lowers cleanly under the arith flattener: {:?}",
            report.reasons
        );
        let rs = rule_set_of(cls.clone());
        let n = rs.n_clauses().unwrap();
        let le = |a: u64, b: u64| {
            nat::nat_le()
                .apply(mk_nat(a))
                .unwrap()
                .apply(mk_nat(b))
                .unwrap()
        };
        let lt = |a: u64, b: u64| {
            nat::nat_lt()
                .apply(mk_nat(a))
                .unwrap()
                .apply(mk_nat(b))
                .unwrap()
        };

        // min(3, 5) = 3 via clause 0 (guard 3 ≤ 5).
        let d0 = derive_mixed(
            &rs,
            0,
            n,
            &[mk_nat(3u64), mk_nat(5u64)],
            vec![side(le(3, 5))],
        )
        .unwrap();
        assert_genuine(&d0);
        assert_eq!(
            d0.concl(),
            &metalogic::derivable(
                &rs,
                &fn_graph("min", &[ground_nat(3), ground_nat(5)], &ground_nat(3)).unwrap()
            )
            .unwrap()
        );

        // min(5, 3) = 3 via clause 1 (Else ⇒ ¬(5 ≤ 3) ⇒ 3 < 5).
        let d1 = derive_mixed(
            &rs,
            1,
            n,
            &[mk_nat(5u64), mk_nat(3u64)],
            vec![side(lt(3, 5))],
        )
        .unwrap();
        assert_genuine(&d1);
        assert_eq!(
            d1.concl(),
            &metalogic::derivable(
                &rs,
                &fn_graph("min", &[ground_nat(5), ground_nat(3)], &ground_nat(3)).unwrap()
            )
            .unwrap()
        );
    }

    #[test]
    fn real_dec_iterated_premises_have_live_empty_stars() {
        use super::super::flatten::Flattener;
        use super::super::star::star_judgement;

        let defs = crate::wasm::spec::wasm_spec();
        let cat = CaseCatalogue::new(&defs);
        let ride = encode::app(con("case.I32"), con("tuple")).unwrap();

        // growmem's optional `j?` guard: absence is the vacuous star case.
        let mut fl = Flattener::new(&cat);
        let (mut growmem, report) = lower_dec(find_dec(&defs, "growmem"), &cat, &mut fl).unwrap();
        growmem.extend(fl.drain_ev_clauses());
        assert!(
            !report.reasons.contains_key("dec.iter-premise"),
            "{report:?}"
        );
        let grow_tag = "star.growmem.dec.clause0.variant0.3";
        let grow_idx = growmem
            .iter()
            .position(|c| {
                c.prems.is_empty() && judgement_tag_is(&c.concl, &format!("rel.{grow_tag}"))
            })
            .expect("growmem optional-star base clause");
        assert_eq!(growmem[grow_idx].metavars.len(), 1);
        let rs = rule_set_of(growmem.clone());
        let n = rs.n_clauses().unwrap();
        let d = derive_mixed(&rs, grow_idx, n, &[ride.clone()], vec![]).unwrap();
        assert_genuine(&d);
        assert_eq!(
            d.concl(),
            &metalogic::derivable(
                &rs,
                &star_judgement(grow_tag, &[ride.clone(), con("opt.none")]).unwrap()
            )
            .unwrap()
        );

        // instantiate's zipped Externaddr_ok iteration: two empty domains
        // satisfy the premise without manufacturing an element judgement.
        let mut fl = Flattener::new(&cat);
        let (mut instantiate, report) =
            lower_dec(find_dec(&defs, "instantiate"), &cat, &mut fl).unwrap();
        instantiate.extend(fl.drain_ev_clauses());
        assert!(
            !report.reasons.contains_key("dec.iter-premise"),
            "{report:?}"
        );
        let inst_tag = "star.instantiate.dec.clause0.variant0.1";
        let inst_idx = instantiate
            .iter()
            .position(|c| {
                c.prems.is_empty() && judgement_tag_is(&c.concl, &format!("rel.{inst_tag}"))
            })
            .expect("instantiate zipped-star base clause");
        assert_eq!(instantiate[inst_idx].metavars.len(), 1);
        let rs = rule_set_of(instantiate.clone());
        let n = rs.n_clauses().unwrap();
        let d = derive_mixed(&rs, inst_idx, n, &[ride.clone()], vec![]).unwrap();
        assert_genuine(&d);
        assert_eq!(
            d.concl(),
            &metalogic::derivable(
                &rs,
                &star_judgement(inst_tag, &[ride, con("list"), con("list")]).unwrap()
            )
            .unwrap()
        );
    }

    #[test]
    fn real_subst_moduletype_empty_maps_derive() {
        use super::super::flatten::Flattener;
        let defs = crate::wasm::spec::wasm_spec();
        let cat = CaseCatalogue::new(&defs);
        let mut fl = Flattener::new(&cat);
        let (mut cls, report) =
            lower_dec(find_dec(&defs, "subst_moduletype"), &cat, &mut fl).unwrap();
        assert_eq!(report.clean, 1, "{report:?}");
        assert!(!report.reasons.contains_key("dec.coarse-spine"));
        cls.extend(fl.drain_ev_clauses());
        assert_eq!(cls.len(), 5, "one graph clause + two 2-clause maps");

        let rs = rule_set_of(cls);
        let n = rs.n_clauses().unwrap();
        let nil = con("list");
        let map_left = derive_mixed(&rs, 1, n, &[nil.clone(), nil.clone()], vec![]).unwrap();
        let map_right = derive_mixed(&rs, 3, n, &[nil.clone(), nil.clone()], vec![]).unwrap();
        let d = derive_mixed(
            &rs,
            0,
            n,
            &[
                nil.clone(),
                nil.clone(),
                nil.clone(),
                nil.clone(),
                nil.clone(),
                nil.clone(),
            ],
            vec![
                Premise::Derivation(map_left),
                Premise::Derivation(map_right),
            ],
        )
        .unwrap();
        assert_genuine(&d);
        let pair = encode::app(
            con("case.%->%"),
            encode::app(encode::app(con("tup"), nil.clone()).unwrap(), nil.clone()).unwrap(),
        )
        .unwrap();
        let expected =
            fn_graph("subst_moduletype", &[pair.clone(), nil.clone(), nil], &pair).unwrap();
        assert_eq!(
            d.concl(),
            &metalogic::derivable(&rs, &expected).unwrap(),
            "both empty mapped substitutions preserve the empty module type"
        );
    }

    // ------------------------------------------------------------------
    // R4-F1 regression: Dec clauses match IN ORDER. The truncating `idiv_`
    // legs overlap the earlier `eps` legs at real instances (U: i_2 = 0)
    // with divergent RHSs, masked today only by their dead `fn.truncz`
    // builtin premise — filling the builtin frontier must never create
    // false facts (monotonic growth). The lowered trunc legs must carry a
    // non-vacuous order/complement premise; the eps legs stay live.
    // ------------------------------------------------------------------
    #[test]
    fn idiv_truncating_legs_carry_order_complements() {
        let defs = crate::wasm::spec::wasm_spec();
        let idiv = find_dec(&defs, "idiv_");
        let mut fl = PureFlattener;
        let (cls, report) = lower_dec(idiv, &CaseCatalogue::new(&defs), &mut fl).unwrap();
        assert_eq!(report.clauses, 5);
        // Both divergent overlaps are now expressible as ordinary pattern
        // conditions. PureFlattener labels all conditions `cond`; the third
        // is the source guard already present in this definition.
        assert_eq!(report.reasons.get("dec.order"), None, "{report:?}");
        assert_eq!(report.reasons.get("cond"), Some(&3), "{report:?}");

        let has_order = |c: &Clause| {
            c.prems.iter().any(|p| match p {
                LowerPrem::Judgement(j) => opaque_reason(j).as_deref() == Some("cond"),
                LowerPrem::Side(_) => false,
            })
        };
        // Clause 1 (U-trunc) overlaps clause 0 (U eps at i_2 = 0) with a
        // divergent RHS; clause 4 (S-trunc) overlaps clause 2 the same way.
        assert!(has_order(&cls[1]), "U-trunc leg carries its complement");
        assert!(has_order(&cls[4]), "S-trunc leg carries its complement");
        // Eps legs stay live: idiv_(32, U, 7, (0)) = eps derives
        // premise-free through clause 0.
        assert_eq!(cls[0].metavars.len(), 2); // [N, i_1]
        assert!(cls[0].prems.is_empty());
        let rs = rule_set_of(cls.clone());
        let n = rs.n_clauses().unwrap();
        let wrapped_zero = SpecTecExp::Case {
            op: MixOp::new(vec![String::new(), String::new()]),
            e1: Box::new(SpecTecExp::Tup { es: vec![num(0)] }),
        };
        let u = encode::encode_exp(&case("U", unit())).unwrap();
        let zero_enc = encode::encode_exp(&wrapped_zero).unwrap();
        let eps = encode::encode_exp(&SpecTecExp::Opt { eo: None }).unwrap();
        let d = derive_mixed(&rs, 0, n, &[ground_nat(32), ground_nat(7)], vec![]).unwrap();
        assert_genuine(&d);
        let expected =
            fn_graph("idiv_", &[ground_nat(32), u, ground_nat(7), zero_enc], &eps).unwrap();
        assert_eq!(d.concl(), &metalogic::derivable(&rs, &expected).unwrap());
    }

    #[test]
    fn real_idiv_signed_quotient_guard_is_fully_exact() {
        use super::super::flatten::Flattener;

        let defs = crate::wasm::spec::wasm_spec();
        let cat = CaseCatalogue::new(&defs);
        let mut fl = Flattener::new(&cat);
        let (cls, report) = lower_dec(find_dec(&defs, "idiv_"), &cat, &mut fl).unwrap();

        assert_eq!(report.clauses, 5);
        assert_eq!(report.clean, 5, "{report:?}");
        assert_eq!(report.cond_only, 0, "{report:?}");
        assert_eq!(report.reasons.get("cond.coarse-eq"), None, "{report:?}");

        let ev = fl.drain_ev_clauses();
        assert!(
            ev.iter()
                .filter(|c| judgement_tag_is(&c.concl, "rel.ev.signed-div-eq-pos-nat"))
                .count()
                == 2,
            "the real signed idiv guard requests both exact same-sign clauses"
        );
        let rs = rule_set_of(cls.into_iter().chain(ev).collect());
        assert!(rs.n_clauses().unwrap() > 5);
    }

    // ------------------------------------------------------------------
    // Real spec `setminus1_` (Typ param + cons pattern + encoded-equality
    // guard): derive setminus1_(A, [A]) = [] with a refl side theorem.
    // ------------------------------------------------------------------
    #[test]
    fn real_setminus1_derives_with_encoding_equality() {
        let defs = crate::wasm::spec::wasm_spec();
        let sm = find_dec(&defs, "setminus1_");
        let mut fl = ArithFlattener::default();
        let (cls, report) = lower_dec(sm, &CaseCatalogue::new(&defs), &mut fl).unwrap();
        assert_eq!(report.clauses, 3);
        let rs = rule_set_of(cls.clone());
        let n = rs.n_clauses().unwrap();

        let a = encode::encode_exp(&case("A", unit())).unwrap();
        let a_list = {
            // ⌜[A]⌝ — snoc spine with one element.
            encode::app(con("list"), a.clone()).unwrap()
        };
        // Clause 1: setminus1_(w, [w_1] ++ w'*) = [] -- if w = w_1.
        // metavars [w, w_1, w'*, cat-mid]; premises [ev.cat, Side(w = w_1)].
        assert_eq!(cls[1].prems.len(), 2);
        // ev.cat([A], [], [A]) — the base clause (index 3).
        let evcat = derive_mixed(&rs, 3, n, &[a_list.clone()], vec![]).unwrap();
        let refl = Thm::refl(a.clone()).unwrap();
        let d = derive_mixed(
            &rs,
            1,
            n,
            &[a.clone(), a.clone(), ground_list(&[]), a_list.clone()],
            vec![Premise::Derivation(evcat), Premise::Side(refl)],
        )
        .unwrap();
        assert_genuine(&d);
        assert_eq!(
            d.concl(),
            &metalogic::derivable(
                &rs,
                &fn_graph("setminus1_", &[a, a_list], &ground_list(&[])).unwrap()
            )
            .unwrap()
        );
    }

    // ------------------------------------------------------------------
    // Toy monomorphised higher-order instance: app1_(f_, x) = $f_(x) applied
    // to g, end-to-end through spec_fn_clauses.
    // ------------------------------------------------------------------
    #[test]
    fn monomorphised_combinator_instance_derives() {
        // def $g(x) = W(x)
        let g = SpecTecDef::Dec {
            x: "g".into(),
            ps: vec![SpecTecParam::Exp {
                x: "x".into(),
                t: nat_typ(),
            }],
            t: nat_typ(),
            clauses: vec![SpecTecClause::Clause {
                ps: vec![],
                as_: vec![exp_arg(var("x"))],
                e: case("W", var("x")),
                prs: vec![],
            }],
        };
        // def $app1_(f_, x) = $f_(x)   (higher-order combinator)
        let app1 = SpecTecDef::Dec {
            x: "app1_".into(),
            ps: vec![
                SpecTecParam::Def {
                    x: "f_".into(),
                    ps: vec![],
                    t: nat_typ(),
                },
                SpecTecParam::Exp {
                    x: "x".into(),
                    t: nat_typ(),
                },
            ],
            t: nat_typ(),
            clauses: vec![SpecTecClause::Clause {
                ps: vec![],
                as_: vec![SpecTecArg::Def { x: "f_".into() }, exp_arg(var("x"))],
                e: SpecTecExp::Call {
                    x: "f_".into(),
                    as1: vec![exp_arg(var("x"))],
                },
                prs: vec![],
            }],
        };
        // def $h(x) = $app1_($g, x)   (the constant-op call site)
        let h = SpecTecDef::Dec {
            x: "h".into(),
            ps: vec![SpecTecParam::Exp {
                x: "x".into(),
                t: nat_typ(),
            }],
            t: nat_typ(),
            clauses: vec![SpecTecClause::Clause {
                ps: vec![],
                as_: vec![exp_arg(var("x"))],
                e: SpecTecExp::Call {
                    x: "app1_".into(),
                    as1: vec![SpecTecArg::Def { x: "g".into() }, exp_arg(var("x"))],
                },
                prs: vec![],
            }],
        };

        let defs = vec![g, app1, h];
        let mut fl = PureFlattener;
        let (cls, census) = spec_fn_clauses(&defs, &mut fl).unwrap();
        assert_eq!(census.functions, 3);
        assert_eq!(census.combinators, 1);
        assert_eq!(census.mono_instances, 1);
        assert_eq!(census.spec_loaded, census.spec_clauses);
        assert_eq!(cls.len(), 3); // fn.g, fn.app1_$g, fn.h

        let rs = rule_set_of(cls.clone());
        let n = rs.n_clauses().unwrap();
        // Locate clauses by conclusion tag.
        let idx_of = |tag: &str| {
            cls.iter()
                .position(|c| judgement_tag_is(&c.concl, &format!("rel.fn.{tag}")))
                .unwrap_or_else(|| panic!("no clause tagged fn.{tag}"))
        };
        let (ig, iapp, ih) = (idx_of("g"), idx_of("app1_$g"), idx_of("h"));

        let a = encode::encode_exp(&case("A", unit())).unwrap();
        let wa = encode::encode_exp(&case("W", case("A", unit()))).unwrap();

        // fn.g(A) = W(A).
        let dg = derive_mixed(&rs, ig, n, &[a.clone()], vec![]).unwrap();
        // fn.app1_$g(A) = W(A) via the fn.g premise.
        let dapp = derive_mixed(
            &rs,
            iapp,
            n,
            &[a.clone(), wa.clone()],
            vec![Premise::Derivation(dg)],
        )
        .unwrap();
        assert_eq!(
            dapp.concl(),
            &metalogic::derivable(&rs, &fn_graph("app1_$g", &[a.clone()], &wa).unwrap()).unwrap()
        );
        // fn.h(A) = W(A) via the monomorphised premise.
        let dh = derive_mixed(
            &rs,
            ih,
            n,
            &[a.clone(), wa.clone()],
            vec![Premise::Derivation(dapp)],
        )
        .unwrap();
        assert_genuine(&dh);
        assert_eq!(
            dh.concl(),
            &metalogic::derivable(&rs, &fn_graph("h", &[a], &wa).unwrap()).unwrap()
        );
    }

    // ------------------------------------------------------------------
    // Wave-D sort-fix regression: `$default_(Inn)` per-case expands, so the
    // false fact `fn.default_(F32, CONST F32 0)` is refused (NO clause
    // conclusion even matches it), while `fn.default_(I32, CONST I32 0)`
    // fires premise-free through its expanded ground clause.
    // ------------------------------------------------------------------
    #[test]
    fn default_expansion_refuses_wrong_sort() {
        use covalence_core::Term;

        /// First-order match of a clause conclusion (metavars `st$v$…` are
        /// consistently-bound wildcards) against a ground target.
        fn matches(pat: &Term, tgt: &Term, binds: &mut BTreeMap<String, Term>) -> bool {
            if let Some(v) = pat.as_free()
                && let Some(name) = v.name().strip_prefix("st$v$")
            {
                if let Some(b) = binds.get(name) {
                    return b == tgt;
                }
                binds.insert(name.to_owned(), tgt.clone());
                return true;
            }
            match (pat.as_app(), tgt.as_app()) {
                (Some((f1, a1)), Some((f2, a2))) => {
                    matches(f1, f2, binds) && matches(a1, a2, binds)
                }
                _ => pat == tgt,
            }
        }

        let defs = crate::wasm::spec::wasm_spec();
        let dec = find_dec(&defs, "default_");
        let cat = CaseCatalogue::new(&defs);
        let mut fl = PureFlattener;
        let (cls, report) = lower_dec(dec, &cat, &mut fl).unwrap();
        assert!(report.expanded >= 2, "default_ expands: {report:?}");

        // `default_(t) = ?(CONST t (0))` at a concrete numtype `t` — the
        // shape of the spec's `Inn` clause RHS at a concrete case.
        let point = |tag: &str| {
            let t = case(tag, unit());
            let wrapped_zero = SpecTecExp::Case {
                op: MixOp::new(vec![String::new(), String::new()]),
                e1: Box::new(SpecTecExp::Tup { es: vec![num(0)] }),
            };
            let konst = SpecTecExp::Case {
                op: mixop("CONST"),
                e1: Box::new(SpecTecExp::Tup {
                    es: vec![t.clone(), wrapped_zero],
                }),
            };
            let rhs = SpecTecExp::Opt {
                eo: Some(Box::new(konst)),
            };
            fn_graph(
                "default_",
                &[encode::encode_exp(&t).unwrap()],
                &encode::encode_exp(&rhs).unwrap(),
            )
            .unwrap()
        };

        // The conclusion's relation tag (`st$c$rel.<tag>` at the spine head).
        fn tag_of(t: &Term) -> Option<String> {
            let mut cur = t;
            loop {
                let (f, _) = cur.as_app()?;
                if let Some((h, c)) = f.as_app()
                    && h.as_free().map(|v| v.name()) == Some("st$app")
                    && let Some(v) = c.as_free()
                    && let Some(tag) = v.name().strip_prefix("st$c$rel.")
                {
                    return Some(tag.to_owned());
                }
                cur = f;
            }
        }

        // The good point anchors the encoding shape: exactly one clause
        // concludes it — ground and premise-free — and it derives.
        let good = point("I32");
        let good_idx: Vec<usize> = cls
            .iter()
            .enumerate()
            .filter(|(_, c)| matches(&c.concl, &good, &mut BTreeMap::new()))
            .map(|(i, _)| i)
            .collect();
        assert_eq!(good_idx.len(), 1, "one clause concludes the I32 point");
        let idx = good_idx[0];
        assert!(cls[idx].metavars.is_empty() && cls[idx].prems.is_empty());
        let rs = rule_set_of(cls.clone());
        let n = rs.n_clauses().unwrap();
        let d = derive_mixed(&rs, idx, n, &[], vec![]).unwrap();
        assert_genuine(&d);
        assert_eq!(d.concl(), &metalogic::derivable(&rs, &good).unwrap());

        // The bad point is REFUSED. Pre-fix, the ∀-open `Inn` clause derived
        // it premise-free; post-expansion, any derivation would have to end
        // with a clause whose conclusion matches the point — and every such
        // clause (the `Fnn` clause, whose `CONST F32 _` payload is an open
        // call result) requires a premise of a relation with NO clauses in
        // the set (`fn.fzero`, a zero-clause builtin): underivable.
        let bad = point("F32");
        let concl_tags: BTreeSet<String> = cls.iter().filter_map(|c| tag_of(&c.concl)).collect();
        let mut matching = 0usize;
        for (i, c) in cls.iter().enumerate() {
            if !matches(&c.concl, &bad, &mut BTreeMap::new()) {
                continue;
            }
            matching += 1;
            assert!(
                !c.prems.is_empty(),
                "clause {i} would derive the bad point premise-free: {}",
                c.concl
            );
            assert!(
                c.prems.iter().any(|p| match p {
                    LowerPrem::Judgement(j) => tag_of(j).is_some_and(|t| !concl_tags.contains(&t)),
                    LowerPrem::Side(_) => false,
                }),
                "clause {i} matching the bad point must hit an underivable premise"
            );
        }
        assert!(matching <= 1, "at most the Fnn clause matches");
    }

    // ------------------------------------------------------------------
    // Whole-spec census: total loading + floors + exact buckets.
    // ------------------------------------------------------------------
    #[test]
    fn utf8_recursive_map_predecessor_is_an_exact_singleton_noop() {
        use super::super::flatten::Flattener;
        let defs = crate::wasm::spec::wasm_spec();
        let cat = CaseCatalogue::new(&defs);
        let mut fl = Flattener::new(&cat);
        let (_, census) = spec_fn_clauses(&defs, &mut fl).unwrap();
        let utf8 = census
            .reports
            .iter()
            .find(|report| report.name == "utf8" && report.tag == "utf8")
            .expect("bundled utf8 Dec");

        assert_eq!(utf8.clauses, 5);
        assert_eq!(utf8.clean, 5, "{utf8:?}");
        assert_eq!(utf8.opaque, 0, "{utf8:?}");
        assert_eq!(utf8.reasons.get("dec.order"), None, "{utf8:?}");
    }

    #[test]
    fn ordered_alias_expansions_leave_only_the_existential_vcvtop_frontier() {
        use super::super::flatten::Flattener;
        let defs = crate::wasm::spec::wasm_spec();
        let cat = CaseCatalogue::new(&defs);
        let mut fl = Flattener::new(&cat);
        let (_, census) = spec_fn_clauses(&defs, &mut fl).unwrap();
        let report = |name: &str| {
            census
                .reports
                .iter()
                .find(|report| report.name == name && report.tag == name)
                .unwrap_or_else(|| panic!("bundled {name} Dec"))
        };

        for name in ["growtable", "growmem", "vextternop__"] {
            let report = report(name);
            assert_eq!(report.opaque, 0, "{report:?}");
            assert_eq!(report.reasons.get("dec.order"), None, "{report:?}");
        }
        let vcvtop = report("vcvtop__");
        assert_eq!(vcvtop.clean, 2, "{vcvtop:?}");
        assert_eq!(vcvtop.opaque, 1, "{vcvtop:?}");
        assert_eq!(vcvtop.reasons.get("dec.order"), Some(&1), "{vcvtop:?}");
    }

    #[test]
    fn final_dec_opacity_sites_pin_their_exact_source_capabilities() {
        let defs = crate::wasm::spec::wasm_spec();
        let find = |name: &str| {
            collect_decs(&defs)
                .into_iter()
                .find(|def| dec_parts(def).is_some_and(|(x, _, _)| x == name))
                .unwrap_or_else(|| panic!("bundled {name} Dec"))
        };

        let (_, _, vcvtop) = dec_parts(find("vcvtop__")).unwrap();
        assert_eq!(vcvtop.len(), 3);
        for (index, clause) in vcvtop.iter().enumerate() {
            let SpecTecClause::Clause { prs, .. } = clause;
            assert_eq!(prs.len(), 4, "vcvtop__ clause {index} applicability");
            assert!(
                prs.iter()
                    .all(|prem| matches!(prem, SpecTecPrem::If { .. })),
                "vcvtop__ clause {index} keeps its four source applicability equations"
            );
        }
        // The final clause can overlap each earlier clause and therefore
        // needs the complement of their existentially witnessed
        // applicability, not merely a flipped arithmetic guard.
        let (_, _, not_immut) = dec_parts(find("NotImmutReachable")).unwrap();
        assert_eq!(not_immut.len(), 2);
        let SpecTecClause::Clause {
            e: first_rhs,
            prs: first_prems,
            ..
        } = &not_immut[0];
        assert!(matches!(first_rhs, SpecTecExp::Bool { b: false }));
        assert!(matches!(
            first_prems.as_slice(),
            [SpecTecPrem::Rule { x, .. }] if x == "ImmutReachable"
        ));
        let SpecTecClause::Clause {
            e: fallback_rhs,
            prs: fallback_prems,
            ..
        } = &not_immut[1];
        assert!(matches!(fallback_rhs, SpecTecExp::Bool { b: true }));
        assert!(matches!(fallback_prems.as_slice(), [SpecTecPrem::Else]));
    }

    #[test]
    fn whole_spec_census() {
        use super::super::flatten::Flattener;
        let defs = crate::wasm::spec::wasm_spec();
        let cat = CaseCatalogue::new(&defs);
        let mut fl = Flattener::new(&cat);
        let (mut cls, census) = spec_fn_clauses(&defs, &mut fl).unwrap();
        // The real flattener pools evaluator clauses; drain them so the
        // kernel check below sees the whole (standalone) set.
        let ev = fl.drain_ev_clauses();
        let n_ev = ev.len();
        println!("evaluator clauses (pooled): {n_ev}");
        cls.extend(ev);

        println!(
            "functions: {} ({} builtins, {} combinators, {} mono instances, {} unresolved)",
            census.functions,
            census.builtins,
            census.combinators,
            census.mono_instances,
            census.unresolved_instantiations
        );
        println!(
            "spec clauses: {} (loaded {}, clean {}, cond-only {}, opaque {})",
            census.spec_clauses,
            census.spec_loaded,
            census.spec_clean,
            census.spec_cond_only,
            census.spec_opaque
        );
        println!(
            "emitted clauses: {} (+{} evaluator aux; {} Dec-star sites / {} clauses); fns fully clean: {}; coarse premises: {}",
            census.clauses_emitted,
            census.aux_clauses,
            census.iter_sites,
            census.iter_aux_clauses,
            census.fns_fully_clean,
            census.coarse_premises
        );
        println!("--- opaque reasons (canonical lowerings) ---");
        for (r, c) in &census.reasons {
            println!("  {c:>4}  {r}");
        }
        println!("--- opaque functions (canonical lowerings) ---");
        for report in census.reports.iter().filter(|report| report.opaque != 0) {
            println!(
                "  {} [{}]: {}/{} opaque {:?}",
                report.name, report.tag, report.opaque, report.clauses, report.reasons
            );
        }
        // Corpus shape (from the taxonomy; a dep bump that changes these
        // should fail loudly).
        assert_eq!(census.functions, 462);
        assert_eq!(census.spec_clauses, 804);
        assert_eq!(census.builtins, 91);
        assert_eq!(census.combinators, 16);
        assert_eq!(census.unresolved_instantiations, 0);
        assert_eq!(census.iter_sites, 6);
        assert_eq!(census.iter_aux_clauses, 12);

        // LOADING IS TOTAL: every source equation clause is represented.
        assert_eq!(census.spec_loaded, census.spec_clauses);

        // Every emitted clause builds a well-typed HOL clause term.
        let rs = rule_set_of(cls.clone());
        let n = rs.n_clauses().unwrap();
        assert_eq!(n, census.clauses_emitted + census.aux_clauses + n_ev);

        // Floors (raise as coverage grows; measured 2026-07-19 post exact
        // source-sort, mapped-guard, rigid-record and call-result
        // complements under the real condition flattener: clean 802. The
        // one remaining `dec.order` clause is vcvtop__'s genuinely
        // existential predecessor complement. Current cond-only residue:
        // condition-only residue is zero: `idiv_`'s signed rational quotient
        // equality is an exact evaluator relation. Structural: coarse-spine
        // 0, else-pattern 0, else-nonif-guard 1; fns fully clean 369. All Dec
        // Iter premises use shared star relations (6 expanded
        // sites / 12 defining clauses), with no iter-premise opacity.
        assert!(census.spec_clean >= 802, "clean = {}", census.spec_clean);
        assert_eq!(
            census.spec_cond_only, 0,
            "cond-only = {}",
            census.spec_cond_only
        );
        assert_eq!(
            census.reasons.get("cond.coarse-eq"),
            None,
            "all bundled Dec equality conversions are exact"
        );
        assert!(
            census.spec_clean + census.spec_cond_only >= 690,
            "clean+cond-only = {}",
            census.spec_clean + census.spec_cond_only
        );
        assert!(
            census.fns_fully_clean >= 369,
            "fns fully clean = {}",
            census.fns_fully_clean
        );
        assert_eq!(
            census.reasons.get("dec.else-pattern"),
            None,
            "all bundled Else pattern complements are exact"
        );
        assert!(
            census.mono_instances >= 50,
            "mono instances = {}",
            census.mono_instances
        );
        // The clause-order machinery is live: the may-overlap frontier is
        // censused, never silent (a collapse to 0 would mean divergent-RHS
        // overlaps — idiv_'s truncating legs — fire unguarded again).
        let order = census.reasons.get("dec.order").copied().unwrap_or(0);
        assert_eq!(order, 1, "dec.order clauses = {order}");

        // R4-F2: no premise may mention a `Def`-param name as (part of) a
        // graph tag — a `fn.f_` premise would be silently underivable and
        // uncensused. Def-param names, minus real Dec names.
        let dec_names: BTreeSet<&str> = collect_decs(&defs)
            .iter()
            .filter_map(|d| dec_parts(d).map(|p| p.0))
            .collect();
        let mut param_names: BTreeSet<String> = BTreeSet::new();
        for d in collect_decs(&defs) {
            if let Some((_, ps, cs)) = dec_parts(d) {
                let (_, set) = def_param_names(ps, cs);
                param_names.extend(set);
            }
        }
        param_names.retain(|p| !dec_names.contains(p.as_str()));
        assert!(!param_names.is_empty(), "corpus has Def params");
        for c in &cls {
            for p in &c.prems {
                let LowerPrem::Judgement(j) = p else { continue };
                let Some(tag) = concl_rel_tag(j) else {
                    continue;
                };
                let Some(fn_name) = tag.strip_prefix("fn.") else {
                    continue;
                };
                for seg in fn_name.split('$') {
                    assert!(
                        !param_names.contains(seg),
                        "unresolved Def-param name in premise tag fn.{fn_name}"
                    );
                }
            }
        }
    }

    /// The relation tag of a judgement term (`st$c$rel.<tag>` at the spine
    /// head), for premise scans.
    fn concl_rel_tag(t: &covalence_core::Term) -> Option<String> {
        let mut cur = t;
        loop {
            let (f, _) = cur.as_app()?;
            if let Some((h, c)) = f.as_app()
                && h.as_free().map(|v| v.name()) == Some("st$app")
                && let Some(v) = c.as_free()
                && let Some(tag) = v.name().strip_prefix("st$c$rel.")
            {
                return Some(tag.to_owned());
            }
            cur = f;
        }
    }

    // ------------------------------------------------------------------
    // Unit: identity-iteration collapse and Sub stripping.
    // ------------------------------------------------------------------
    #[test]
    fn collapse_identity_iter_and_sub() {
        // (x* with x ← xs) collapses to xs; Sub is stripped.
        let it = SpecTecExp::Iter {
            e1: Box::new(var("x")),
            it: SpecTecIter::List,
            xes: vec![SpecTecIterExp::Dom {
                x: "x".into(),
                e: var("xs"),
            }],
        };
        assert_eq!(collapse(&it), var("xs"));
        let sub = SpecTecExp::Sub {
            t1: nat_typ(),
            t2: nat_typ(),
            e1: Box::new(it),
        };
        assert_eq!(collapse(&sub), var("xs"));
        // Nested: (x* with x ← xs)* with xs ← xss collapses to xss.
        let nested = SpecTecExp::Iter {
            e1: Box::new(SpecTecExp::Iter {
                e1: Box::new(var("x")),
                it: SpecTecIter::List,
                xes: vec![SpecTecIterExp::Dom {
                    x: "x".into(),
                    e: var("xs"),
                }],
            }),
            it: SpecTecIter::List,
            xes: vec![SpecTecIterExp::Dom {
                x: "xs".into(),
                e: var("xss"),
            }],
        };
        assert_eq!(collapse(&nested), var("xss"));
        // ListN does NOT collapse (length constraint).
        let listn = SpecTecExp::Iter {
            e1: Box::new(var("x")),
            it: SpecTecIter::ListN {
                e: vec![var("n")],
                xo: vec![],
            },
            xes: vec![SpecTecIterExp::Dom {
                x: "x".into(),
                e: var("xs"),
            }],
        };
        assert!(matches!(collapse(&listn), SpecTecExp::Iter { .. }));
    }

    // ------------------------------------------------------------------
    // Unit: negation flips comparisons and De Morgans connectives.
    // ------------------------------------------------------------------
    #[test]
    fn negation_is_syntactically_exact() {
        use SpecTecCmpOp as C;
        let cmp = |op: C| SpecTecExp::Cmp {
            op,
            t: SpecTecOpTyp::Num(SpecTecNumTyp::Nat),
            e1: Box::new(var("i")),
            e2: Box::new(var("j")),
        };
        assert_eq!(
            negate(&cmp(C::Le)),
            SpecTecExp::Cmp {
                op: C::Gt,
                t: SpecTecOpTyp::Num(SpecTecNumTyp::Nat),
                e1: Box::new(var("i")),
                e2: Box::new(var("j")),
            }
        );
        let conj = SpecTecExp::Bin {
            op: SpecTecBinOp::And,
            t: SpecTecOpTyp::Bool(SpecTecBoolTyp::Bool),
            e1: Box::new(cmp(C::Eq)),
            e2: Box::new(cmp(C::Lt)),
        };
        let neg = negate(&conj);
        let SpecTecExp::Bin {
            op: SpecTecBinOp::Or,
            e1,
            e2,
            ..
        } = neg
        else {
            panic!("expected Or");
        };
        assert!(matches!(*e1, SpecTecExp::Cmp { op: C::Ne, .. }));
        assert!(matches!(*e2, SpecTecExp::Cmp { op: C::Ge, .. }));
        // Double negation via Not-stripping.
        let not = SpecTecExp::Un {
            op: SpecTecUnOp::Not,
            t: SpecTecOpTyp::Bool(SpecTecBoolTyp::Bool),
            e2: Box::new(cmp(C::Eq)),
        };
        assert_eq!(negate(&not), cmp(C::Eq));
    }

    #[test]
    fn ordered_guard_projects_equality_witnesses_before_negation() {
        let eq = |a: SpecTecExp, b: SpecTecExp| SpecTecExp::Cmp {
            op: SpecTecCmpOp::Eq,
            t: SpecTecOpTyp::Num(SpecTecNumTyp::Nat),
            e1: Box::new(a),
            e2: Box::new(b),
        };
        // ∃y. y = 3 ∧ x = y  iff  x = 3.
        let neg = negate_projected_guards(
            &[eq(var("y"), num(3)), eq(var("x"), var("y"))],
            &["x".into()],
        )
        .expect("equality witness is projectable");
        assert_eq!(
            neg,
            SpecTecExp::Cmp {
                op: SpecTecCmpOp::Ne,
                t: SpecTecOpTyp::Num(SpecTecNumTyp::Nat),
                e1: Box::new(var("x")),
                e2: Box::new(num(3)),
            }
        );

        // ∃y. y = x is always true, so its ordered complement is false.
        assert_eq!(
            negate_projected_guards(&[eq(var("y"), var("x"))], &["x".into()]),
            Some(SpecTecExp::Bool { b: false })
        );

        // The middle-end's identity-list rendering is an equally valid
        // existential witness: ∃ys. y*{y <- ys} = xs is always true.
        let identity_list = SpecTecExp::Iter {
            e1: Box::new(var("y")),
            it: SpecTecIter::List,
            xes: vec![SpecTecIterExp::Dom {
                x: "y".into(),
                e: var("ys"),
            }],
        };
        assert_eq!(
            negate_projected_guards(&[eq(identity_list, var("xs"))], &["xs".into()]),
            Some(SpecTecExp::Bool { b: false })
        );

        // A genuinely unconstrained existential relation remains explicit.
        let opaque = SpecTecExp::Call {
            x: "p".into(),
            as1: vec![exp_arg(var("y"))],
        };
        assert!(negate_projected_guards(&[opaque], &["x".into()]).is_none());
    }

    #[test]
    fn ordered_tag_pattern_has_an_exact_structural_complement() {
        let prior = SpecTecExp::Cat {
            e1: Box::new(SpecTecExp::List {
                es: vec![case("FUNC", var("payload"))],
            }),
            e2: Box::new(var("tail")),
        };
        let current = SpecTecExp::Cat {
            e1: Box::new(SpecTecExp::List {
                es: vec![var("head")],
            }),
            e2: Box::new(var("tail")),
        };
        let complement =
            tag_pattern_complement(&prior, &current).expect("head tag is discriminable");
        assert!(matches!(
            complement,
            SpecTecExp::Cmp {
                op: SpecTecCmpOp::Ne,
                e1,
                e2,
                ..
            } if *e1 == var("head") && *e2 == case("FUNC", var("payload"))
        ));
        assert!(
            tag_pattern_complement(&var("earlier_wildcard"), &var("current_wildcard")).is_none(),
            "renamed wildcards overlap everywhere and have no complement"
        );
    }

    #[test]
    fn ordered_numeric_literal_has_an_exact_complement() {
        let prior = SpecTecExp::Num {
            n: SpecTecNum::Nat(8),
        };
        let current = var("n");
        assert!(matches!(
            tag_pattern_complement(&prior, &current),
            Some(SpecTecExp::Cmp {
                op: SpecTecCmpOp::Ne,
                t: SpecTecOpTyp::Num(SpecTecNumTyp::Nat),
                e1,
                e2,
            }) if *e1 == current && *e2 == prior
        ));
    }

    #[test]
    fn ordered_patterns_use_exact_source_sort_disjointness() {
        use super::super::sortguard::GuardKind;

        let defs = crate::wasm::spec::wasm_spec();
        let cat = CaseCatalogue::new(&defs);
        let declared = declared_pattern_sorts(&[SpecTecParam::Exp {
            x: "valtype".into(),
            t: SpecTecTyp::Var {
                x: "valtype".into(),
                as1: vec![],
            },
        }]);
        assert_eq!(declared.len(), 1);
        assert_eq!(declared[0].kind, GuardKind::Plain);
        let prior = Earlier {
            args: vec![exp_arg(var("valtype"))],
            guards: vec![],
            rhs: var("r"),
            only_if: true,
            sort_guards: declared,
        };
        assert!(
            sort_patterns_disjoint(&prior, &[exp_arg(case("I8", unit()))], &[], &cat,),
            "I8 is outside valtype, so the guarded wildcard cannot overlap it"
        );
        assert!(
            !sort_patterns_disjoint(&prior, &[exp_arg(case("I32", unit()))], &[], &cat,),
            "I32 is a valtype and must remain overlapping"
        );
    }

    #[test]
    fn ordered_source_sort_wildcards_have_an_exact_finite_complement() {
        use super::super::sortguard::{Guard, GuardKind};

        let defs = crate::wasm::spec::wasm_spec();
        let cat = CaseCatalogue::new(&defs);
        let prior = Earlier {
            args: vec![exp_arg(SpecTecExp::Cat {
                e1: Box::new(SpecTecExp::List {
                    es: vec![var("type")],
                }),
                e2: Box::new(var("tail")),
            })],
            guards: vec![],
            rhs: var("r"),
            only_if: true,
            sort_guards: vec![Guard {
                var: "type".into(),
                sort: "type".into(),
                kind: GuardKind::Plain,
            }],
        };
        let current = vec![exp_arg(SpecTecExp::Cat {
            e1: Box::new(SpecTecExp::List {
                es: vec![var("decl")],
            }),
            e2: Box::new(var("tail")),
        })];
        let complement = args_sort_pattern_complement(&prior, &current, &cat)
            .expect("catalogued source sort has an exact head complement");

        fn ne_heads(e: &SpecTecExp, out: &mut Vec<String>) {
            match e {
                SpecTecExp::Bin {
                    op: SpecTecBinOp::And,
                    e1,
                    e2,
                    ..
                } => {
                    ne_heads(e1, out);
                    ne_heads(e2, out);
                }
                SpecTecExp::Cmp {
                    op: SpecTecCmpOp::Ne,
                    e1,
                    e2,
                    ..
                } => {
                    assert_eq!(**e1, var("decl"));
                    let SpecTecExp::Case { op, .. } = &**e2 else {
                        panic!("sort complement compares against a case head")
                    };
                    out.push(mixop_key(op));
                }
                other => panic!("unexpected sort complement node: {other:?}"),
            }
        }
        let mut actual = Vec::new();
        ne_heads(&complement, &mut actual);
        let expected: Vec<String> = super::super::sortguard::sort_case_list(&cat, "type")
            .unwrap()
            .into_iter()
            .map(|(key, _)| key)
            .collect();
        assert_eq!(actual, expected);

        let structurally_different = vec![exp_arg(SpecTecExp::List {
            es: vec![var("decl")],
        })];
        assert!(
            args_sort_pattern_complement(&prior, &structurally_different, &cat).is_none(),
            "sort evidence must not bridge a different list pattern"
        );
    }

    #[test]
    fn ordered_more_general_pattern_transports_its_guard_before_negation() {
        let prior_arg = var("all");
        let current_arg = SpecTecExp::Cat {
            e1: Box::new(var("prefix")),
            e2: Box::new(SpecTecExp::List {
                es: vec![var("import")],
            }),
        };
        let prior_call = SpecTecExp::Call {
            x: "importsd".into(),
            as1: vec![exp_arg(prior_arg.clone())],
        };
        let prior = Earlier {
            args: vec![exp_arg(prior_arg)],
            guards: vec![SpecTecExp::Cmp {
                op: SpecTecCmpOp::Eq,
                t: SpecTecOpTyp::Bool(SpecTecBoolTyp::Bool),
                e1: Box::new(prior_call),
                e2: Box::new(SpecTecExp::List { es: vec![] }),
            }],
            rhs: var("r"),
            only_if: true,
            sort_guards: vec![],
        };
        let complement = mapped_guard_complement(
            &prior,
            &[exp_arg(current_arg.clone())],
            &["prefix".into(), "import".into()],
        )
        .expect("a purely-more-general pattern guard transports exactly");
        let SpecTecExp::Cmp {
            op: SpecTecCmpOp::Ne,
            e1,
            e2,
            ..
        } = complement
        else {
            panic!("guard equality negates to disequality")
        };
        assert_eq!(*e2, (SpecTecExp::List { es: vec![] }));
        assert!(matches!(
            &*e1,
            SpecTecExp::Call { x, as1 }
                if x == "importsd" && as1 == &vec![exp_arg(current_arg)]
        ));
    }

    // ------------------------------------------------------------------
    // Unit: builtins load as clause-less tags; ev.cat only appended on use.
    // ------------------------------------------------------------------
    #[test]
    fn builtin_and_aux_bookkeeping() {
        let builtin = SpecTecDef::Dec {
            x: "iadd_".into(),
            ps: vec![],
            t: nat_typ(),
            clauses: vec![],
        };
        let plain = SpecTecDef::Dec {
            x: "id".into(),
            ps: vec![SpecTecParam::Exp {
                x: "x".into(),
                t: nat_typ(),
            }],
            t: nat_typ(),
            clauses: vec![SpecTecClause::Clause {
                ps: vec![],
                as_: vec![exp_arg(var("x"))],
                e: var("x"),
                prs: vec![],
            }],
        };
        let mut fl = PureFlattener;
        let (cls, census) = spec_fn_clauses(&[builtin, plain], &mut fl).unwrap();
        assert_eq!(census.builtins, 1);
        assert_eq!(census.spec_clauses, 1);
        assert_eq!(census.aux_clauses, 0, "no Cat use ⇒ no ev.cat clauses");
        assert_eq!(cls.len(), 1);
    }
}
