//! **Iterated premises** — per-site auxiliary *star relations* over the
//! encoder's snoc spines (`⌜[e₀…eₙ]⌝ = app(⌜[e₀…eₙ₋₁]⌝, ⌜eₙ⌝)`, base
//! `st$c$list` — exactly [`encode_exp`] on `SpecTecExp::List`). See
//! `notes/vibes/logics/spectec-total-load.md` §Iterated premises.
//!
//! A SpecTec premise `(P(x…))*` (a [`SpecTecPrem::Iter`]) lowers to
//!
//! 1. a **judgement premise** for the enclosing relation-rule or Dec clause — a
//!    `star.<rel>.<rule>.<idx>`-tagged judgement over the iteration-domain
//!    metavariables (built by [`star_judgement`], arity-marked like
//!    [`super::fn_graph`]); plus
//! 2. **auxiliary clauses** defining that star relation (data [`Clause`]s the
//!    integration layer appends to the combined rule set):
//!
//!    - `List`, k iteration vars → a k-ary **zip-star**: a nil clause
//!      `star(c…, nil, …, nil)` and a snoc clause
//!      `P(x…) ⟹ star(c…, xs…) ⟹ star(c…, app(xs,x)…)`;
//!    - `Opt` → two clauses: `star(c…, opt.none…)` (trivial) and
//!      `P(x…) ⟹ star(c…, app(opt.some, x)…)`;
//!    - `ListN` → a real-nat **indexed star**: base `istar(c…, nil…, ⌜0⌝)` and
//!      step `j = S i ⟹ P(x…, i) ⟹ istar(c…, xs…, i) ⟹
//!      istar(c…, app(xs,x)…, j)` with the enclosing premise instance
//!      `istar(c…, l…, bound)`.
//!
//! ## Design decisions (load-bearing, kept in sync with the tests)
//!
//! - **Ride-through metavariables become star-relation *arguments*** (the `c…`
//!   above): an enclosing-clause metavar the inner premise mentions but the site does not
//!   iterate is passed through the star judgement, *not* re-quantified per
//!   element. The alternative (aux-clause-only metavars) would let each list
//!   element pick a *different* instantiation of the context — strictly weaker
//!   than the SpecTec premise, violating the never-over-approximate frame.
//!   With arguments, `all_elim` instantiation of the enclosing rule pins the
//!   context once, and the aux clauses thread it unchanged. Argument order is
//!   `[rides…, iteration states…, index?]`, rides in first-seen order of the
//!   inner premise expression.
//! - **The `ListN` index obeys the numeric-metavar discipline** (`encode.rs`
//!   module docs): in judgement spines — the star's index argument and every
//!   occurrence inside the inner premise's judgements — the index metavar `i`
//!   appears *wrapped* as `app(st$c$num.nat, st$v$i)`; in the arithmetic
//!   `Side` antecedent it is *bare*. Instantiation currency is the bare
//!   kernel numeral, which lands `encode(Num k)` in every spine and a closed,
//!   kernel-reducible side condition simultaneously.
//! - **Successor via a `Side` equation, not a spine successor**: kernel
//!   numerals are literal leaves, so `S ⌜k⌝` and `⌜k+1⌝` are *distinct terms*
//!   and a conclusion `istar(…, S i)` could never chain syntactically. The
//!   step clause instead binds two numeric metavars `i, j` with the antecedent
//!   `j = S i` — closed at instantiation (`⌜k+1⌝ = S ⌜k⌝`) and discharged by
//!   computation ([`prove_true`](crate::init::ext::TermExt::prove_true) via
//!   the kernel `SuccCert`).
//! - **`ListN` bounds**: a plain `Var` bound `n` is used directly
//!   (numeric-wrapped, currency = bare numeral). Any other bound (the 13
//!   `|l|` sites) is bound to a **fresh numeric metavar** `b` constrained by
//!   the synthesized condition `b = <bound>` routed through the
//!   [`CondFlattener`] — an `ev.len`-style premise under the real flattener,
//!   [`opaque`] under [`PureFlattener`](super::PureFlattener) (loads, cannot
//!   fire). We prefer this over a bespoke length premise so *all* condition
//!   machinery lives behind the one flattener seam.
//! - **`ListN` with iteration vars consumes list state *and* counts**: the
//!   step appends one element per domain and increments the index in
//!   lockstep, so `istar(l…, n)` additionally asserts `|l| = n` — implied by
//!   SpecTec elaboration, so never weaker; this avoids flattening `l[i]`
//!   element access altogether.
//! - **Inner premises** flatten through the shared seam: a `Rule` premise's
//!   expression goes through [`CondFlattener::expr`] (pure encoding under
//!   `PureFlattener`), an `If` premise through [`CondFlattener::cond`]
//!   ([`opaque`] under `PureFlattener` — the site loads, the condition
//!   antecedent is underivable until the real flattener lands). Premise kinds
//!   that cannot occur under `Iter` in this corpus (`Else`/`Let`/nested
//!   `Iter`) load as a whole-site [`opaque`] premise — reported, never
//!   dropped.
//!
//! Element metavariables are instantiated with **full encodings** (never bare
//! numerals): the snoc spine appends the bare leaf `st$v$x`, so a numeral
//! element must arrive as `encode(Num k)`. A future flattener emitting bare
//! arithmetic `Side`s over *element* vars would break this currency — route
//! element arithmetic through `ev.*` premises instead (see the census note).

use covalence_core::subst::subst_free;
use covalence_core::{Result, Term, Var};
use covalence_hol_eval::mk_nat;
use covalence_spectec::ast::{
    SpecTecCmpOp, SpecTecExp, SpecTecIter, SpecTecIterExp, SpecTecNumTyp, SpecTecOpTyp, SpecTecPrem,
};

use super::super::encode::{self, app, collect_metavars, con, metavar, metavar_name, phi, tag};
use super::flatten::children;
use super::{Clause, CondFlattener, Flattened, LowerPrem, opaque};
use crate::init::ext::TermExt;

// ============================================================================
// The site currency
// ============================================================================

/// One `Iter` premise site of a spec relation rule or Dec clause — everything
/// [`lower_iter_premise`] needs to synthesize its star relation.
#[derive(Debug)]
pub struct StarSite<'a> {
    /// The enclosing relation/function's name (tag component).
    pub rel_name: &'a str,
    /// The enclosing rule or Dec-clause site name (tag component).
    pub rule_name: &'a str,
    /// The premise's index within the rule (tag component — disambiguates
    /// multiple `Iter` premises of one rule).
    pub premise_idx: usize,
    /// The iterated inner premise.
    pub pr1: &'a SpecTecPrem,
    /// The iterator kind (`List` / `Opt` / `ListN` / `List1`).
    pub it: &'a SpecTecIter,
    /// The iteration bindings (`Dom { x, e }`: element var `x` drawn from
    /// domain expression `e` — a plain `Var` throughout the corpus).
    pub xes: &'a [SpecTecIterExp],
    /// The enclosing rule's metavariables collected *so far* (raw SpecTec
    /// ids); names in [`LoweredIter::new_metavars`] are fresh w.r.t. these.
    pub rule_metavars: &'a [String],
}

impl<'a> StarSite<'a> {
    /// View premise `premise_idx` of a rule as a [`StarSite`], if it is an
    /// `Iter` premise.
    pub fn of_premise(
        rel_name: &'a str,
        rule_name: &'a str,
        premise_idx: usize,
        prem: &'a SpecTecPrem,
        rule_metavars: &'a [String],
    ) -> Option<Self> {
        let SpecTecPrem::Iter { pr1, it, xes } = prem else {
            return None;
        };
        Some(StarSite {
            rel_name,
            rule_name,
            premise_idx,
            pr1,
            it,
            xes,
            rule_metavars,
        })
    }

    /// The star relation's tag suffix `star.<rel>.<rule>.<idx>` (the full
    /// judgement tag is `rel.` + this, via [`tag`] — the [`super::fn_graph`]
    /// convention).
    pub fn star_tag(&self) -> String {
        format!(
            "star.{}.{}.{}",
            self.rel_name, self.rule_name, self.premise_idx
        )
    }
}

/// Census/residue notes a lowering records (never silent).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IterNote {
    /// The inner premise is an `If`: its condition went through the flattener
    /// (opaque residue under [`super::PureFlattener`]).
    InnerIf,
    /// A `ListN` bound that is not a plain `Var`: bound to a fresh metavar via
    /// a flattened `b = <bound>` condition.
    BoundFlattened,
    /// The inner `Rule` premise carries coarse element-access spines
    /// (`Idx`/`Dot`/`Len`/`Slice` in judgement position — the `Extend_store`
    /// family, review R3-F2): the aux clauses load and are sound (syntactic
    /// keys), but the access is not evaluated, so the inner judgement only
    /// meets ground keys carrying the same raw spine. Counted, never silent.
    CoarseInner,
    /// The whole site loads as a single [`opaque`] premise (unsupported inner
    /// premise kind / iterator shape — none in the bundled corpus).
    OpaqueSite(String),
}

/// What lowering one `Iter` site produced.
#[derive(Debug)]
pub struct LoweredIter {
    /// Premises for the **enclosing rule's** clause, in order (any flattened
    /// domain/bound premises first, the star judgement last).
    pub prems: Vec<LowerPrem>,
    /// Auxiliary clauses **defining** the star relation (append to the
    /// combined rule set; base/nil clause first).
    pub aux: Vec<Clause>,
    /// Metavariables the enclosing clause must additionally quantify (raw
    /// ids, first-needed order, deduped against
    /// [`StarSite::rule_metavars`]) — domain vars, ride-throughs, `ListN`
    /// bound vars, flattener-fresh vars.
    pub new_metavars: Vec<String>,
    /// Residue notes (see [`IterNote`]).
    pub notes: Vec<IterNote>,
}

// ============================================================================
// Star judgement construction (the one spine builder — see `fn_graph`)
// ============================================================================

/// The canonical judgement body of a star-relation instance: tag
/// `star.<rel>.<rule>.<idx>` (as `rel.`-prefixed by [`tag`]), body = the
/// arity-marked `app`-spine `starargs.<n> a₀ … aₙ₋₁`. Every producer and every
/// test MUST build star judgements through this one constructor.
pub fn star_judgement(tag_suffix: &str, args: &[Term]) -> Result<Term> {
    let mut spine = con(format!("starargs.{}", args.len()));
    for a in args {
        spine = app(spine, a.clone())?;
    }
    tag(tag_suffix, spine)
}

/// The star-relation tag suffix of an aux clause's conclusion (`star.…`), if
/// it is one — the spine walk shared with the integration layer's
/// `concl_tag`.
fn star_tag_of(concl: &Term) -> Option<&str> {
    let mut cur = concl;
    loop {
        let (f, _) = cur.as_app()?;
        match f.as_app() {
            Some((h, c)) => {
                if h.as_free().map(|v| v.name()) == Some("st$app")
                    && let Some(v) = c.as_free()
                    && let Some(t) = v.name().strip_prefix("st$c$rel.star.")
                {
                    return Some(t);
                }
                cur = f;
            }
            None => return None,
        }
    }
}

/// **R3-F5 defensive check** for wherever star aux clauses are appended to a
/// combined set: every site must own its `star.<rel>.<rule>.<idx>` tag
/// exclusively — a collision (e.g. two same-named rules of one relation with
/// `Iter` premises at the same index) would merge two sites' aux clauses into
/// one relation, letting each site's enclosing premise fire off the *other*
/// site's clauses (over-approximation). Every lowered site emits exactly two
/// aux clauses, so in a combined aux list each star tag must occur exactly
/// twice.
pub fn assert_unique_star_tags(aux: &[Clause]) {
    let mut counts: std::collections::BTreeMap<&str, usize> = std::collections::BTreeMap::new();
    for c in aux {
        let t = star_tag_of(&c.concl)
            .expect("star aux clause concludes in a star.<rel>.<rule>.<idx> relation");
        *counts.entry(t).or_default() += 1;
    }
    let bad: Vec<(&&str, &usize)> = counts.iter().filter(|(_, k)| **k != 2).collect();
    assert!(
        bad.is_empty(),
        "star tag collision (R3-F5) — sites sharing a star relation: {bad:?}"
    );
}

// ============================================================================
// Lowering
// ============================================================================

/// The lowered inner premise of a site.
struct Inner {
    /// Aux-clause premises the inner premise contributes (its judgement /
    /// flattened condition premises).
    prems: Vec<LowerPrem>,
    /// Flattener-fresh metavars those premises mention (quantified in the aux
    /// clause).
    extra_metavars: Vec<String>,
    /// The SpecTec metavariables of the inner premise expression, first-seen
    /// order (iteration vars + ride-throughs).
    vars: Vec<String>,
    /// Whether the inner premise was an `If` (census).
    is_if: bool,
    /// Whether the inner `Rule` premise carries coarse element-access spines
    /// (census — [`IterNote::CoarseInner`], review R3-F2).
    coarse_access: bool,
}

/// Whether an inner-premise expression carries a coarse element-access spine
/// (`Idx`/`Dot`/`Len`/`Slice` at a judgement-encoded position, post-canon;
/// nested iteration subtrees are self-contained syntactic keys and don't
/// count) — the R3-F2 census trigger.
fn has_coarse_access(e: &SpecTecExp) -> bool {
    use SpecTecExp as E;
    match encode::canon(e) {
        E::Iter { .. } => false,
        E::Idx { .. } | E::Dot { .. } | E::Len { .. } | E::Slice { .. } => true,
        other => children(other).into_iter().any(has_coarse_access),
    }
}

/// Lower the inner premise through the flattener seam. `None` = unsupported
/// kind (whole-site opaque).
fn lower_inner(pr1: &SpecTecPrem, fl: &mut dyn CondFlattener) -> Result<Option<Inner>> {
    match pr1 {
        SpecTecPrem::Rule { x, e, .. } => {
            let mut vars = Vec::new();
            collect_metavars(e, &mut vars);
            let (t, fltn) = fl.expr(e)?;
            let mut prems = fltn.prems;
            prems.push(LowerPrem::Judgement(tag(x, t)?));
            Ok(Some(Inner {
                prems,
                extra_metavars: fltn.new_metavars,
                vars,
                is_if: false,
                // `expr` is judgement-mode: element accesses stay coarse.
                coarse_access: has_coarse_access(e),
            }))
        }
        SpecTecPrem::If { e } => {
            let mut vars = Vec::new();
            collect_metavars(e, &mut vars);
            let Flattened {
                prems,
                new_metavars,
            } = fl.cond(e)?;
            Ok(Some(Inner {
                prems,
                extra_metavars: new_metavars,
                vars,
                is_if: true,
                // `cond` evaluates accesses through `ev.*` (or censuses).
                coarse_access: false,
            }))
        }
        // Not in the corpus (no `Let`, no `Else`, no nested `Iter` under
        // `Iter`) — refuse to guess; the site loads opaquely.
        SpecTecPrem::Let { .. } | SpecTecPrem::Else | SpecTecPrem::Iter { .. } => Ok(None),
    }
}

/// A name not in `used`, pushed into `used` (primes appended on collision).
fn fresh(base: &str, used: &mut Vec<String>) -> String {
    let mut name = base.to_string();
    while used.iter().any(|u| u == &name) {
        name.push('\'');
    }
    used.push(name.clone());
    name
}

/// Push `id` if absent (first-seen dedup).
fn push_unique(out: &mut Vec<String>, id: &str) {
    if !out.iter().any(|s| s == id) {
        out.push(id.to_owned());
    }
}

/// Wrap every occurrence of numeric metavar `v` in `t` with the literal tag:
/// `st$v$v ↦ app(st$c$num.nat, st$v$v)` — the judgement-spine leg of the
/// numeric-metavar discipline.
fn wrap_numeric(v: &str, t: &Term) -> Result<Term> {
    let wrapped = app(con("num.nat"), metavar(v))?;
    Ok(subst_free(t, &Var::new(metavar_name(v), phi()), &wrapped))
}

/// Wrap numeric metavar `v` in every **judgement** premise (`Side`s keep the
/// bare variable — the other leg of the discipline).
fn wrap_numeric_prems(v: &str, prems: Vec<LowerPrem>) -> Result<Vec<LowerPrem>> {
    prems
        .into_iter()
        .map(|p| {
            Ok(match p {
                LowerPrem::Judgement(j) => LowerPrem::Judgement(wrap_numeric(v, &j)?),
                LowerPrem::Side(s) => LowerPrem::Side(s),
            })
        })
        .collect()
}

/// The whole-site opaque fallback: one underivable tagged premise, reported.
fn opaque_site(site: &StarSite, why: &str) -> Result<LoweredIter> {
    let body = con(site.star_tag());
    Ok(LoweredIter {
        prems: vec![LowerPrem::Judgement(opaque(&format!("iter.{why}"), body)?)],
        aux: Vec::new(),
        new_metavars: Vec::new(),
        notes: vec![IterNote::OpaqueSite(why.to_owned())],
    })
}

/// Everything shared between the iterator kinds, computed once.
struct SiteParts {
    tag_suffix: String,
    /// Element metavar ids (one per `Dom`).
    elems: Vec<String>,
    /// Ride-through metavar ids (inner-premise vars that are not iterated).
    rides: Vec<String>,
    /// Every name in scope so far (for freshness).
    used: Vec<String>,
    notes: Vec<IterNote>,
    new_metavars: Vec<String>,
}

impl SiteParts {
    fn new(site: &StarSite, inner: &Inner, index_var: Option<&str>) -> Self {
        let elems: Vec<String> = site
            .xes
            .iter()
            .map(|SpecTecIterExp::Dom { x, .. }| x.clone())
            .collect();
        let rides: Vec<String> = inner
            .vars
            .iter()
            .filter(|v| !elems.iter().any(|e| e == *v) && Some(v.as_str()) != index_var)
            .cloned()
            .collect();
        let mut used: Vec<String> = site.rule_metavars.to_vec();
        for v in inner.vars.iter().chain(&elems).chain(&inner.extra_metavars) {
            push_unique(&mut used, v);
        }
        if let Some(i) = index_var {
            push_unique(&mut used, i);
        }
        let mut notes = Vec::new();
        if inner.is_if {
            notes.push(IterNote::InnerIf);
        }
        if inner.coarse_access {
            notes.push(IterNote::CoarseInner);
        }
        SiteParts {
            tag_suffix: site.star_tag(),
            elems,
            rides,
            used,
            notes,
            new_metavars: Vec::new(),
        }
    }

    fn ride_terms(&self) -> Vec<Term> {
        self.rides.iter().map(metavar).collect()
    }

    /// Record a rule-level metavar need (dedup against the rule's own).
    fn need_metavar(&mut self, site: &StarSite, id: &str) {
        if !site.rule_metavars.iter().any(|m| m == id) {
            push_unique(&mut self.new_metavars, id);
        }
    }

    /// Flatten the site's domain expressions into state terms for the
    /// enclosing premise (plain `Var`s throughout the corpus, but total),
    /// accumulating any flattening premises and rule-level metavars.
    fn domain_states(
        &mut self,
        site: &StarSite,
        fl: &mut dyn CondFlattener,
        main_prems: &mut Vec<LowerPrem>,
    ) -> Result<Vec<Term>> {
        let mut states = Vec::new();
        for SpecTecIterExp::Dom { e, .. } in site.xes {
            let mut dom_vars = Vec::new();
            collect_metavars(e, &mut dom_vars);
            let (t, fltn) = fl.expr(e)?;
            main_prems.extend(fltn.prems);
            for v in dom_vars.iter().chain(&fltn.new_metavars) {
                self.need_metavar(site, v);
            }
            states.push(t);
        }
        // Ride-throughs appear in the enclosing premise too.
        let rides = self.rides.clone();
        for r in &rides {
            self.need_metavar(site, r);
        }
        Ok(states)
    }
}

/// Lower one `Iter` premise site into its enclosing-rule premises and the aux
/// clauses defining its star relation. Total: anything unsupported loads as a
/// reported [`opaque`] premise, never an error and never a dropped premise.
pub fn lower_iter_premise(site: &StarSite, fl: &mut dyn CondFlattener) -> Result<LoweredIter> {
    let Some(inner) = lower_inner(site.pr1, fl)? else {
        return opaque_site(site, "inner-premise-kind");
    };
    match site.it {
        SpecTecIter::List => lower_list(site, inner, fl, false),
        SpecTecIter::List1 => lower_list(site, inner, fl, true),
        SpecTecIter::Opt => lower_opt(site, inner, fl),
        SpecTecIter::ListN { e, xo } => lower_listn(site, inner, fl, e, xo),
    }
}

/// `List` (and `List1`): the k-ary zip-star over snoc spines.
fn lower_list(
    site: &StarSite,
    inner: Inner,
    fl: &mut dyn CondFlattener,
    require_nonempty: bool,
) -> Result<LoweredIter> {
    if site.xes.is_empty() {
        // A `List` iteration with no domains has nothing to recurse on.
        return opaque_site(site, "list-no-vars");
    }
    let mut parts = SiteParts::new(site, &inner, None);
    let k = parts.elems.len();
    let rides = parts.ride_terms();

    // nil clause: star(c…, nil, …, nil).
    let mut nil_args = rides.clone();
    nil_args.extend(std::iter::repeat_n(con("list"), k));
    let nil_clause = Clause {
        metavars: parts.rides.clone(),
        prems: Vec::new(),
        concl: star_judgement(&parts.tag_suffix, &nil_args)?,
    };

    // snoc clause: P(x…) ⟹ star(c…, xs…) ⟹ star(c…, app(xs,x)…).
    let xs_names: Vec<String> = (0..k)
        .map(|i| fresh(&format!("star#xs{i}"), &mut parts.used))
        .collect();
    let mut prev_args = rides.clone();
    prev_args.extend(xs_names.iter().map(|n| metavar(n)));
    let mut next_args = rides.clone();
    for (xs, x) in xs_names.iter().zip(&parts.elems) {
        next_args.push(app(metavar(xs), metavar(x))?);
    }
    let mut snoc_prems = inner.prems;
    snoc_prems.push(LowerPrem::Judgement(star_judgement(
        &parts.tag_suffix,
        &prev_args,
    )?));
    let mut snoc_metavars = parts.rides.clone();
    snoc_metavars.extend(xs_names);
    snoc_metavars.extend(parts.elems.clone());
    snoc_metavars.extend(inner.extra_metavars.clone());
    let snoc_clause = Clause {
        metavars: snoc_metavars,
        prems: snoc_prems,
        concl: star_judgement(&parts.tag_suffix, &next_args)?,
    };

    // Enclosing premise: star(c…, l…) over the flattened domains.
    let mut main_prems = Vec::new();
    let mut main_args = rides;
    let states = parts.domain_states(site, fl, &mut main_prems)?;
    main_args.extend(states.iter().cloned());
    if require_nonempty {
        // `List1` (not in the corpus): the star premise plus an explicitly
        // underivable non-emptiness antecedent — sound, reported.
        main_prems.push(LowerPrem::Judgement(opaque(
            "iter.list1.nonempty",
            states[0].clone(),
        )?));
        parts.notes.push(IterNote::OpaqueSite("list1".into()));
    }
    main_prems.push(LowerPrem::Judgement(star_judgement(
        &parts.tag_suffix,
        &main_args,
    )?));

    Ok(LoweredIter {
        prems: main_prems,
        aux: vec![nil_clause, snoc_clause],
        new_metavars: parts.new_metavars,
        notes: parts.notes,
    })
}

/// `Opt`: none/some clauses over the encoder's `opt.none` / `opt.some x`.
fn lower_opt(site: &StarSite, inner: Inner, fl: &mut dyn CondFlattener) -> Result<LoweredIter> {
    if site.xes.is_empty() {
        return opaque_site(site, "opt-no-vars");
    }
    let mut parts = SiteParts::new(site, &inner, None);
    let k = parts.elems.len();
    let rides = parts.ride_terms();

    // none clause: star(c…, opt.none, …).
    let mut none_args = rides.clone();
    none_args.extend(std::iter::repeat_n(con("opt.none"), k));
    let none_clause = Clause {
        metavars: parts.rides.clone(),
        prems: Vec::new(),
        concl: star_judgement(&parts.tag_suffix, &none_args)?,
    };

    // some clause: P(x…) ⟹ star(c…, app(opt.some, x)…).
    let mut some_args = rides.clone();
    for x in &parts.elems {
        some_args.push(app(con("opt.some"), metavar(x))?);
    }
    let mut some_metavars = parts.rides.clone();
    some_metavars.extend(parts.elems.clone());
    some_metavars.extend(inner.extra_metavars.clone());
    let some_clause = Clause {
        metavars: some_metavars,
        prems: inner.prems,
        concl: star_judgement(&parts.tag_suffix, &some_args)?,
    };

    // Enclosing premise: star(c…, o…).
    let mut main_prems = Vec::new();
    let mut main_args = rides;
    main_args.extend(parts.domain_states(site, fl, &mut main_prems)?);
    main_prems.push(LowerPrem::Judgement(star_judgement(
        &parts.tag_suffix,
        &main_args,
    )?));

    Ok(LoweredIter {
        prems: main_prems,
        aux: vec![none_clause, some_clause],
        new_metavars: parts.new_metavars,
        notes: parts.notes,
    })
}

/// `ListN`: the real-nat indexed star (index wrapped in spines, bare in the
/// successor `Side`; element state consumed in lockstep when the site has
/// iteration vars).
fn lower_listn(
    site: &StarSite,
    inner: Inner,
    fl: &mut dyn CondFlattener,
    bound: &[SpecTecExp],
    xo: &[String],
) -> Result<LoweredIter> {
    let Some(bound_exp) = bound.first() else {
        // A `ListN` without a bound expression is not meaningful here.
        return opaque_site(site, "listn-no-bound");
    };
    // The index binder: `xo`'s var if present, else a fresh name (the inner
    // premise then simply doesn't mention it).
    let named_index = xo.first().map(String::as_str);
    let mut parts = SiteParts::new(site, &inner, named_index);
    let idx = match named_index {
        Some(i) => i.to_owned(),
        None => fresh("star#i", &mut parts.used),
    };
    // If the flattener already has the index under the numeric discipline (a
    // same-named rule metavar used arithmetically outside the site), its inner
    // premises are already wrapped — wrapping again would double-wrap.
    let idx_prewrapped = fl.is_numeric(&idx);
    let k = parts.elems.len();
    let rides = parts.ride_terms();

    // base: istar(c…, nil…, ⌜0⌝-wrapped).
    let mut base_args = rides.clone();
    base_args.extend(std::iter::repeat_n(con("list"), k));
    base_args.push(app(con("num.nat"), mk_nat(0u64))?);
    let base_clause = Clause {
        metavars: parts.rides.clone(),
        prems: Vec::new(),
        concl: star_judgement(&parts.tag_suffix, &base_args)?,
    };

    // step: j = S i ⟹ P[i wrapped in judgements] ⟹ istar(c…, xs…, i) ⟹
    //       istar(c…, app(xs,x)…, j).
    let xs_names: Vec<String> = (0..k)
        .map(|i| fresh(&format!("star#xs{i}"), &mut parts.used))
        .collect();
    let j = fresh("star#j", &mut parts.used);
    let succ_side = metavar(&j).equals(Term::app(Term::succ(), metavar(&idx)))?;
    let mut step_prems = vec![LowerPrem::Side(succ_side)];
    step_prems.extend(if idx_prewrapped {
        inner.prems
    } else {
        wrap_numeric_prems(&idx, inner.prems)?
    });
    let mut prev_args = rides.clone();
    prev_args.extend(xs_names.iter().map(|n| metavar(n)));
    prev_args.push(app(con("num.nat"), metavar(&idx))?);
    step_prems.push(LowerPrem::Judgement(star_judgement(
        &parts.tag_suffix,
        &prev_args,
    )?));
    let mut next_args = rides.clone();
    for (xs, x) in xs_names.iter().zip(&parts.elems) {
        next_args.push(app(metavar(xs), metavar(x))?);
    }
    next_args.push(app(con("num.nat"), metavar(&j))?);
    let mut step_metavars = parts.rides.clone();
    step_metavars.extend(xs_names);
    step_metavars.extend(parts.elems.clone());
    step_metavars.push(idx.clone());
    step_metavars.push(j);
    step_metavars.extend(inner.extra_metavars.clone());
    let step_clause = Clause {
        metavars: step_metavars,
        prems: step_prems,
        concl: star_judgement(&parts.tag_suffix, &next_args)?,
    };

    // Enclosing premise: istar(c…, l…, B).
    let mut main_prems = Vec::new();
    let mut main_args = rides;
    main_args.extend(parts.domain_states(site, fl, &mut main_prems)?);
    let bound_term = match bound_exp {
        SpecTecExp::Var { id } => {
            // Plain-`Var` bound: numeric-wrapped, currency = bare numeral.
            parts.need_metavar(site, id);
            app(con("num.nat"), metavar(id))?
        }
        other => {
            // Fresh numeric bound metavar `b`, constrained by the flattened
            // condition `b = <bound>` (ev.len-style under the real
            // flattener; opaque under `PureFlattener`). `b` is put under the
            // flattener's numeric discipline FIRST so the condition renders
            // as a bare-arithmetic Side over `b` (currency = bare numeral —
            // matching the single wrap in the istar bound position below).
            let b = fresh("star#n", &mut parts.used);
            fl.mark_numeric(&b);
            let cond = SpecTecExp::Cmp {
                op: SpecTecCmpOp::Eq,
                t: SpecTecOpTyp::Num(SpecTecNumTyp::Nat),
                e1: Box::new(SpecTecExp::Var { id: b.clone() }),
                e2: Box::new(other.clone()),
            };
            let fltn = fl.cond(&cond)?;
            main_prems.extend(fltn.prems);
            push_unique(&mut parts.new_metavars, &b);
            for v in &fltn.new_metavars {
                parts.need_metavar(site, v);
            }
            parts.notes.push(IterNote::BoundFlattened);
            app(con("num.nat"), metavar(&b))?
        }
    };
    main_args.push(bound_term);
    main_prems.push(LowerPrem::Judgement(star_judgement(
        &parts.tag_suffix,
        &main_args,
    )?));

    Ok(LoweredIter {
        prems: main_prems,
        aux: vec![base_clause, step_clause],
        new_metavars: parts.new_metavars,
        notes: parts.notes,
    })
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::super::super::encode::encode_exp;
    use super::super::super::spec::wasm_spec;
    use super::super::{PureFlattener, rule_set_of};
    use super::*;
    use crate::metalogic::{self, Premise};
    use covalence_hol_eval::EvalThm as Thm;
    use covalence_spectec::ast::{MixOp, SpecTecDef, SpecTecNum, SpecTecRule};

    fn var(id: &str) -> SpecTecExp {
        SpecTecExp::Var { id: id.into() }
    }
    fn mixop(s: &str) -> MixOp {
        MixOp::new(vec![s.to_string()])
    }
    fn zero() -> SpecTecExp {
        SpecTecExp::Case {
            op: mixop("zero"),
            e1: Box::new(SpecTecExp::Opt { eo: None }),
        }
    }
    fn rule_prem(rel: &str, e: SpecTecExp) -> SpecTecPrem {
        SpecTecPrem::Rule {
            x: rel.into(),
            as1: vec![],
            op: mixop(rel),
            e,
        }
    }
    fn dom(x: &str, l: &str) -> SpecTecIterExp {
        SpecTecIterExp::Dom {
            x: x.into(),
            e: var(l),
        }
    }
    fn assert_genuine(thm: &Thm) {
        assert!(thm.hyps().is_empty(), "hypothesis-free");
    }

    /// `List` zip-star, one iteration var: synthesize the star for
    /// `Q(l) ⟸ (R(x))^{x ∈ l}` with `R` the single-clause relation `R(zero)`,
    /// then derive `Q [z,z,z]` bottom-up (nil, snoc ×3, main) hypothesis-free.
    #[test]
    fn list_star_derives_three_elements() {
        let iter_prem = SpecTecPrem::Iter {
            pr1: Box::new(rule_prem("R", var("x"))),
            it: SpecTecIter::List,
            xes: vec![dom("x", "l")],
        };
        let rule_mvs = vec!["l".to_string()];
        let site = StarSite::of_premise("Q", "r", 0, &iter_prem, &rule_mvs).unwrap();
        let li = lower_iter_premise(&site, &mut PureFlattener).unwrap();
        assert_eq!(li.aux.len(), 2);
        assert!(li.new_metavars.is_empty(), "domain var l already in scope");
        assert!(li.notes.is_empty());
        assert_eq!(li.prems.len(), 1, "just the star judgement");

        // Combined rule set: R axiom, the main Q clause, then the aux pair.
        let r_axiom = Clause {
            metavars: vec![],
            prems: vec![],
            concl: tag("R", encode_exp(&zero()).unwrap()).unwrap(),
        };
        let main = Clause {
            metavars: rule_mvs.clone(),
            prems: li.prems,
            concl: tag("Q", encode_exp(&var("l")).unwrap()).unwrap(),
        };
        let mut clauses = vec![r_axiom, main];
        clauses.extend(li.aux);
        let rs = rule_set_of(clauses);
        let n = rs.n_clauses().unwrap();
        assert_eq!(n, 4);

        let st = site.star_tag();
        assert_eq!(st, "star.Q.r.0");
        let z = encode_exp(&zero()).unwrap();
        let der_r = metalogic::derive_mixed(&rs, 0, n, &[], vec![]).unwrap();

        // nil (clause 2), then three snocs (clause 3).
        let mut list = con("list");
        let mut der = metalogic::derive_mixed(&rs, 2, n, &[], vec![]).unwrap();
        assert_eq!(
            der.concl(),
            &metalogic::derivable(&rs, &star_judgement(&st, &[list.clone()]).unwrap()).unwrap()
        );
        for _ in 0..3 {
            der = metalogic::derive_mixed(
                &rs,
                3,
                n,
                &[list.clone(), z.clone()],
                vec![Premise::Derivation(der_r.clone()), Premise::Derivation(der)],
            )
            .unwrap();
            list = app(list, z.clone()).unwrap();
            assert_eq!(
                der.concl(),
                &metalogic::derivable(&rs, &star_judgement(&st, &[list.clone()]).unwrap()).unwrap()
            );
        }
        assert_genuine(&der);
        // list is now exactly encode([z,z,z]).
        let enc3 = encode_exp(&SpecTecExp::List {
            es: vec![zero(), zero(), zero()],
        })
        .unwrap();
        assert_eq!(list, enc3);

        // Main rule at l := [z,z,z].
        let der_q =
            metalogic::derive_mixed(&rs, 1, n, &[enc3.clone()], vec![Premise::Derivation(der)])
                .unwrap();
        assert_genuine(&der_q);
        assert_eq!(
            der_q.concl(),
            &metalogic::derivable(&rs, &tag("Q", enc3).unwrap()).unwrap()
        );
    }

    /// `Opt` both ways: `Q(o) ⟸ (R(x))?` — derive `Q(none)` via the trivial
    /// clause and `Q(some z)` via the some clause.
    #[test]
    fn opt_star_derives_none_and_some() {
        let iter_prem = SpecTecPrem::Iter {
            pr1: Box::new(rule_prem("R", var("x"))),
            it: SpecTecIter::Opt,
            xes: vec![dom("x", "o")],
        };
        let rule_mvs = vec!["o".to_string()];
        let site = StarSite::of_premise("Q", "r", 0, &iter_prem, &rule_mvs).unwrap();
        let li = lower_iter_premise(&site, &mut PureFlattener).unwrap();
        assert_eq!(li.aux.len(), 2);

        let r_axiom = Clause {
            metavars: vec![],
            prems: vec![],
            concl: tag("R", encode_exp(&zero()).unwrap()).unwrap(),
        };
        let main = Clause {
            metavars: rule_mvs.clone(),
            prems: li.prems,
            concl: tag("Q", encode_exp(&var("o")).unwrap()).unwrap(),
        };
        let mut clauses = vec![r_axiom, main];
        clauses.extend(li.aux);
        let rs = rule_set_of(clauses);
        let n = rs.n_clauses().unwrap();

        // Q(none): none clause (2) then main (1).
        let enc_none = encode_exp(&SpecTecExp::Opt { eo: None }).unwrap();
        let der_none = metalogic::derive_mixed(&rs, 2, n, &[], vec![]).unwrap();
        let q_none = metalogic::derive_mixed(
            &rs,
            1,
            n,
            &[enc_none.clone()],
            vec![Premise::Derivation(der_none)],
        )
        .unwrap();
        assert_genuine(&q_none);
        assert_eq!(
            q_none.concl(),
            &metalogic::derivable(&rs, &tag("Q", enc_none).unwrap()).unwrap()
        );

        // Q(some z): R, some clause (3, arg z), main.
        let z = encode_exp(&zero()).unwrap();
        let enc_some = encode_exp(&SpecTecExp::Opt {
            eo: Some(Box::new(zero())),
        })
        .unwrap();
        let der_r = metalogic::derive_mixed(&rs, 0, n, &[], vec![]).unwrap();
        let der_some =
            metalogic::derive_mixed(&rs, 3, n, &[z], vec![Premise::Derivation(der_r)]).unwrap();
        let q_some = metalogic::derive_mixed(
            &rs,
            1,
            n,
            &[enc_some.clone()],
            vec![Premise::Derivation(der_some)],
        )
        .unwrap();
        assert_genuine(&q_some);
        assert_eq!(
            q_some.concl(),
            &metalogic::derivable(&rs, &tag("Q", enc_some).unwrap()).unwrap()
        );
    }

    /// `ListN` with a concrete bound: `Q(n) ⟸ (R(i))^{i<n}` — the istar
    /// 0,1,2 chain with real numerals (successor discharged by computation),
    /// then the main rule at `n := 2`. The final judgement's bound position is
    /// exactly `encode(Num 2)` — the numeric-metavar discipline end to end.
    #[test]
    fn listn_star_derives_concrete_bound() {
        let iter_prem = SpecTecPrem::Iter {
            pr1: Box::new(rule_prem("R", var("i"))),
            it: SpecTecIter::ListN {
                e: vec![var("n")],
                xo: vec!["i".into()],
            },
            xes: vec![],
        };
        let rule_mvs = vec!["n".to_string()];
        let site = StarSite::of_premise("Q", "r", 0, &iter_prem, &rule_mvs).unwrap();
        let li = lower_iter_premise(&site, &mut PureFlattener).unwrap();
        assert_eq!(li.aux.len(), 2);
        assert!(li.notes.is_empty(), "Var bound needs no flattening");
        assert!(li.new_metavars.is_empty(), "bound var n already in scope");
        assert_eq!(li.prems.len(), 1);

        // R is schematic (∀x. R x) so wrapped-index instances are derivable.
        let r_schema = Clause {
            metavars: vec!["x".to_string()],
            prems: vec![],
            concl: tag("R", metavar("x")).unwrap(),
        };
        // Main clause: conclusion spine occurrence of numeric `n` is wrapped
        // (what the integration layer emits for numeric metavars).
        let main = Clause {
            metavars: rule_mvs.clone(),
            prems: li.prems,
            concl: tag("Q", app(con("num.nat"), metavar("n")).unwrap()).unwrap(),
        };
        let mut clauses = vec![r_schema, main];
        clauses.extend(li.aux);
        let rs = rule_set_of(clauses);
        let n = rs.n_clauses().unwrap();
        let st = site.star_tag();

        // base (clause 2): istar(⌜0⌝-wrapped).
        let wrap = |k: u64| app(con("num.nat"), mk_nat(k)).unwrap();
        let mut der = metalogic::derive_mixed(&rs, 2, n, &[], vec![]).unwrap();
        assert_eq!(
            der.concl(),
            &metalogic::derivable(&rs, &star_judgement(&st, &[wrap(0)]).unwrap()).unwrap()
        );
        // step (clause 3), metavars [i, star#j]: k → k+1 with the successor
        // side condition proved by kernel computation.
        for k in 0u64..2 {
            let side = mk_nat(k + 1)
                .equals(Term::app(Term::succ(), mk_nat(k)))
                .unwrap()
                .prove_true()
                .unwrap();
            let der_r = metalogic::derive_mixed(&rs, 0, n, &[wrap(k)], vec![]).unwrap();
            der = metalogic::derive_mixed(
                &rs,
                3,
                n,
                &[mk_nat(k), mk_nat(k + 1)],
                vec![
                    Premise::Side(side),
                    Premise::Derivation(der_r),
                    Premise::Derivation(der),
                ],
            )
            .unwrap();
            assert_eq!(
                der.concl(),
                &metalogic::derivable(&rs, &star_judgement(&st, &[wrap(k + 1)]).unwrap()).unwrap()
            );
        }
        assert_genuine(&der);

        // Main rule at n := ⌜2⌝ (bare-numeral currency): the conclusion's
        // spine position is exactly encode(Num 2).
        let der_q =
            metalogic::derive_mixed(&rs, 1, n, &[mk_nat(2u64)], vec![Premise::Derivation(der)])
                .unwrap();
        assert_genuine(&der_q);
        let enc_two = encode_exp(&SpecTecExp::Num {
            n: SpecTecNum::Nat(2),
        })
        .unwrap();
        assert_eq!(
            der_q.concl(),
            &metalogic::derivable(&rs, &tag("Q", enc_two).unwrap()).unwrap()
        );
    }

    // ------------------------------------------------------------------
    // Real-spec sites
    // ------------------------------------------------------------------

    /// Every `Rel` definition of the spec (flattening `Rec` groups).
    fn relations(defs: &[SpecTecDef]) -> Vec<&SpecTecDef> {
        let mut out = Vec::new();
        fn go<'a>(d: &'a SpecTecDef, out: &mut Vec<&'a SpecTecDef>) {
            match d {
                SpecTecDef::Rel { .. } => out.push(d),
                SpecTecDef::Rec { ds } => ds.iter().for_each(|x| go(x, out)),
                _ => {}
            }
        }
        defs.iter().for_each(|d| go(d, &mut out));
        out
    }

    /// The rule-level metavar context an integration pass would have collected
    /// before premise `upto` (conclusion + all earlier premises' `Rule`
    /// expressions).
    fn context_metavars(rule: &SpecTecRule, upto: usize) -> Vec<String> {
        let SpecTecRule::Rule { e, prs, .. } = rule;
        let mut mvs = Vec::new();
        collect_metavars(e, &mut mvs);
        for pr in prs.iter().take(upto) {
            if let SpecTecPrem::Rule { e, .. } = pr {
                collect_metavars(e, &mut mvs);
            }
        }
        mvs
    }

    /// `Resulttype_ok`'s single-Iter rule lowers structurally: one ride
    /// (the context `C`), one list state, domain var `t*` surfaced as a new
    /// rule metavar, aux = nil + snoc.
    #[test]
    fn real_resulttype_ok_site_shape() {
        let defs = wasm_spec();
        let rels = relations(&defs);
        let def = rels
            .iter()
            .find(|d| matches!(d, SpecTecDef::Rel { x, .. } if x == "Resulttype_ok"))
            .expect("Resulttype_ok in the bundled spec");
        let SpecTecDef::Rel { x, rules, .. } = def else {
            unreachable!()
        };
        let SpecTecRule::Rule { x: rname, prs, .. } = &rules[0];
        let ctx = context_metavars(&rules[0], 0);
        let site = StarSite::of_premise(x, rname, 0, &prs[0], &ctx).expect("Iter premise");
        let li = lower_iter_premise(&site, &mut PureFlattener).unwrap();

        assert_eq!(li.aux.len(), 2, "nil + snoc");
        assert!(li.notes.is_empty(), "inner Rule premise, no residue");
        assert_eq!(li.prems.len(), 1);
        // The domain var `t*` already occurs in the conclusion (the encoder's
        // canonical view collapses the identity iteration `t*` to it), so the
        // site introduces no new rule-level metavars.
        assert!(li.new_metavars.is_empty(), "domain var already in scope");
        // nil clause: one ride (C), no premises; snoc: inner + star premise.
        assert_eq!(li.aux[0].metavars, vec!["C".to_string()]);
        assert!(li.aux[0].prems.is_empty());
        assert_eq!(li.aux[1].prems.len(), 2);
        // The enclosing star premise mentions the domain metavar `st$v$t*`.
        let LowerPrem::Judgement(j) = &li.prems[0] else {
            panic!("star premise is a judgement");
        };
        let expected = star_judgement(&site.star_tag(), &[metavar("C"), metavar("t*")]).unwrap();
        assert_eq!(j, &expected);
    }

    /// `Blocktype_ok/valtype`'s `Opt` site: none/some aux clauses over the
    /// encoder's option constructors.
    #[test]
    fn real_blocktype_ok_opt_site_shape() {
        let defs = wasm_spec();
        let rels = relations(&defs);
        let def = rels
            .iter()
            .find(|d| matches!(d, SpecTecDef::Rel { x, .. } if x == "Blocktype_ok"))
            .expect("Blocktype_ok in the bundled spec");
        let SpecTecDef::Rel { x, rules, .. } = def else {
            unreachable!()
        };
        let (rname, prem, ctx) = rules
            .iter()
            .find_map(|r| {
                let SpecTecRule::Rule { x: rname, prs, .. } = r;
                prs.iter().enumerate().find_map(|(i, p)| {
                    matches!(
                        p,
                        SpecTecPrem::Iter {
                            it: SpecTecIter::Opt,
                            ..
                        }
                    )
                    .then(|| (rname.clone(), p.clone(), context_metavars(r, i)))
                })
            })
            .expect("an Opt Iter site");
        let site = StarSite::of_premise(x, &rname, 0, &prem, &ctx).unwrap();
        let li = lower_iter_premise(&site, &mut PureFlattener).unwrap();
        assert_eq!(li.aux.len(), 2);
        assert!(li.notes.is_empty());
        // none clause conclusion carries the opt.none leaf in state position.
        let nil_concl = &li.aux[0].concl;
        let expected = star_judgement(&site.star_tag(), &[metavar("C"), con("opt.none")]).unwrap();
        assert_eq!(nil_concl, &expected);
    }

    /// A real `Len`-bound `ListN` site (`Store_ok`) takes the
    /// fresh-bound-metavar + flattened `b = |l|` route (opaque under
    /// `PureFlattener` — loads, cannot fire).
    #[test]
    fn real_store_ok_len_bound_flattens() {
        let defs = wasm_spec();
        let rels = relations(&defs);
        let def = rels
            .iter()
            .find(|d| matches!(d, SpecTecDef::Rel { x, .. } if x == "Store_ok"))
            .expect("Store_ok in the bundled spec");
        let SpecTecDef::Rel { x, rules, .. } = def else {
            unreachable!()
        };
        let (rname, idx, prem, ctx) = rules
            .iter()
            .find_map(|r| {
                let SpecTecRule::Rule { x: rname, prs, .. } = r;
                prs.iter().enumerate().find_map(|(i, p)| {
                    matches!(
                        p,
                        SpecTecPrem::Iter {
                            it: SpecTecIter::ListN { .. },
                            ..
                        }
                    )
                    .then(|| (rname.clone(), i, p.clone(), context_metavars(r, i)))
                })
            })
            .expect("a ListN Iter site");
        let site = StarSite::of_premise(x, &rname, idx, &prem, &ctx).unwrap();
        let li = lower_iter_premise(&site, &mut PureFlattener).unwrap();
        assert_eq!(li.aux.len(), 2, "base + step");
        assert!(li.notes.contains(&IterNote::BoundFlattened));
        // The bound-binding condition premise precedes the istar judgement.
        assert!(li.prems.len() >= 2);
        assert!(
            li.new_metavars.iter().any(|m| m.starts_with("star#n")),
            "fresh bound metavar surfaced"
        );
    }

    // ------------------------------------------------------------------
    // Whole-spec census
    // ------------------------------------------------------------------

    /// Walk all 92 `Iter` sites of the bundled WASM 3.0 spec, lower each with
    /// the [`PureFlattener`] baseline, kernel-check every aux clause, and pin
    /// the census exactly. Soundness frame: 0 failures, 0 whole-site opaques —
    /// every site loads structurally; the only residue is flattener-opaque
    /// conditions (inner `If`s and `Len` bounds), reported below.
    #[test]
    fn whole_spec_iter_census() {
        let defs = wasm_spec();
        let mut sites = 0usize;
        let (mut n_list, mut n_listn, mut n_opt, mut n_list1) = (0usize, 0, 0, 0);
        let (mut inner_rule, mut inner_if) = (0usize, 0);
        let mut aux_clauses = Vec::new();
        let mut inner_if_residue = 0usize;
        let mut bound_flattened = 0usize;
        let mut coarse_inner = 0usize;
        let mut opaque_sites = 0usize;
        let mut tags = std::collections::BTreeSet::new();

        for def in relations(&defs) {
            let SpecTecDef::Rel { x, rules, .. } = def else {
                unreachable!()
            };
            for rule in rules {
                let SpecTecRule::Rule { x: rname, prs, .. } = rule;
                for (i, pr) in prs.iter().enumerate() {
                    let ctx = context_metavars(rule, i);
                    let Some(site) = StarSite::of_premise(x, rname, i, pr, &ctx) else {
                        continue;
                    };
                    sites += 1;
                    // R3-F5: every site owns its star tag exclusively.
                    assert!(
                        tags.insert(site.star_tag()),
                        "duplicate star tag {}",
                        site.star_tag()
                    );
                    match site.it {
                        SpecTecIter::List => n_list += 1,
                        SpecTecIter::ListN { .. } => n_listn += 1,
                        SpecTecIter::Opt => n_opt += 1,
                        SpecTecIter::List1 => n_list1 += 1,
                    }
                    match site.pr1 {
                        SpecTecPrem::Rule { .. } => inner_rule += 1,
                        SpecTecPrem::If { .. } => inner_if += 1,
                        _ => {}
                    }
                    let li = lower_iter_premise(&site, &mut PureFlattener)
                        .expect("every corpus site lowers");
                    // Every premise term is well-typed in the carrier.
                    for p in li.prems.iter().chain(li.aux.iter().flat_map(|c| &c.prems)) {
                        match p {
                            LowerPrem::Judgement(j) => {
                                assert_eq!(j.type_of().unwrap(), phi());
                            }
                            LowerPrem::Side(s) => {
                                assert_eq!(s.type_of().unwrap(), covalence_core::Type::bool());
                            }
                        }
                    }
                    if li.notes.contains(&IterNote::InnerIf) {
                        inner_if_residue += 1;
                    }
                    if li.notes.contains(&IterNote::BoundFlattened) {
                        bound_flattened += 1;
                    }
                    if li.notes.contains(&IterNote::CoarseInner) {
                        coarse_inner += 1;
                    }
                    if li
                        .notes
                        .iter()
                        .any(|n| matches!(n, IterNote::OpaqueSite(_)))
                    {
                        opaque_sites += 1;
                    }
                    aux_clauses.extend(li.aux);
                }
            }
        }

        // R3-F5: the appended aux list carries exactly two clauses per tag.
        assert_unique_star_tags(&aux_clauses);

        // Kernel-check every emitted aux clause in one combined rule set (the
        // layout builds + type-checks each clause term).
        let n_aux = aux_clauses.len();
        let rs = rule_set_of(aux_clauses);
        assert_eq!(rs.n_clauses().unwrap(), n_aux);

        println!("iter-premise census (bundled WASM 3.0 spec):");
        println!("  sites total:            {sites}");
        println!(
            "  by iterator:            list {n_list} / listn {n_listn} / opt {n_opt} / list1 {n_list1}"
        );
        println!("  by inner premise:       rule {inner_rule} / if {inner_if}");
        println!("  lowered structurally:   {}", sites - opaque_sites);
        println!("  aux clauses emitted:    {n_aux} (kernel-checked)");
        println!("  inner-If opaque residue:{inner_if_residue}");
        println!("  bound-flattened (|l|):  {bound_flattened}");
        println!("  coarse-inner access:    {coarse_inner}");
        println!("  whole-site opaque:      {opaque_sites}");

        assert_eq!(sites, 92);
        assert_eq!((n_list, n_listn, n_opt, n_list1), (71, 16, 5, 0));
        assert_eq!((inner_rule, inner_if), (74, 18));
        assert_eq!(opaque_sites, 0, "every corpus site lowers structurally");
        assert_eq!(n_aux, 184, "two aux clauses per site");
        assert_eq!(inner_if_residue, 18);
        assert_eq!(bound_flattened, 13, "the Len-bound ListN sites");
        // R3-F2: element accesses inside inner Rule premises stay coarse
        // (judgement position) — censused, not silent. 14 sites: the 10
        // Len-bound `Extend_store`-family sites (`S.FUNCS[i]`-style spines)
        // plus 4 more inner-Rule access spines the same detector catches.
        assert_eq!(coarse_inner, 14, "coarse element-access inner premises");
    }
}
