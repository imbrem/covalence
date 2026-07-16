//! **Shared lowering core for the total-load push** — the one clause currency
//! every leg of the whole-spec lowering (`notes/vibes/logics/spectec-total-load.md`)
//! produces and consumes.
//!
//! A [`Clause`] is a rule-set clause in *data* form: `∀ metavars…. prem₀ ⟹ …
//! ⟹ d ⌜concl⌝`, where each premise is either a [`LowerPrem::Judgement`]
//! (a `d ⌜J⌝` antecedent — an inductive sub-derivation, discharged via
//! [`crate::metalogic::Premise::Derivation`]) or a [`LowerPrem::Side`] (an
//! arbitrary bool-typed HOL antecedent — a denoted condition, a syntactic
//! equation over encodings, real-nat arithmetic — discharged via
//! [`crate::metalogic::Premise::Side`]).
//!
//! Every metavariable is `Φ = nat`-typed and named through
//! [`encode::metavar_name`] (`st$v$<id>`), **including** the metavars a `Side`
//! antecedent mentions — that is what lets one ∀-bound variable serve both the
//! opaque judgement spine and a computable condition (the real-nat literal
//! embedding, `encode.rs` module docs).
//!
//! Soundness frame (see the design note): clauses only ever make `Derivable`
//! *under*-approximate — antecedents are at least as strong as the SpecTec
//! premises. A premise form that cannot be expressed yet is kept as an
//! **opaque judgement** ([`opaque`]): a tagged antecedent with no clauses
//! anywhere in the rule set, hence underivable — the rule *loads* faithfully
//! but cannot fire until the tag gains real clauses. Never drop a premise.
//!
//! ## Sorts, junk points, and the faithfulness contract
//!
//! Metavariables are untyped `Φ = nat` leaves, so clauses quantify over *all*
//! encodings — including **junk points**: terms that are the encoding of no
//! well-sorted SpecTec instance. The contract (see `encode.rs`,
//! *Faithfulness, not soundness*) is only about real points: a derivable
//! judgement whose body **is** the encoding of a well-sorted instance must be
//! SpecTec-derivable. Junk-point derivability (e.g. premise-free typing rules
//! firing on arbitrary encodings) is outside the contract. Three mechanisms
//! keep the real points honest:
//!
//! 1. **Pinned metavariables.** A metavariable with a bare (exact-sort)
//!    occurrence at a *pinning* position — one that survives verbatim into
//!    the encoded conclusion — cannot be ill-sorted at a real point: an
//!    ill-sorted value there makes the whole conclusion junk. (Positions
//!    lifted out of the conclusion — call arguments, identity-collapsed
//!    iteration bodies, `Dec` RHSs under result flattening — do **not** pin;
//!    nor do premises, whose relations can be sort-coarse: `ev.neq` is
//!    head-level, evaluator relations are sort-generic. Conclusion-`Cat`
//!    children lifted into `ev.cat` premises (`Mode::Concl`, Wave G) still
//!    pin *in value*: `ev.cat` embeds every element verbatim into the
//!    conclusion's result list, so an ill-sorted element still makes the
//!    conclusion junk.)
//! 2. **Sort guards / expansion** ([`sortguard`]). Every metavariable whose
//!    sort was lost entirely to the `Sub`-strip (no pinning bare occurrence)
//!    is either per-case expanded (`Dec` leg, nullary sorts) or carries an
//!    `ev.sort.*` guard premise — restoring exactly the lost constraint (up
//!    to payload junk, which point 1's argument absorbs).
//! 3. **Float (premise-only) metavariables** cannot mint false facts at real
//!    points. A clause `∀ȳ. P(x̄, ȳ) ⟹ J(x̄)` means `(∃ȳ P) ⟹ J` — exactly
//!    the SpecTec rule's reading — so the only risk is a **junk witness**:
//!    `P` derivable at junk `ȳ` where no real witness exists. Two cases: a
//!    float variable that is *sub-only* in its premises is sort-guarded by
//!    point 2 (this closes the real leak, where the premise was an equation
//!    or another constraint that junk satisfies vacuously — e.g.
//!    `Instr_ok/select-impl`'s `t = numtype`). A float variable with a bare
//!    premise occurrence sits at its exact sort inside the premise body; a
//!    junk witness then makes each such premise a junk *point* of its
//!    relation, and every clause chain deriving it treats the junk subterm
//!    parametrically (clauses are `∀`-quantified; guards only restrict to
//!    enumerated sorts; numeric side conditions only touch real-`nat`
//!    currency) — so re-instantiating the same derivation with any well-sorted
//!    inhabitant of the position's sort yields a real witness, and the SpecTec
//!    `∃` holds. This is a meta-level design argument (not machine-checked);
//!    its precondition — no clause discriminates junk from real *below* the
//!    sorted fringe — is exactly what points 1–2 maintain.

use covalence_core::{Result, Term};

use super::encode::{con, metavar_name, phi, tag};
use crate::init::ext::TermExt;
use crate::metalogic::RuleSet;

pub mod builtins;
pub mod decs;
pub mod else_;
pub mod evalrel;
pub mod flatten;
pub mod slice;
pub mod sortguard;
pub mod star;
pub mod total;
pub mod trace;

/// One antecedent of a lowered clause.
#[derive(Debug, Clone)]
pub enum LowerPrem {
    /// `d ⌜J⌝` — an inductive premise (any relation of the combined set:
    /// spec relations `rel.<R>`, function graphs `fn.<f>`, evaluator
    /// relations `ev.<op>…`, iteration stars `star.<site>`).
    Judgement(Term),
    /// An arbitrary bool-typed HOL antecedent over the clause's `st$v$…`
    /// metavariables, discharged directly by a side theorem.
    Side(Term),
}

/// A lowered clause in data form. `metavars` are raw SpecTec ids (unmangled),
/// outermost-first; every occurrence in `prems`/`concl` uses the mangled
/// [`encode::metavar`] free variable.
#[derive(Debug, Clone)]
pub struct Clause {
    pub metavars: Vec<String>,
    pub prems: Vec<LowerPrem>,
    pub concl: Term,
}

/// The clause's HOL term `∀ x…. prem₀ ⟹ … ⟹ d ⌜concl⌝`, with `d_apply`
/// supplied by the rule-set builder (the generalization of
/// `wasm::relation::clause_of` to mixed antecedents).
pub fn clause_term(c: &Clause, d_apply: &dyn Fn(&Term) -> Result<Term>) -> Result<Term> {
    let mut body = d_apply(&c.concl)?;
    for p in c.prems.iter().rev() {
        let ant = match p {
            LowerPrem::Judgement(j) => d_apply(j)?,
            LowerPrem::Side(s) => s.clone(),
        };
        body = ant.imp(body)?;
    }
    for mv in c.metavars.iter().rev() {
        body = body.forall(&metavar_name(mv), phi())?;
    }
    Ok(body)
}

/// A [`RuleSet`] over an explicit clause list (clause `i` = `clauses[i]`).
pub fn rule_set_of(clauses: Vec<Clause>) -> RuleSet<'static> {
    RuleSet::new(phi(), move |d| {
        clauses.iter().map(|c| clause_term(c, d)).collect()
    })
}

/// An **opaque premise**: `d ⌜opaque.<reason> body⌝` where the tag
/// `opaque.<reason>` has no clauses in any rule set produced by this module
/// tree — underivable by construction, so a rule carrying it loads faithfully
/// (antecedent stronger than the original premise) but cannot fire. Reported,
/// never silent.
pub fn opaque(reason: &str, body: Term) -> Result<Term> {
    tag(format!("opaque.{reason}"), body)
}

/// The canonical judgement body of a **function-graph** relation instance:
/// relation tag `fn.<f>`, body = the `app`-spine of the encoded arguments
/// followed by the encoded result (zero-arg functions: just the result).
///
/// Every leg (condition flattening, Dec lowering, drivers) MUST build
/// function-graph judgements through this one constructor so tags and
/// argument order never diverge.
pub fn fn_graph(f: &str, args: &[Term], result: &Term) -> Result<Term> {
    let mut spine = con(format!("fnargs.{}", args.len()));
    for a in args {
        spine = super::encode::app(spine, a.clone())?;
    }
    spine = super::encode::app(spine, result.clone())?;
    tag(format!("fn.{f}"), spine)
}

/// What flattening one condition / expression produced besides the term:
/// premises to prepend and fresh metavars the clause must additionally
/// quantify (appended after the rule's own metavars, in first-allocated
/// order).
#[derive(Debug, Clone, Default)]
pub struct Flattened {
    pub prems: Vec<LowerPrem>,
    pub new_metavars: Vec<String>,
}

/// The seam between clause producers (rule lowering, `decs`, `star`) and the
/// condition/expression flattener (`flatten`). Implementations must uphold the
/// soundness frame: never weaken — a condition that cannot be expressed
/// becomes an [`opaque`] premise, not a dropped one.
///
/// The default-method surface is what lets the stateful real flattener
/// ([`flatten::Flattener`]) coordinate the **numeric-metavar discipline** and
/// the shared **evaluator-clause pool** with clause producers behind one `dyn`
/// seam; stateless flatteners ([`PureFlattener`]) get sound no-op behaviour.
pub trait CondFlattener {
    /// Flatten a boolean side-condition into premises.
    fn cond(&mut self, cond: &covalence_spectec::ast::SpecTecExp) -> Result<Flattened>;
    /// Flatten an expression in judgement position: its encoded term plus
    /// whatever premises evaluating it requires.
    fn expr(&mut self, e: &covalence_spectec::ast::SpecTecExp) -> Result<(Term, Flattened)>;
    /// Flatten an expression in **result** position (a `Dec` clause's RHS):
    /// like [`CondFlattener::expr`], but structural operators
    /// (`Dot`/`Idx`/`Len`/`Proj`/`Uncase`/`Unopt`/`Cat`) may additionally be
    /// evaluated through `ev.*` premises, so graph conclusions carry the
    /// *value* of an accessor body instead of a coarse operator spine (the
    /// store-accessor unblocking — see [`decs`]' docs). Default: plain
    /// [`CondFlattener::expr`] (sound — the result stays a coarse spine).
    fn expr_result(&mut self, e: &covalence_spectec::ast::SpecTecExp) -> Result<(Term, Flattened)> {
        self.expr(e)
    }
    /// Begin a new rule/clause: reset per-rule state and pre-scan `exprs` for
    /// the numeric-metavar discipline. Producers MUST call this once before
    /// `cond`/`expr` for a new clause. Default: no-op (stateless flatteners).
    fn begin_rule(&mut self, _exprs: &[&covalence_spectec::ast::SpecTecExp]) {}
    /// Whether this flattener applies the numeric-metavar **wrap** itself in
    /// `expr` spines. When `true`, clause producers must NOT wrap again (the
    /// wrap is applied exactly once per spine, by whichever leg builds it).
    fn wraps_numeric(&self) -> bool {
        false
    }
    /// Put a metavariable under the numeric discipline for the current rule
    /// (used by producers introducing numeric-currency vars of their own, e.g.
    /// the star leg's `ListN` bound metavars). Default: no-op.
    fn mark_numeric(&mut self, _id: &str) {}
    /// Whether a metavariable is under the numeric discipline for the current
    /// rule. Default: `false`.
    fn is_numeric(&self, _id: &str) -> bool {
        false
    }
    /// Request an evaluator-clause family by dedup `key`. A flattener managing
    /// a shared pool records the clauses internally (deduplicated, drained by
    /// the integration layer) and returns `[]`; the default builds and returns
    /// them for the producer to append locally.
    fn request_ev(
        &mut self,
        _key: &str,
        build: &dyn Fn() -> Result<Vec<Clause>>,
    ) -> Result<Vec<Clause>> {
        build()
    }
}

/// Baseline flattener: `expr` is the pure encoding with no premises;
/// `cond` is the [`opaque`] escape hatch (the clause loads faithfully but the
/// condition antecedent is underivable until a real flattener replaces it).
#[derive(Debug, Default)]
pub struct PureFlattener;

impl CondFlattener for PureFlattener {
    fn cond(&mut self, cond: &covalence_spectec::ast::SpecTecExp) -> Result<Flattened> {
        let body = super::encode::encode_exp(cond)?;
        Ok(Flattened {
            prems: vec![LowerPrem::Judgement(opaque("cond", body)?)],
            new_metavars: Vec::new(),
        })
    }

    fn expr(&mut self, e: &covalence_spectec::ast::SpecTecExp) -> Result<(Term, Flattened)> {
        Ok((super::encode::encode_exp(e)?, Flattened::default()))
    }
}
