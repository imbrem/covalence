//! **General schema-database Metamath replay** — "a Metamath database IS a
//! logic". This generalises the prop-specific [`crate::metalogic::mm_replay`]
//! (which hardcodes set.mm's `ax-1`/`ax-2`/`ax-mp`) to an **arbitrary**
//! [`metamath::Database`](crate::metamath::Database): from the database's
//! assertions we build a data-driven [`RuleSet`], and replay a *verified,
//! untrusted* normal proof into a kernel-constructed
//! `⊢ Derivable_L ⌜S⌝` (= [`metalogic::derivable`](crate::metalogic::derivable)
//! over the encoded syntax). One function, [`replay_db`], replays *any* such
//! database — three unrelated logics in the tests below ride the same code.
//!
//! Same "construct, don't trust" discipline as `mm_replay`: the Metamath
//! verifier's say-so is **not** trusted for the HOL theorem; every step is
//! re-checked through the kernel, and the result lands in *pure derivability
//! over encoded syntax* — **no denotation `⟦S⟧`, no observer, no oracle**. The
//! returned `Thm` is `has_no_obs()`.
//!
//! # The encoding: an uninterpreted free term algebra (former-structured)
//!
//! The carrier is `Φ = `[`Type::nat`]`()`. We encode a Metamath expression's
//! *symbol sequence* (its body — the typecode is ignored; derivability ranges
//! over formula bodies) as a HOL term over three families of **uninterpreted
//! free variables**:
//!
//! - one binary `concat : nat → nat → nat`, `Term::free("mm$concat", …)`,
//!   applied to two encoded sub-terms;
//! - one constant `mm$c$<tok> : nat` per Metamath **constant symbol** `tok`;
//! - each Metamath **variable** (metavariable) `v` is the plain free var
//!   `Term::free(v, nat)`.
//!
//! [`db.is_variable`](crate::metamath::Database::is_variable) picks
//! variable-vs-constant. The folding of a token list into nested `concat`s is
//! done **former-structured**: a body is parsed against the database's
//! *syntactic formers* (the non-`|-` assertions — `wff`/`term`/… productions)
//! into a tree, and each former-application node `f(a₀,…)` is encoded as
//! `encode(former-body, vᵢ ↦ enc(aᵢ))` — i.e. the former's own body
//! right-folded with its metavars filled by the *encoded sub-trees*. A bare
//! variable body is its metavariable leaf. [`Parser`] drives this; [`encode`]
//! does the right-fold of one former body.
//!
//! ## Why substitution = `all_elim` (the key idea)
//!
//! Each `|-` assertion becomes one [`Closed_L`](crate::metalogic::closed_conj)
//! clause, `∀v₀ … v_{m-1}. (premises ⟹)? d ⌜concl⌝`, with the metavariables
//! `vᵢ` ∀-bound (outermost first). A Metamath *substitution-instance* of that
//! schema is then **exactly** the kernel's [`Thm::all_elim`]: applying the
//! clause to argument terms substitutes `vᵢ := enc(argᵢ)` capture-avoidingly.
//!
//! This works because `concat` and the `mm$c$…` constants are *uninterpreted*
//! free vars and the metavariables are *variables*: HOL's capture-avoiding
//! substitution of `enc(arg)` for `v` in `enc(schematic)` is **syntactically**
//! `enc(schematic[v := arg])` — there is no β/δ-redex to fire and nothing to
//! normalise; `all_elim` *is* Metamath substitution on the nose. The one
//! subtlety the *former-structured* fold resolves: a flat token fold would make
//! a literal axiom conclusion (e.g. `( ph -> ( ps -> ph ) )`) and the same
//! expression reached by substituting a former-built argument into a schema's
//! metavar disagree on `concat`-associativity (one spreads the inner parens
//! across the fold, the other nests them as a sub-tree). Parsing *both* against
//! the formers makes every expression — literal or substituted — the **same**
//! compact tree, so `enc(actual-premise) = enc(schema)[v := enc(arg)]` holds on
//! the nose and `imp_elim`/`all_elim` line up.
//!
//! # Scope / over-approximation
//!
//! - **Typecodes and `$d`** are over-approximated: clauses quantify each
//!   metavariable over *all* of `Φ` (every `nat`) rather than the typecode's
//!   sub-language, and `$d` disjointness is not enforced. This is **sound for
//!   the existence / construct direction** we land in (a larger rule set only
//!   proves *more* derivable formulas; we only ever *construct* a witness for
//!   the specific instance the untrusted proof names).
//! - **Both proof encodings** are replayed: the proof is decoded to the uniform
//!   [`crate::metamath::ProofStep`] sequence, and a compressed proof's `Z`-saves
//!   / heap back-references drive a `Slot` heap alongside the stack, so a re-used
//!   sub-proof is a cheap re-push (its sharing is preserved, no re-expansion).
//! - **Syntactic formers** (`wff`/`term`/… assertions) are *grammar*, not
//!   derivability rules: they build [`Slot::Wff`] terms during replay but
//!   contribute **no** clause to the rule set.

use std::collections::HashMap;

use covalence_core::{Error, Result, Term, Thm, Type};

use crate::init::ext::TermExt;
use crate::metamath::expr::body_of;
use crate::metamath::{Assertion, Database, Expr, Statement};

use super::{RuleSet, conj, conj_thms, derivable};

// ============================================================================
// Errors
// ============================================================================

fn replay_err(msg: impl Into<String>) -> Error {
    Error::ConnectiveRule(format!("mm-db-replay: {}", msg.into()))
}

/// The reified-syntax carrier `Φ` for the free term algebra: plain `nat`.
fn phi() -> Type {
    Type::nat()
}

// ============================================================================
// The free-term-algebra encoding `enc(·)`
// ============================================================================

/// The uninterpreted binary former `concat : nat → nat → nat`.
fn concat_fn() -> Term {
    Term::free("mm$concat", Type::fun(phi(), Type::fun(phi(), phi())))
}

/// `concat(a, b)` — two applications of the uninterpreted [`concat_fn`].
fn concat(a: Term, b: Term) -> Result<Term> {
    concat_fn().apply(a)?.apply(b)
}

/// The HOL free-variable name for a Metamath **metavariable** `tok`. Namespaced
/// (`mm$v$<tok>`) so it can never collide with the impredicative engine's own
/// reserved variable name `d` (the predicate `d : Φ→bool` in
/// `Derivable_L A := ∀d. Closed_L d ⟹ d A`) — a Metamath setvar literally named
/// `d` would otherwise appear as both `nat` (metavar) and `nat→bool` (predicate)
/// in one term, which the kernel rejects ("free variable `d` declared at two
/// different types"). Used at *every* metavar site (leaf encoding, clause
/// ∀-binders, the `$f` float slot) so they stay consistent.
pub fn mv(tok: &str) -> String {
    format!("mm$v${tok}")
}

/// A leaf resolver: a Metamath **variable** `tok` → `Term::free(mm$v$<tok>, nat)`
/// (a metavariable, to be ∀-bound in its clause); any other token is treated as
/// a **constant** → the uninterpreted constant `mm$c$<tok> : nat`.
fn leaf(db: &Database, tok: &str) -> Term {
    if db.is_variable(tok) {
        Term::free(mv(tok), phi())
    } else {
        Term::free(format!("mm$c${tok}"), phi())
    }
}

/// Right-fold one former body `[s₁,…,sₙ]` into `concat(enc s₁, concat(enc s₂, …
/// enc sₙ))` (a singleton is just `enc s₁`). `resolve` maps each token to its
/// term — a former-application's metavars to the encoded sub-trees, every other
/// token to its [`leaf`].
pub fn encode(body: &[impl AsRef<str>], resolve: &dyn Fn(&str) -> Result<Term>) -> Result<Term> {
    let mut iter = body.iter().rev();
    let last = iter
        .next()
        .ok_or_else(|| replay_err("cannot encode an empty symbol sequence"))?;
    let mut acc = resolve(last.as_ref())?;
    for tok in iter {
        acc = concat(resolve(tok.as_ref())?, acc)?;
    }
    Ok(acc)
}

// ============================================================================
// The former grammar + parser (compact, former-structured encoding)
// ============================================================================

/// A syntactic former (a non-`|-` assertion = a grammar production): its result
/// typecode, the body pattern, and the metavar→typecode map of its floats.
#[derive(Clone)]
struct Former {
    /// e.g. `wff` / `term`.
    typecode: String,
    /// The conclusion body tokens (metavar tokens mixed with literal constants).
    body: Vec<String>,
    /// `(var, typecode)` for each `$f` float, in frame order.
    floats: Vec<(String, String)>,
}

/// The database's syntactic-former grammar (productions for `wff`/`term`/…),
/// driving the compact, former-structured encoding of any body.
pub struct Parser<'a> {
    db: &'a Database,
    formers: Vec<Former>,
    /// `typecode → indices into `formers`` (in database order). Lets [`parse`]
    /// consider only the productions of the requested typecode instead of
    /// scanning *all* formers (set.mm has ~1400 of them; without the index every
    /// `parse(tc, …)` was O(all formers)). Database order is preserved within a
    /// typecode, so first-match semantics are unchanged.
    by_typecode: HashMap<String, Vec<usize>>,
    /// The distinct former result-typecodes in database-first-seen order
    /// (precomputed candidate start symbols for a whole-`|-`-body parse).
    typecodes: Vec<String>,
    /// Every declared `$f` floating hypothesis's `var → typecode`, gathered from
    /// the *whole* database (not just former frames — a variable's `$f` may be
    /// introduced for a `|-` assertion, e.g. demo0's `s`).
    var_tc: HashMap<String, String>,
}

impl<'a> Parser<'a> {
    /// Build the parser from a database: every non-`|-` assertion is a former.
    pub fn new(db: &'a Database) -> Self {
        let formers: Vec<Former> = db
            .assertions()
            .filter(|a| a.conclusion.typecode() != "|-")
            .filter_map(|a| {
                let body = body_of(&a.conclusion)?;
                Some(Former {
                    typecode: a.conclusion.typecode().to_string(),
                    body: body.iter().map(|s| s.to_string()).collect(),
                    floats: a
                        .frame
                        .floats
                        .iter()
                        .map(|f| (f.var.clone(), f.typecode.clone()))
                        .collect(),
                })
            })
            .collect();
        // Index formers by their result typecode (database order preserved) and
        // collect the distinct typecodes in first-seen order.
        let mut by_typecode: HashMap<String, Vec<usize>> = HashMap::new();
        let mut typecodes: Vec<String> = Vec::new();
        for (i, f) in formers.iter().enumerate() {
            let entry = by_typecode.entry(f.typecode.clone());
            if matches!(entry, std::collections::hash_map::Entry::Vacant(_)) {
                typecodes.push(f.typecode.clone());
            }
            entry.or_default().push(i);
        }
        let mut var_tc = HashMap::new();
        for stmt in db.statements() {
            if let Statement::Float(f) = stmt {
                var_tc.insert(f.var.clone(), f.typecode.clone());
            }
        }
        Parser {
            db,
            formers,
            by_typecode,
            typecodes,
            var_tc,
        }
    }

    /// Encode an expression *body* compactly under this grammar.
    ///
    /// If the statement's typecode has a production (some former concludes it,
    /// e.g. `wff`/`term`), the body is parsed *strictly* as one expression of
    /// that typecode. A `|-` body (the provability layer) has **no** former
    /// production, so it is encoded *greedily* ([`encode_greedy`]): maximal
    /// syntactic sub-expressions are parsed compactly and every other token is a
    /// literal constant — which still makes a `|-` schema's metavar positions
    /// (single typed-variable leaves) line up with substituted instances.
    pub fn encode_expr(&self, e: &Expr) -> Result<Term> {
        let body = body_of(e).ok_or_else(|| replay_err("malformed statement (no body)"))?;
        let toks: Vec<&str> = body.iter().map(|s| s.as_str()).collect();
        if self.by_typecode.contains_key(e.typecode()) {
            let (term, rest) = self.parse(e.typecode(), &toks)?;
            if !rest.is_empty() {
                return Err(replay_err(format!(
                    "trailing symbols after parsing `{}`",
                    e.render()
                )));
            }
            return Ok(term);
        }
        // No production for this typecode (the `|-` provability layer). First
        // try to parse the *whole* body as a single expression of some former
        // typecode (set.mm-style: a `|-` body is one `wff`); the parenthesised
        // grammars are unambiguous, so a full consume is canonical. Otherwise
        // fall back to greedy token-by-token encoding (raw `|-` bodies with no
        // top-level production, e.g. the GROUP theory's `( a = a )`).
        for tc in &self.typecodes {
            if let Ok((term, rest)) = self.parse(tc, &toks)
                && rest.is_empty()
            {
                return Ok(term);
            }
        }
        self.encode_greedy(&toks)
    }

    /// Greedily encode a token sequence with no top-level production: walk left
    /// to right, parsing a maximal syntactic sub-expression where one starts and
    /// otherwise taking the token as a literal constant leaf; right-fold the
    /// resulting node sequence with [`concat`].
    fn encode_greedy(&self, toks: &[&str]) -> Result<Term> {
        let mut nodes: Vec<Term> = Vec::new();
        let mut rest = toks;
        while let Some((head, tail)) = rest.split_first() {
            if let Some((node, after)) = self.parse_any(rest)? {
                nodes.push(node);
                rest = after;
            } else {
                nodes.push(leaf(self.db, head));
                rest = tail;
            }
        }
        // Right-fold the nodes into nested `concat`s.
        let mut iter = nodes.into_iter().rev();
        let mut acc = iter
            .next()
            .ok_or_else(|| replay_err("cannot encode an empty `|-` body"))?;
        for node in iter {
            acc = concat(node, acc)?;
        }
        Ok(acc)
    }

    /// Try to parse a *non-leaf* syntactic sub-expression (any former typecode)
    /// off the front of `toks`. Returns `None` if none applies (the caller then
    /// treats the head as a literal `|-`-structural token). A bare typed
    /// variable is intentionally *not* matched here — it is taken as a leaf by
    /// the caller, which is the right granularity for a `|-` schema's metavars.
    fn parse_any<'t>(&self, toks: &'t [&'t str]) -> Result<Option<(Term, &'t [&'t str])>> {
        for f in &self.formers {
            if let Some((term, rest)) = self.try_former(f, toks)? {
                return Ok(Some((term, rest)));
            }
        }
        Ok(None)
    }

    /// Parse one expression of typecode `tc` off the front of `toks`, returning
    /// the compact encoding and the remaining tokens. A lone metavariable of
    /// typecode `tc` is a leaf; otherwise the longest-matching former applies.
    fn parse<'t>(&self, tc: &str, toks: &'t [&'t str]) -> Result<(Term, &'t [&'t str])> {
        // A bare metavariable of this typecode (its `$f` typecode must match).
        if let Some((head, rest)) = toks.split_first()
            && self.db.is_variable(head)
            && self.var_typecode(head) == Some(tc)
        {
            return Ok((leaf(self.db, head), rest));
        }
        // Try each former whose result typecode is `tc` (via the typecode index,
        // database order preserved); first full match wins.
        if let Some(idxs) = self.by_typecode.get(tc) {
            for &i in idxs {
                if let Some((term, rest)) = self.try_former(&self.formers[i], toks)? {
                    return Ok((term, rest));
                }
            }
        }
        Err(replay_err(format!(
            "cannot parse a `{tc}` from `{}`",
            toks.join(" ")
        )))
    }

    /// Attempt to match former `f` against the front of `toks`. On success
    /// returns the compact encoding (the former body re-folded with its
    /// metavars filled by the parsed sub-trees) and the rest.
    fn try_former<'t>(
        &self,
        f: &Former,
        mut toks: &'t [&'t str],
    ) -> Result<Option<(Term, &'t [&'t str])>> {
        let mut args: HashMap<&str, Term> = HashMap::new();
        for pat in &f.body {
            if let Some((_, sub_tc)) = f.floats.iter().find(|(v, _)| v == pat) {
                // A metavar position: recursively parse a sub-expression.
                let Ok((sub, rest)) = self.parse(sub_tc, toks) else {
                    return Ok(None);
                };
                args.insert(pat.as_str(), sub);
                toks = rest;
            } else {
                // A literal constant: it must match the next input token.
                match toks.split_first() {
                    Some((head, rest)) if head == pat => toks = rest,
                    _ => return Ok(None),
                }
            }
        }
        // Re-fold the former body with metavars → their parsed encodings.
        let resolve = |tok: &str| -> Result<Term> {
            Ok(match args.get(tok) {
                Some(t) => t.clone(),
                None => leaf(self.db, tok),
            })
        };
        let term = encode(&f.body, &resolve)?;
        Ok(Some((term, toks)))
    }

    /// The `$f` typecode declared for variable `var`, if any.
    fn var_typecode(&self, var: &str) -> Option<&str> {
        self.var_tc.get(var).map(String::as_str)
    }
}

/// Encode an assertion's *conclusion body* compactly (the public helper the
/// tests use to state the expected `Derivable_L ⌜concl⌝`).
pub fn encode_conclusion(db: &Database, assertion: &Assertion) -> Result<Term> {
    Parser::new(db).encode_expr(&assertion.conclusion)
}

// ============================================================================
// `RuleSet`-from-`Database`
// ============================================================================

/// A precompiled `|-` clause: its metavariables (∀-binders, in frame order),
/// the encoded essential premises, and the encoded conclusion. All `enc(·)`
/// terms are the [`Parser`]'s compact encodings; the clause body is
/// rebuilt for each `d ⌜·⌝` applier the engine passes (bound `d`, then
/// `d := pred`).
#[derive(Clone)]
struct Clause {
    float_vars: Vec<String>,
    ess_encs: Vec<Term>,
    concl_enc: Term,
}

impl Clause {
    /// Build this clause's `bool`-typed body for a given `d ⌜·⌝` applier:
    /// `∀float_vars. (⋀ d ⌜ess⌝ ⟹)? d ⌜concl⌝` (binders outermost-first).
    fn build(&self, d_apply: &dyn Fn(&Term) -> Result<Term>) -> Result<Term> {
        let mut body = if self.ess_encs.is_empty() {
            d_apply(&self.concl_enc)?
        } else {
            let prems: Vec<Term> = self
                .ess_encs
                .iter()
                .map(|e| d_apply(e))
                .collect::<Result<_>>()?;
            conj(prems)?.imp(d_apply(&self.concl_enc)?)?
        };
        // Bind float_vars[0] OUTERMOST, so `all_elim(arg0)` strips it first.
        // Bind the *namespaced* metavar name (matches `leaf`'s encoding).
        for v in self.float_vars.iter().rev() {
            body = body.forall(&mv(v), phi())?;
        }
        Ok(body)
    }
}

/// Encode one `|-` assertion as a [`Clause`] (the metavariable binders + encoded
/// premises + encoded conclusion). Returns `None` for a non-`|-` assertion (a
/// syntactic former — grammar, not a rule) or if the body fails to encode (which
/// cannot happen on a verified database; a missing clause only weakens the rule
/// set, sound for the construct direction).
fn clause_from(parser: &Parser, a: &Assertion) -> Option<Clause> {
    if a.conclusion.typecode() != "|-" {
        return None;
    }
    let float_vars: Vec<String> = a.frame.floats.iter().map(|f| f.var.clone()).collect();
    let ess_encs: Result<Vec<Term>> = a
        .frame
        .essentials
        .iter()
        .map(|h| parser.encode_expr(&h.expr))
        .collect();
    let (Ok(ess_encs), Ok(concl_enc)) = (ess_encs, parser.encode_expr(&a.conclusion)) else {
        return None;
    };
    Some(Clause {
        float_vars,
        ess_encs,
        concl_enc,
    })
}

/// Collect the database's `|-` clauses (one per `|-` assertion, in database
/// order) and a `label → clause index` map. Syntactic formers (non-`|-`
/// assertions) are skipped — they are grammar, not derivability rules.
fn collect_clauses(db: &Database) -> (Vec<Clause>, HashMap<String, usize>) {
    let parser = Parser::new(db);
    collect_clauses_with(&parser, db.assertions())
}

/// Like [`collect_clauses`] but over a pre-built [`Parser`] and an explicit
/// assertion iterator (so the caller controls the one-per-database parser build).
fn collect_clauses_with<'a>(
    parser: &Parser,
    assertions: impl Iterator<Item = &'a Assertion>,
) -> (Vec<Clause>, HashMap<String, usize>) {
    let mut clauses = Vec::new();
    let mut index = HashMap::new();
    for a in assertions {
        if let Some(c) = clause_from(parser, a) {
            index.insert(a.label.clone(), clauses.len());
            clauses.push(c);
        }
    }
    (clauses, index)
}

/// Collect the `|-` clauses **scoped to one theorem's proof** — exactly the `|-`
/// assertions its proof references (directly), in first-use order — plus the
/// `label → clause index` map. This is the *performance* path: the resulting
/// rule set's `Closed_L` has only the lemmas the proof actually uses (tens),
/// not the whole database (tens of thousands), so `derivable`/`nth_conjunct`
/// stay cheap. The logic is a sub-rule-set `L' ⊆ L` of the database; by
/// monotonicity (`metalogic::transport_db`) `Derivable_L' ⟹ Derivable_L`.
fn scoped_clauses(
    db: &Database,
    parser: &Parser,
    steps: &[crate::metamath::ProofStep],
) -> Result<(Vec<Clause>, HashMap<String, usize>)> {
    let mut clauses = Vec::new();
    let mut index = HashMap::new();
    for step in steps {
        let crate::metamath::ProofStep::Label(label) = step else {
            continue;
        };
        if index.contains_key(label) {
            continue;
        }
        if let Some(Statement::Assert(a)) = db.statement_by_label(label) {
            if let Some(c) = clause_from(parser, a) {
                index.insert(label.clone(), clauses.len());
                clauses.push(c);
            }
        }
    }
    Ok((clauses, index))
}

/// Assemble a [`RuleSet`] (carrier `Φ = nat`) from a list of clauses.
fn clauses_to_ruleset(clauses: Vec<Clause>) -> RuleSet<'static> {
    RuleSet::new(phi(), move |d_apply| {
        clauses.iter().map(|c| c.build(d_apply)).collect()
    })
}

/// Public, read-only view of one `|-` clause of a database's rule set — the
/// per-rule data [`crate::metalogic::transport_db`] needs to state and discharge
/// a *rule-simulation* obligation generically (without re-parsing the database).
///
/// The fields are the same compact encodings [`rule_set`] uses: the metavariable
/// names (∀-binders, frame order), the encoded essential premises, and the
/// encoded conclusion. [`build_body`](ClauseInfo::build_body) rebuilds the
/// `bool`-typed clause for any `d ⌜·⌝` applier — exactly the term a transport
/// `clause_sim` must prove at `d := pred`.
#[derive(Clone, Debug)]
pub struct ClauseInfo {
    /// The clause's metavariables, outermost-`∀` first.
    pub float_vars: Vec<String>,
    /// The encoded essential premises (`d`-of-these are the clause antecedents).
    pub ess_encs: Vec<Term>,
    /// The encoded conclusion (`d`-of-this is the clause consequent).
    pub concl_enc: Term,
}

impl ClauseInfo {
    /// The carrier type `Φ = nat` these encodings live over.
    pub fn phi() -> Type {
        phi()
    }

    /// Rebuild this clause's `bool` body for a `d ⌜·⌝` applier — the same layout
    /// [`rule_set`] hands the engine: `∀float_vars. (⋀ d ⌜ess⌝ ⟹)? d ⌜concl⌝`.
    pub fn build_body(&self, d_apply: &dyn Fn(&Term) -> Result<Term>) -> Result<Term> {
        Clause {
            float_vars: self.float_vars.clone(),
            ess_encs: self.ess_encs.clone(),
            concl_enc: self.concl_enc.clone(),
        }
        .build(d_apply)
    }
}

/// The database's `|-` clauses (one per `|-` assertion, database order), as the
/// public [`ClauseInfo`] view, paired with the `label → clause index` map.
/// Same data [`rule_set`] is built from — the bridge for generic transport.
pub fn clause_infos(db: &Database) -> (Vec<ClauseInfo>, HashMap<String, usize>) {
    let (clauses, index) = collect_clauses(db);
    let infos = clauses
        .into_iter()
        .map(|c| ClauseInfo {
            float_vars: c.float_vars,
            ess_encs: c.ess_encs,
            concl_enc: c.concl_enc,
        })
        .collect();
    (infos, index)
}

/// Build the [`RuleSet`] for a Metamath database: carrier `Φ = nat`, one clause
/// per `|-` assertion (database order). This *is* the logic the database
/// defines.
pub fn rule_set(db: &Database) -> RuleSet<'static> {
    clauses_to_ruleset(collect_clauses(db).0)
}

// ============================================================================
// The replay
// ============================================================================

/// One slot on the replay stack (and the compressed-proof heap). `Clone` is
/// what lets a `Save`/`Heap` re-use a saved sub-result **without recomputation**
/// — `Term` and `Thm` are both cheap `Arc`-backed clones, so the compressed
/// proof's sharing is preserved (no exponential re-expansion).
#[derive(Clone)]
enum Slot {
    /// An encoded `Φ` term — a `wff`/`term`/… expression (or a `$f` variable).
    Wff(Term),
    /// `Γ ⊢ Derivable_L ⌜X⌝` — a re-derived derivability theorem (its essential
    /// hypotheses surface as `Γ`).
    Proved(Thm),
}

/// **Replay a verified, normal Metamath proof, re-deriving
/// `⊢ Derivable_L ⌜S⌝` in the kernel** for the database's logic `L`.
///
/// `assertion` must be a `$p` theorem whose proof
/// [`crate::metamath::verify`] accepts (the caller verifies it; the replay
/// re-derives the HOL theorem independently). Returns a genuine, oracle-free
/// kernel theorem whose conclusion is `derivable(rule_set(db), enc(S))`; any
/// **essential hypotheses** of the assertion appear as the theorem's
/// hypotheses `Derivable_L ⌜hyp⌝ ⊢ Derivable_L ⌜S⌝`.
///
/// Both proof encodings are handled: the proof is decoded into the uniform
/// [`crate::metamath::ProofStep`] sequence ([`crate::metamath::proof_steps`]),
/// driving a `stack` plus a compressed-proof `heap`. A `Save` step clones the
/// top stack slot onto the heap; a `Heap(i)` step re-pushes `heap[i]` — so a
/// re-used sub-proof is a cheap `Arc`-clone re-push, **not** a recomputation,
/// preserving the compressed proof's sharing (no exponential re-expansion).
pub fn replay_db(db: &Database, assertion: &Assertion) -> Result<Thm> {
    let parser = Parser::new(db);
    let steps = crate::metamath::proof_steps(db, assertion)
        .map_err(|e| replay_err(format!("decoding proof: {e}")))?;
    let (clauses, clause_index) = collect_clauses_with(&parser, db.assertions());
    let rs = clauses_to_ruleset(clauses);
    replay_with(db, &parser, assertion, &steps, &rs, &clause_index)
}

/// **Derive that a single named theorem is derivable — the fast, on-demand
/// path.** Get `⊢ Derivable_L' ⌜T⌝` where `L'` is the sub-rule-set of exactly the
/// `|-` assertions `T`'s proof references (so `Closed_L'` is small and replay is
/// cheap — unlike [`replay_db`], whose rule set is the *whole* database). `L' ⊆
/// L`, so `metalogic::transport_db` lifts the result to the full database logic
/// when wanted. Shares all replay machinery with [`replay_db`]; only the rule
/// set is scoped.
///
/// This builds a fresh [`Parser`] for the one call. To derive **many** theorems
/// from one database, build the parser once and use [`derive_theorem_with`] —
/// [`Parser::new`] is O(database size) and would otherwise dominate the import.
pub fn derive_theorem(db: &Database, label: &str) -> Result<Thm> {
    let parser = Parser::new(db);
    derive_theorem_with(db, &parser, label)
}

/// [`derive_theorem`] over a **pre-built [`Parser`]** — the path for importing
/// *many* theorems from one database. [`Parser::new`] is O(database size) (it
/// scans every assertion/float to build the former grammar + `var → typecode`
/// map); building it once and threading it across all theorems removes that
/// per-theorem scan (on set.mm, ~4.6 ms × 47k theorems ≈ minutes of pure
/// rebuilding). The parser is read-only and `Sync`, so the parallel import
/// shares one `&Parser` across worker threads. Otherwise identical to
/// [`derive_theorem`].
pub fn derive_theorem_with(db: &Database, parser: &Parser, label: &str) -> Result<Thm> {
    let assertion = match db.statement_by_label(label) {
        Some(Statement::Assert(a)) if a.proof.is_some() => a,
        Some(Statement::Assert(_)) => {
            return Err(replay_err(format!("`{label}` is an axiom (no proof to replay)")));
        }
        _ => return Err(replay_err(format!("`{label}` is not a theorem of the database"))),
    };
    let steps = crate::metamath::proof_steps(db, assertion)
        .map_err(|e| replay_err(format!("decoding proof: {e}")))?;
    let (clauses, clause_index) = scoped_clauses(db, parser, &steps)?;
    let rs = clauses_to_ruleset(clauses);
    replay_with(db, parser, assertion, &steps, &rs, &clause_index)
}

/// The shared replay loop: drive `assertion`'s proof steps against the supplied
/// rule set `rs` (with its `label → clause index` map), re-deriving
/// `⊢ Derivable_L ⌜S⌝`. Both [`replay_db`] (full database rule set) and
/// [`derive_theorem`] (proof-scoped rule set) call this — the only difference is
/// which clauses `rs`/`clause_index` carry.
fn replay_with(
    db: &Database,
    parser: &Parser,
    assertion: &Assertion,
    steps: &[crate::metamath::ProofStep],
    rs: &RuleSet,
    clause_index: &HashMap<String, usize>,
) -> Result<Thm> {
    if assertion.proof.is_none() {
        return Err(replay_err("assertion has no proof to replay"));
    }

    // Build the rule-set's `{Closed d} ⊢ Closed d` assumption and *all* its
    // conjuncts ONCE per theorem (was: rebuilt on every `|-` step in
    // `derive_clause` — `closed_for_var` + `assume` + O(k) `nth_conjunct`,
    // i.e. O(S·D) big-term work). Now each `|-` step just clones the cached
    // conjunct (an `Arc` bump) and `all_elim`s its args.
    let clause_ctx = ClauseCtx::new(rs)?;

    let mut stack: Vec<Slot> = Vec::new();
    let mut heap: Vec<Slot> = Vec::new();

    for step in steps {
        match step {
            crate::metamath::ProofStep::Label(label) => {
                let slot = apply_label(db, rs, clause_index, &clause_ctx, parser, label, &mut stack)?;
                stack.push(slot);
            }
            crate::metamath::ProofStep::Save => {
                // `Z` — clone the top of stack onto the sharing heap.
                let top = stack
                    .last()
                    .ok_or_else(|| replay_err("`Z` save with an empty stack"))?
                    .clone();
                heap.push(top);
            }
            crate::metamath::ProofStep::Heap(idx) => {
                // Re-push a saved sub-result: a cheap clone, never a recompute.
                let slot = heap
                    .get(*idx)
                    .ok_or_else(|| replay_err(format!("heap backreference {idx} out of range")))?
                    .clone();
                stack.push(slot);
            }
        }
    }

    match stack.len() {
        1 => match stack.pop().expect("len checked") {
            Slot::Proved(thm) => {
                // Sanity: the re-derived theorem is the derivability of the
                // claimed conclusion's encoding. Reuse the already-built `parser`
                // (not `encode_conclusion`, which would `Parser::new` the whole
                // database again) and the cached `Closed d` (not `derivable`,
                // which would re-lay-out the clauses) — `Derivable_L A` is just
                // `∀d. closed_t ⟹ d A`.
                let concl_enc = parser.encode_expr(&assertion.conclusion)?;
                let want = clause_ctx
                    .closed_t
                    .clone()
                    .imp(clause_ctx.d.clone().apply(concl_enc)?)?
                    .forall("d", clause_ctx.pred_ty.clone())?;
                if thm.concl() != &want {
                    return Err(replay_err(format!(
                        "replayed conclusion does not match the claimed `{}`",
                        crate::metamath::expr::render(&assertion.conclusion),
                    )));
                }
                Ok(thm)
            }
            Slot::Wff(_) => Err(replay_err("proof ended on a non-`|-` slot")),
        },
        depth => Err(replay_err(format!(
            "proof did not reduce to a single result (stack depth {depth})"
        ))),
    }
}

/// Process one `Label` proof step, returning the `Slot` it pushes (shared by
/// both proof encodings via [`replay_db`]'s step loop):
///
/// - a `$f` float → the metavariable as a `Slot::Wff` term;
/// - a `$e` essential → `Slot::Proved(assume Derivable_L ⌜hyp⌝)` (the hypothesis
///   surfaces on the final theorem);
/// - a `$a`/`$p` assertion → a syntactic former (`Slot::Wff`) or a `|-` rule
///   instance (`Slot::Proved`), via [`apply_assert`].
fn apply_label(
    db: &Database,
    rs: &RuleSet,
    clause_index: &HashMap<String, usize>,
    clause_ctx: &ClauseCtx,
    parser: &Parser,
    label: &str,
    stack: &mut Vec<Slot>,
) -> Result<Slot> {
    let stmt = db
        .statement_by_label(label)
        .ok_or_else(|| replay_err(format!("unknown proof label `{label}`")))?;
    match stmt {
        Statement::Float(f) => {
            // `$f <typecode> <var>` — push the metavariable as a plain term.
            Ok(Slot::Wff(Term::free(mv(&f.var), phi())))
        }
        Statement::Essential(h) => {
            // `$e |- <hyp>` — its derivability is *assumed*; it becomes a
            // hypothesis of the final theorem.
            let enc = parser.encode_expr(&h.expr)?;
            Ok(Slot::Proved(Thm::assume(derivable(rs, &enc)?)?))
        }
        Statement::Assert(target) => {
            apply_assert(db, clause_index, clause_ctx, target, label, stack)
        }
        _ => Err(replay_err(format!("label `{label}` is not applicable"))),
    }
}

/// Apply a target assertion during replay: pop its mandatory operands (floats
/// first, then essentials, in frame order) and dispatch on whether it is a
/// syntactic former or a `|-` rule.
fn apply_assert(
    db: &Database,
    clause_index: &HashMap<String, usize>,
    clause_ctx: &ClauseCtx,
    target: &Assertion,
    label: &str,
    stack: &mut Vec<Slot>,
) -> Result<Slot> {
    let n_floats = target.frame.floats.len();
    let n_mand = target.frame.mandatory_count();
    if stack.len() < n_mand {
        return Err(replay_err(format!(
            "stack underflow applying `{label}` (need {n_mand}, have {})",
            stack.len()
        )));
    }
    let args: Vec<Slot> = stack.split_off(stack.len() - n_mand);
    // `args[0..n_floats]` are the float (wff) operands; `args[n_floats..]` are
    // the essential (proved) operands, both in frame order.
    let float_args: Vec<Term> = args
        .get(..n_floats)
        .ok_or_else(|| replay_err(format!("`{label}`: not enough float operands")))?
        .iter()
        .enumerate()
        .map(|(i, s)| match s {
            Slot::Wff(t) => Ok(t.clone()),
            Slot::Proved(_) => Err(replay_err(format!("`{label}`: float operand {i} is not a wff"))),
        })
        .collect::<Result<_>>()?;

    if target.conclusion.typecode() != "|-" {
        // --- syntactic former: build the encoded instance, no proof ---
        // The float args are already compact sub-trees; re-fold the former's
        // conclusion body with each metavar filled by its arg. This is the
        // *same* compact encoding `Parser` produces for a literal of this
        // shape, so substitution into a `|-` schema (via `all_elim`) matches.
        let enc = encode_former(db, target, label, &float_args)?;
        Ok(Slot::Wff(enc))
    } else {
        // --- a `|-` axiom or rule: re-derive its instance through the kernel ---
        let prems: Vec<Thm> = args[n_floats..]
            .iter()
            .map(|s| match s {
                Slot::Proved(t) => Ok(t.clone()),
                Slot::Wff(_) => Err(replay_err(format!("`{label}`: expected a `|-` premise"))),
            })
            .collect::<Result<_>>()?;
        let k = *clause_index
            .get(label)
            .ok_or_else(|| replay_err(format!("`{label}` is not a `|-` clause of the database")))?;
        derive_clause(clause_ctx, k, &float_args, prems).map(Slot::Proved)
    }
}

/// Encode a **syntactic-former application** during replay: right-fold the
/// former's conclusion body, mapping each float metavariable
/// `target.frame.floats[i].var` to the i-th popped argument sub-tree
/// `float_args[i]` and every other token to its [`leaf`]. The result is the
/// compact `enc(former-body[vᵢ := argᵢ])`, identical to the `Parser`'s encoding
/// of a literal of the same shape.
fn encode_former(
    db: &Database,
    target: &Assertion,
    label: &str,
    float_args: &[Term],
) -> Result<Term> {
    let body = body_of(&target.conclusion)
        .ok_or_else(|| replay_err(format!("`{label}`: malformed former conclusion")))?;
    let mut args: HashMap<&str, Term> = HashMap::new();
    for (i, f) in target.frame.floats.iter().enumerate() {
        args.insert(f.var.as_str(), float_args[i].clone());
    }
    let resolve = |tok: &str| -> Result<Term> {
        Ok(match args.get(tok) {
            Some(t) => t.clone(),
            None => leaf(db, tok),
        })
    };
    encode(body, &resolve)
}

/// **Per-theorem precomputed clause assumptions.** Built ONCE per theorem (was:
/// rebuilt on every `|-` proof step inside `derive_clause`), this caches the
/// rule set's `{Closed d} ⊢ Closed d` assumption, the predicate variable `d`,
/// the `Closed d` term (for the final `imp_intro`), and — the big win — **all
/// `n` conjuncts already extracted** into an `O(1)`-indexable `Vec<Thm>`.
///
/// Extracting all conjuncts up front is O(n) total (one left walk peeling
/// `and_elim_r`/`and_elim_l`), versus the old per-step `nth_conjunct(k)` which
/// is O(k) each → O(S·D) across a proof. Each `Thm` is `Arc`-backed, so cloning
/// a cached conjunct is a cheap refcount bump.
struct ClauseCtx {
    d: Term,
    closed_t: Term,
    assumed: Thm,
    pred_ty: Type,
    conjuncts: Vec<Thm>,
}

impl ClauseCtx {
    fn new(rs: &RuleSet) -> Result<Self> {
        let d = rs.d_var();
        // Lay the clauses out ONCE (was: `n_clauses` laid them out to count, then
        // `closed_for_var` laid them out again to conjoin — two full builds of D
        // `bool` terms per theorem). One build gives us both the count and the
        // `Closed d` conjunction.
        let clause_terms = (rs.clauses)(&|f| d.clone().apply(f.clone()))?;
        let n = clause_terms.len();
        let closed_t = conj(clause_terms)?;
        let assumed = Thm::assume(closed_t.clone())?; // {Closed d} ⊢ Closed d
        // Pre-extract conjunct 0..n in one left-to-right walk: `running` is the
        // tail `cₖ ∧ (cₖ₊₁ ∧ …)`; conjunct k is its left projection (or the whole
        // tail for the last k), then advance with `and_elim_r`.
        let mut conjuncts = Vec::with_capacity(n);
        let mut running = assumed.clone();
        for k in 0..n {
            if k + 1 < n {
                conjuncts.push(running.clone().and_elim_l()?);
                running = running.and_elim_r()?;
            } else {
                conjuncts.push(running);
                break;
            }
        }
        Ok(ClauseCtx {
            d,
            closed_t,
            assumed,
            pred_ty: rs.pred_ty(),
            conjuncts,
        })
    }
}

/// The `|-` derivation constructor (mirrors [`crate::init::prop::derive_mp`]).
///
/// For the clause at index `k`, with float-argument terms `args` and
/// essential-premise theorems `prems`, construct `⊢ Derivable_L ⌜concl-instance⌝`
/// (carrying the premises' essential hypotheses):
///
/// take the pre-extracted conjunct `k` from `ctx`; `all_elim` the float args in
/// order (so they hit `float_vars[0]` first); if there are premises, turn each
/// `⊢ Derivable_L ⌜eᵢ⌝` into `d ⌜eᵢ⌝` under the cached `Closed_L d` and discharge
/// the clause's antecedent with their conjunction; finally `imp_intro`
/// `Closed_L d` and `all_intro` `d`.
fn derive_clause(ctx: &ClauseCtx, k: usize, args: &[Term], prems: Vec<Thm>) -> Result<Thm> {
    // {Closed d} ⊢ ∀floats. (prem_conj ⟹)? d ⌜concl⌝ — clone the cached conjunct.
    let mut clause = ctx
        .conjuncts
        .get(k)
        .ok_or_else(|| replay_err(format!("clause index {k} out of range")))?
        .clone();
    for a in args {
        clause = clause.all_elim(a.clone())?; // strip float_vars[0..] in order
    }

    let d_concl = if prems.is_empty() {
        clause // {Closed d} ⊢ d ⌜concl⌝
    } else {
        // Each premise ⊢ Derivable_L ⌜eᵢ⌝ → {…} ⊢ d ⌜eᵢ⌝ under `assumed`.
        let prem_d: Vec<Thm> = prems
            .into_iter()
            .map(|p| p.all_elim(ctx.d.clone())?.imp_elim(ctx.assumed.clone()))
            .collect::<Result<_>>()?;
        clause.imp_elim(conj_thms(prem_d)?)? // {…} ⊢ d ⌜concl⌝
    };

    // Discharge `Closed d`, generalise `d`; essential hyps remain.
    d_concl
        .imp_intro(&ctx.closed_t)?
        .all_intro("d", ctx.pred_ty.clone())
}

// ============================================================================
// Tests — genericity over three unrelated databases (one function, three logics)
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_genuine(thm: &Thm) {
        assert!(thm.has_no_obs(), "replayed theorem must be oracle-free");
    }

    /// The vendored real `hol.mm` (CC0; all 151 `$p` proofs are *compressed*).
    const HOL_MM: &str = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../covalence-metamath/tests/fixtures/hol.mm"
    ));

    /// **Performance benchmark** for `derive_theorem`. Times every `$p` theorem
    /// of `hol.mm` (all 151) individually and reports the total plus the slowest
    /// few. With `COV_SET_MM` set, also samples set.mm. `#[ignore]`d (timing).
    /// Run: `cargo test -p covalence-hol --lib --release \
    ///   metalogic::mm_database::tests::bench_derive_theorem -- --ignored --nocapture`
    #[test]
    #[ignore = "performance benchmark; run with --ignored --nocapture"]
    fn bench_derive_theorem() {
        let db = crate::metamath::parse(HOL_MM).expect("hol.mm parses");
        let labels: Vec<String> = db
            .assertions()
            .filter(|a| a.proof.is_some() && a.conclusion.typecode() == "|-")
            .map(|a| a.label.clone())
            .collect();

        // Import-path timing: build the parser ONCE (Win 4) and derive each
        // theorem through `derive_theorem_with` (the shared-parser path used by
        // `mm_import`). This is the realistic whole-database import cost.
        let parser = Parser::new(&db);
        let t0 = std::time::Instant::now();
        let mut timings: Vec<(String, std::time::Duration)> = Vec::new();
        for label in &labels {
            let t = std::time::Instant::now();
            let thm = derive_theorem_with(&db, &parser, label)
                .unwrap_or_else(|e| panic!("hol.mm `{label}` failed: {e}"));
            assert!(thm.has_no_obs());
            timings.push((label.clone(), t.elapsed()));
        }
        let total = t0.elapsed();
        timings.sort_by(|a, b| b.1.cmp(&a.1));
        eprintln!(
            "\n=== hol.mm import (shared parser): {} theorems in {:?} ===",
            labels.len(),
            total
        );
        eprintln!("slowest 10:");
        for (l, d) in timings.iter().take(10) {
            eprintln!("  {d:>10.3?}  {l}");
        }

        if let Ok(path) = std::env::var("COV_SET_MM") {
            let source = std::fs::read_to_string(&path).expect("read set.mm");
            let tp = std::time::Instant::now();
            let db = crate::metamath::parse(&source).expect("set.mm parses");
            eprintln!("\nset.mm parsed in {:?}", tp.elapsed());
            let _warm = Parser::new(&db); // warm caches/pages
            let tpp = std::time::Instant::now();
            let _p = Parser::new(&db);
            eprintln!("set.mm Parser::new (warm) in {:?}", tpp.elapsed());
            // A fixed sample including some known-deep theorems if present.
            let mut sample: Vec<String> = Vec::new();
            for cand in [
                "a1i", "mp2", "syl", "3syl", "sylib", "mpbir", "imim1i", "con2d",
                "pm2.61i", "ax12v", "19.21t", "exlimdv", "dvelimhw",
            ] {
                if let Some(Statement::Assert(a)) = db.statement_by_label(cand)
                    && a.proof.is_some()
                {
                    sample.push(cand.to_string());
                }
            }
            // Plus the first 50 |- $p theorems in db order.
            for a in db.assertions() {
                if sample.len() >= 63 {
                    break;
                }
                if a.proof.is_some()
                    && a.conclusion.typecode() == "|-"
                    && !sample.contains(&a.label)
                {
                    sample.push(a.label.clone());
                }
            }
            let parser = Parser::new(&db);
            let t0 = std::time::Instant::now();
            let mut timings: Vec<(String, std::time::Duration)> = Vec::new();
            for label in &sample {
                let t = std::time::Instant::now();
                let _ = derive_theorem_with(&db, &parser, label)
                    .unwrap_or_else(|e| panic!("set.mm `{label}` failed: {e}"));
                timings.push((label.clone(), t.elapsed()));
            }
            let total = t0.elapsed();
            timings.sort_by(|a, b| b.1.cmp(&a.1));
            eprintln!(
                "\n=== set.mm import (shared parser): {} theorems in {:?} ===",
                sample.len(),
                total
            );
            eprintln!("slowest 10:");
            for (l, d) in timings.iter().take(10) {
                eprintln!("  {d:>10.3?}  {l}");
            }
        }
    }

    // --- Theory 1: propositional calculus (set.mm ax-1/ax-2/ax-mp) ----------

    const PROP: &str = "\
        $c ( ) -> wff |- $.
        $v ph ps ch $.
        wph $f wff ph $.
        wps $f wff ps $.
        wch $f wff ch $.
        wi $a wff ( ph -> ps ) $.
        ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
        ax-2 $a |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $.
        ${
          mp.maj $e |- ph $.
          mp.min $e |- ( ph -> ps ) $.
          ax-mp $a |- ps $.
        $}
    ";

    /// `ax2i` — a single `ax-2` instance (`ch := ph`), no essentials. The
    /// returned theorem is hypothesis-free, oracle-free, and its conclusion is
    /// exactly `derivable(rule_set(db), enc(S))`.
    #[test]
    fn replay_prop_ax2i() {
        let src = format!(
            "{PROP}\n\
            ax2i $p |- ( ( ph -> ( ps -> ph ) ) -> ( ( ph -> ps ) -> ( ph -> ph ) ) ) $=\n\
              wph wps wph ax-2 $.\n"
        );
        let db = crate::metamath::parse(&src).unwrap();
        assert_eq!(crate::metamath::verify_all(&db).unwrap(), 1);

        let a = db.assertions().find(|a| a.label == "ax2i").unwrap();
        let thm = replay_db(&db, a).unwrap();

        assert!(thm.hyps().is_empty(), "ax2i replay must be hypothesis-free");
        assert_genuine(&thm);

        // ONE function, stated expectation via the public helpers.
        let rs = rule_set(&db);
        let expected = derivable(&rs, &encode_conclusion(&db, a).unwrap()).unwrap();
        assert_eq!(thm.concl(), &expected);
    }

    /// `a1i` — a derived rule with one essential `a1i.1 $e |- ph`. The replay
    /// carries exactly that one hypothesis (`Derivable_L ⌜ph⌝`).
    #[test]
    fn replay_prop_a1i() {
        let src = format!(
            "{PROP}\n\
            ${{\n\
              a1i.1 $e |- ph $.\n\
              a1i $p |- ( ps -> ph ) $=\n\
                wph  wps wph wi  a1i.1  wph wps ax-1  ax-mp $.\n\
            $}}\n"
        );
        let db = crate::metamath::parse(&src).unwrap();
        assert_eq!(crate::metamath::verify_all(&db).unwrap(), 1);

        let a = db.assertions().find(|a| a.label == "a1i").unwrap();
        let thm = replay_db(&db, a).unwrap();
        assert_genuine(&thm);

        let rs = rule_set(&db);
        let expected = derivable(&rs, &encode_conclusion(&db, a).unwrap()).unwrap();
        assert_eq!(thm.concl(), &expected);

        // Exactly one hypothesis: Derivable_L ⌜ph⌝ (metavar `ph` is namespaced).
        let ph = Term::free(mv("ph"), phi());
        let hyps: Vec<&Term> = thm.hyps().iter().collect();
        assert_eq!(hyps.len(), 1, "a1i carries exactly one hypothesis");
        assert_eq!(hyps[0], &derivable(&rs, &ph).unwrap());
    }

    // --- Theory 2: demo0 (the Metamath book's intro theory) -----------------

    const DEMO0: &str = "\
        $c 0 + = -> ( ) term wff |- $.
        $v t r s P Q $.
        tt $f term t $.
        tr $f term r $.
        ts $f term s $.
        wp $f wff P $.
        wq $f wff Q $.
        tze $a term 0 $.
        tpl $a term ( t + r ) $.
        weq $a wff t = r $.
        wim $a wff ( P -> Q ) $.
        a1 $a |- ( t = r -> ( t = s -> r = s ) ) $.
        a2 $a |- ( t + 0 ) = t $.
        ${
          min $e |- P $.
          maj $e |- ( P -> Q ) $.
          mp $a |- Q $.
        $}
        th1 $p |- t = t $= tt tze tpl tt weq tt tt weq tt a2 tt tze tpl
            tt weq tt tze tpl tt weq tt tt weq wim tt a2 tt tze tpl
            tt tt a1 mp mp $.
    ";

    /// `th1` — `|- t = t`, hypothesis-free, using term-formers `tze`/`tpl`,
    /// wff-formers `weq`/`wim`, axioms `a1`/`a2`, and rule `mp`. A completely
    /// different signature from PROP, replayed by the *same* function.
    #[test]
    fn replay_demo0_th1() {
        let db = crate::metamath::parse(DEMO0).unwrap();
        assert_eq!(crate::metamath::verify_all(&db).unwrap(), 1);

        let a = db.assertions().find(|a| a.label == "th1").unwrap();
        let thm = replay_db(&db, a).unwrap();

        assert!(thm.hyps().is_empty(), "th1 replay must be hypothesis-free");
        assert_genuine(&thm);

        let rs = rule_set(&db);
        let expected = derivable(&rs, &encode_conclusion(&db, a).unwrap()).unwrap();
        assert_eq!(thm.concl(), &expected);
    }

    // --- Theory 3: a tiny binary-operation ("group-ish") theory -------------

    const GROUP: &str = "\
        $c term = ( ) o e |- $.
        $v a b c $.
        ta $f term a $.
        tb $f term b $.
        tc $f term c $.
        te $a term e $.
        top $a term ( a o b ) $.
        weq $a |- ( a = b ) $.
        refl $a |- ( a = a ) $.
        symm $a |- ( b = a ) $.
    ";

    /// `th` — `|- ( ( a o b ) = ( a o b ) )` via the former `top` and axiom
    /// `refl` (`a := ( a o b )`). A third distinct signature; same `replay_db`.
    #[test]
    fn replay_group_th() {
        let src = format!(
            "{GROUP}\n\
            th $p |- ( ( a o b ) = ( a o b ) ) $=\n\
              ta tb top refl $.\n"
        );
        let db = crate::metamath::parse(&src).unwrap();
        assert_eq!(crate::metamath::verify_all(&db).unwrap(), 1);

        let a = db.assertions().find(|a| a.label == "th").unwrap();
        let thm = replay_db(&db, a).unwrap();

        assert!(thm.hyps().is_empty(), "th replay must be hypothesis-free");
        assert_genuine(&thm);

        let rs = rule_set(&db);
        let expected = derivable(&rs, &encode_conclusion(&db, a).unwrap()).unwrap();
        assert_eq!(thm.concl(), &expected);
    }
}
