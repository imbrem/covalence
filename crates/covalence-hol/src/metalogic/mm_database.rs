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
//! - **Compressed proofs** are rejected (decompress to a normal proof first).
//! - **Syntactic formers** (`wff`/`term`/… assertions) are *grammar*, not
//!   derivability rules: they build [`Slot::Wff`] terms during replay but
//!   contribute **no** clause to the rule set.

use std::collections::HashMap;

use covalence_core::{Error, Result, Term, Thm, Type};

use crate::init::ext::TermExt;
use crate::metamath::expr::body_of;
use crate::metamath::{Assertion, Database, Expr, Proof, Statement};

use super::{RuleSet, closed_for_var, conj, conj_thms, derivable, nth_conjunct};

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

/// A leaf resolver: a Metamath **variable** `tok` → `Term::free(tok, nat)` (a
/// metavariable, to be ∀-bound in its clause); any other token is treated as a
/// **constant** → the uninterpreted constant `mm$c$<tok> : nat`.
fn leaf(db: &Database, tok: &str) -> Term {
    if db.is_variable(tok) {
        Term::free(tok, phi())
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
    /// Every declared `$f` floating hypothesis's `var → typecode`, gathered from
    /// the *whole* database (not just former frames — a variable's `$f` may be
    /// introduced for a `|-` assertion, e.g. demo0's `s`).
    var_tc: HashMap<String, String>,
}

impl<'a> Parser<'a> {
    /// Build the parser from a database: every non-`|-` assertion is a former.
    pub fn new(db: &'a Database) -> Self {
        let formers = db
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
        let mut var_tc = HashMap::new();
        for stmt in db.statements() {
            if let Statement::Float(f) = stmt {
                var_tc.insert(f.var.clone(), f.typecode.clone());
            }
        }
        Parser {
            db,
            formers,
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
        if self.formers.iter().any(|f| f.typecode == e.typecode()) {
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
        for tc in self.start_typecodes() {
            if let Ok((term, rest)) = self.parse(tc, &toks)
                && rest.is_empty()
            {
                return Ok(term);
            }
        }
        self.encode_greedy(&toks)
    }

    /// The distinct former result-typecodes (candidate start symbols for a
    /// whole-`|-`-body parse), in database-first-seen order.
    fn start_typecodes(&self) -> Vec<&str> {
        let mut seen = Vec::new();
        for f in &self.formers {
            if !seen.contains(&f.typecode.as_str()) {
                seen.push(f.typecode.as_str());
            }
        }
        seen
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
        // Try each former whose result typecode is `tc`; first full match wins.
        for f in self.formers.iter().filter(|f| f.typecode == tc) {
            if let Some((term, rest)) = self.try_former(f, toks)? {
                return Ok((term, rest));
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
        for v in self.float_vars.iter().rev() {
            body = body.forall(v, phi())?;
        }
        Ok(body)
    }
}

/// Collect the database's `|-` clauses (one per `|-` assertion, in database
/// order) and a `label → clause index` map. Syntactic formers (non-`|-`
/// assertions) are skipped — they are grammar, not derivability rules.
fn collect_clauses(db: &Database) -> (Vec<Clause>, HashMap<String, usize>) {
    let parser = Parser::new(db);
    let mut clauses = Vec::new();
    let mut index = HashMap::new();
    for a in db.assertions() {
        if a.conclusion.typecode() != "|-" {
            continue; // a syntactic former — grammar, not a rule.
        }
        let float_vars: Vec<String> = a.frame.floats.iter().map(|f| f.var.clone()).collect();
        let ess_encs: Result<Vec<Term>> = a
            .frame
            .essentials
            .iter()
            .map(|h| parser.encode_expr(&h.expr))
            .collect();
        // Encoding a malformed body shouldn't happen on a verified database; if
        // it does, drop the clause rather than poisoning the whole rule set —
        // a missing clause only makes the rule set *weaker* (sound for the
        // construct direction), and the per-step replay re-checks the instance.
        let (Ok(ess_encs), Ok(concl_enc)) = (ess_encs, parser.encode_expr(&a.conclusion)) else {
            continue;
        };
        index.insert(a.label.clone(), clauses.len());
        clauses.push(Clause {
            float_vars,
            ess_encs,
            concl_enc,
        });
    }
    (clauses, index)
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
    let (clauses, _) = collect_clauses(db);
    RuleSet::new(phi(), move |d_apply| {
        clauses.iter().map(|c| c.build(d_apply)).collect()
    })
}

// ============================================================================
// The replay
// ============================================================================

/// One slot on the replay stack.
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
pub fn replay_db(db: &Database, assertion: &Assertion) -> Result<Thm> {
    let labels = match assertion.proof.as_ref() {
        Some(Proof::Normal(labels)) => labels,
        Some(Proof::Compressed { .. }) => {
            return Err(replay_err(
                "compressed-proof replay is not supported (decompress to a normal proof first)",
            ));
        }
        None => return Err(replay_err("assertion has no proof to replay")),
    };

    let rs = rule_set(db);
    let (_, clause_index) = collect_clauses(db);
    let n = clause_index.len();
    let parser = Parser::new(db);

    let mut stack: Vec<Slot> = Vec::new();

    for label in labels {
        let stmt = db
            .statement_by_label(label)
            .ok_or_else(|| replay_err(format!("unknown proof label `{label}`")))?;
        match stmt {
            Statement::Float(f) => {
                // `$f <typecode> <var>` — push the metavariable as a plain term.
                stack.push(Slot::Wff(Term::free(&f.var, phi())));
            }
            Statement::Essential(h) => {
                // `$e |- <hyp>` — its derivability is *assumed*; it becomes a
                // hypothesis of the final theorem.
                let enc = parser.encode_expr(&h.expr)?;
                stack.push(Slot::Proved(Thm::assume(derivable(&rs, &enc)?)?));
            }
            Statement::Assert(target) => {
                let slot = apply_assert(db, &rs, &clause_index, n, target, label, &mut stack)?;
                stack.push(slot);
            }
            _ => return Err(replay_err(format!("label `{label}` is not applicable"))),
        }
    }

    match stack.len() {
        1 => match stack.pop().expect("len checked") {
            Slot::Proved(thm) => {
                // Sanity: the re-derived theorem is the derivability of the
                // claimed conclusion's encoding.
                let want = derivable(&rs, &encode_conclusion(db, assertion)?)?;
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

/// Apply a target assertion during replay: pop its mandatory operands (floats
/// first, then essentials, in frame order) and dispatch on whether it is a
/// syntactic former or a `|-` rule.
fn apply_assert(
    db: &Database,
    rs: &RuleSet,
    clause_index: &HashMap<String, usize>,
    n: usize,
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
        derive_clause(rs, k, n, &float_args, prems).map(Slot::Proved)
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

/// The `|-` derivation constructor (mirrors [`crate::init::prop::derive_mp`]).
///
/// For the clause at index `k` (of `n`), with float-argument terms `args` and
/// essential-premise theorems `prems`, construct `⊢ Derivable_L ⌜concl-instance⌝`
/// (carrying the premises' essential hypotheses):
///
/// open `∀d. Closed_L d ⟹ d ⌜·⌝` by assuming `Closed_L d`; extract conjunct
/// `k`; `all_elim` the float args in order (so they hit `float_vars[0]` first);
/// if there are premises, turn each `⊢ Derivable_L ⌜eᵢ⌝` into `d ⌜eᵢ⌝` under the
/// same `Closed_L d` and discharge the clause's antecedent with their
/// conjunction; finally `imp_intro` `Closed_L d` and `all_intro` `d`.
fn derive_clause(
    rs: &RuleSet,
    k: usize,
    n: usize,
    args: &[Term],
    prems: Vec<Thm>,
) -> Result<Thm> {
    let d = rs.d_var();
    let closed_t = closed_for_var(rs)?;
    let assumed = Thm::assume(closed_t.clone())?; // {Closed d} ⊢ Closed d

    // {Closed d} ⊢ ∀floats. (prem_conj ⟹)? d ⌜concl⌝
    let mut clause = nth_conjunct(assumed.clone(), k, n)?;
    for a in args {
        clause = clause.all_elim(a.clone())?; // strip float_vars[0..] in order
    }

    let d_concl = if prems.is_empty() {
        clause // {Closed d} ⊢ d ⌜concl⌝
    } else {
        // Each premise ⊢ Derivable_L ⌜eᵢ⌝ → {…} ⊢ d ⌜eᵢ⌝ under `assumed`.
        let prem_d: Vec<Thm> = prems
            .into_iter()
            .map(|p| p.all_elim(d.clone())?.imp_elim(assumed.clone()))
            .collect::<Result<_>>()?;
        clause.imp_elim(conj_thms(prem_d)?)? // {…} ⊢ d ⌜concl⌝
    };

    // Discharge `Closed d`, generalise `d`; essential hyps remain.
    d_concl
        .imp_intro(&closed_t)?
        .all_intro("d", rs.pred_ty())
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

        // Exactly one hypothesis: Derivable_L ⌜ph⌝.
        let ph = Term::free("ph", phi());
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
