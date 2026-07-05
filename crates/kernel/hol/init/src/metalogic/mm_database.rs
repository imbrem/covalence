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
//! over encoded syntax* — **no denotation `⟦S⟧`, no oracle, no trust in the
//! Metamath verifier's say-so**.
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
//!   derivability rules: they build `Slot::Wff` terms during replay but
//!   contribute **no** clause to the rule set.

use fnv::FnvHashMap as HashMap;

use covalence_core::term::TrustedCons;
use covalence_core::{Error, Result, Term, Thm, Type};

use crate::init::ext::{TermExt, ThmExt};
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

/// The uninterpreted binary former `concat : nat → nat → nat`. Cached once: it
/// is the single most-allocated node in the encoding (every `concat` clones it),
/// so rebuilding the `Term` + its function type per call was pure waste.
fn concat_fn() -> Term {
    static CONCAT_FN: std::sync::LazyLock<Term> = std::sync::LazyLock::new(|| {
        Term::free("mm$concat", Type::fun(phi(), Type::fun(phi(), phi())))
    });
    CONCAT_FN.clone()
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
/// token to its `leaf`.
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

/// Packrat memo for one expression parse: `(typecode id, position) →`
/// `parse result`. A `None` value records a *cached failure* (no parse at
/// that typecode/position), so neither successes nor failures are recomputed
/// during backtracking. Scoped to a single [`Parser::encode_expr`] call, so
/// the [`Parser`] itself stays immutable and `Sync` for the parallel import.
type Memo = HashMap<(u32, usize), Option<(Term, usize)>>;

/// Sentinel typecode id for [`Parser::parse_any_at`] (which tries every
/// former regardless of result typecode). Distinct from any real typecode id
/// (those are a dense range from 0).
const ANY_TC: u32 = u32::MAX;

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
    /// `typecode → small dense id`, covering every typecode that can be a
    /// parse target (former result typecodes + `$f` float typecodes). Used as
    /// the packrat memo key `(id, pos)` so backtracking re-parses of the same
    /// `(typecode, position)` are cached instead of recomputed — turning the
    /// recursive-descent parse of a deeply-nested expression from
    /// exponential to linear.
    tc_id: HashMap<String, u32>,
    /// Every declared `$f` floating hypothesis's `var → typecode`, gathered from
    /// the *whole* database (not just former frames — a variable's `$f` may be
    /// introduced for a `|-` assertion, e.g. demo0's `s`).
    var_tc: HashMap<String, String>,
    /// Precomputed leaf encodings `token → enc(token)` (a `Free`). The hot
    /// `parse`/`try_former` loops then clone an `Arc` instead of re-`format!`ing
    /// the `mm$c$`/`mm$v$` name + reallocating per leaf occurrence. Read-only
    /// after construction (so it stays `Sync` for the parallel import); tokens
    /// not present (rare) fall back to building on the fly via [`Self::leaf`].
    leaves: HashMap<String, Term>,
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
        let mut by_typecode: HashMap<String, Vec<usize>> = HashMap::default();
        let mut typecodes: Vec<String> = Vec::new();
        for (i, f) in formers.iter().enumerate() {
            let entry = by_typecode.entry(f.typecode.clone());
            if matches!(entry, std::collections::hash_map::Entry::Vacant(_)) {
                typecodes.push(f.typecode.clone());
            }
            entry.or_default().push(i);
        }
        let mut var_tc = HashMap::default();
        for stmt in db.statements() {
            if let Statement::Float(f) = stmt {
                var_tc.insert(f.var.clone(), f.typecode.clone());
            }
        }
        // Precompute the leaf encoding of every token the encoder can encounter:
        // each former-body symbol (the syntax constants) and each declared float
        // variable. Built once; the hot loops just clone the cached `Arc`.
        let mut leaves: HashMap<String, Term> = HashMap::default();
        for f in &formers {
            for tok in &f.body {
                leaves.entry(tok.clone()).or_insert_with(|| leaf(db, tok));
            }
        }
        for var in var_tc.keys() {
            leaves.entry(var.clone()).or_insert_with(|| leaf(db, var));
        }
        // Dense ids for every typecode that can be a parse target: former
        // result typecodes and every float typecode (the recursive
        // sub-expression targets). Keys the packrat memo.
        let mut tc_id: HashMap<String, u32> = HashMap::default();
        let intern_tc = |tc: &str, map: &mut HashMap<String, u32>| {
            let next = map.len() as u32;
            map.entry(tc.to_string()).or_insert(next);
        };
        for f in &formers {
            intern_tc(&f.typecode, &mut tc_id);
            for (_, sub_tc) in &f.floats {
                intern_tc(sub_tc, &mut tc_id);
            }
        }
        Parser {
            db,
            formers,
            by_typecode,
            typecodes,
            tc_id,
            var_tc,
            leaves,
        }
    }

    /// Encode an expression *body* compactly under this grammar.
    ///
    /// If the statement's typecode has a production (some former concludes it,
    /// e.g. `wff`/`term`), the body is parsed *strictly* as one expression of
    /// that typecode. A `|-` body (the provability layer) has **no** former
    /// production, so it is encoded *greedily* (`encode_greedy`): maximal
    /// syntactic sub-expressions are parsed compactly and every other token is a
    /// literal constant — which still makes a `|-` schema's metavar positions
    /// (single typed-variable leaves) line up with substituted instances.
    ///
    /// Parsing is **packrat-memoized** (see `Memo`): a recursive-descent
    /// parse of this grammar backtracks (every infix former re-parses its left
    /// operand under each candidate operator), which is exponential in nesting
    /// depth on large set.mm expressions. The memo caches each
    /// `(typecode, position)` result, making the whole encode linear.
    pub fn encode_expr(&self, e: &Expr) -> Result<Term> {
        let body = body_of(e).ok_or_else(|| replay_err("malformed statement (no body)"))?;
        let toks: Vec<&str> = body.iter().map(|s| s.as_str()).collect();
        let mut memo: Memo = Memo::default();
        if self.by_typecode.contains_key(e.typecode()) {
            return match self.parse_at(e.typecode(), &toks, 0, &mut memo) {
                Some((term, end)) if end == toks.len() => Ok(term),
                Some(_) => Err(replay_err(format!(
                    "trailing symbols after parsing `{}`",
                    e.render()
                ))),
                None => Err(replay_err(format!(
                    "cannot parse a `{}` from `{}`",
                    e.typecode(),
                    toks.join(" ")
                ))),
            };
        }
        // No production for this typecode (the `|-` provability layer). First
        // try to parse the *whole* body as a single expression of some former
        // typecode (set.mm-style: a `|-` body is one `wff`); the parenthesised
        // grammars are unambiguous, so a full consume is canonical. Otherwise
        // fall back to greedy token-by-token encoding (raw `|-` bodies with no
        // top-level production, e.g. the GROUP theory's `( a = a )`).
        for tc in &self.typecodes {
            if let Some((term, end)) = self.parse_at(tc, &toks, 0, &mut memo)
                && end == toks.len()
            {
                return Ok(term);
            }
        }
        self.encode_greedy(&toks, &mut memo)
    }

    /// Greedily encode a token sequence with no top-level production: walk left
    /// to right, parsing a maximal syntactic sub-expression where one starts and
    /// otherwise taking the token as a literal constant leaf; right-fold the
    /// resulting node sequence with [`concat`].
    fn encode_greedy(&self, toks: &[&str], memo: &mut Memo) -> Result<Term> {
        let mut nodes: Vec<Term> = Vec::new();
        let mut pos = 0;
        while pos < toks.len() {
            if let Some((node, end)) = self.parse_any_at(toks, pos, memo) {
                nodes.push(node);
                pos = end;
            } else {
                nodes.push(self.leaf(toks[pos]));
                pos += 1;
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
    /// at `pos`. Returns `None` if none applies (the caller then treats the
    /// token as a literal `|-`-structural token). A bare typed variable is
    /// intentionally *not* matched here — it is taken as a leaf by the caller,
    /// which is the right granularity for a `|-` schema's metavars. Memoized
    /// under the sentinel typecode id [`ANY_TC`].
    fn parse_any_at(&self, toks: &[&str], pos: usize, memo: &mut Memo) -> Option<(Term, usize)> {
        if let Some(cached) = memo.get(&(ANY_TC, pos)) {
            return cached.clone();
        }
        let mut res = None;
        for f in &self.formers {
            if let Some(hit) = self.try_former_at(f, toks, pos, memo) {
                res = Some(hit);
                break;
            }
        }
        memo.insert((ANY_TC, pos), res.clone());
        res
    }

    /// Parse one expression of typecode `tc` at `pos`, returning the compact
    /// encoding and the next position. A lone metavariable of typecode `tc` is
    /// a leaf; otherwise the first-matching former applies. Packrat-memoized on
    /// `(tc id, pos)` — the cache that turns the backtracking parse linear.
    fn parse_at(
        &self,
        tc: &str,
        toks: &[&str],
        pos: usize,
        memo: &mut Memo,
    ) -> Option<(Term, usize)> {
        // Typecodes that can be parse targets all have ids; if one somehow
        // doesn't, fall through uncached (correctness over speed).
        if let Some(&id) = self.tc_id.get(tc) {
            if let Some(cached) = memo.get(&(id, pos)) {
                return cached.clone();
            }
            let res = self.parse_uncached(tc, toks, pos, memo);
            memo.insert((id, pos), res.clone());
            res
        } else {
            self.parse_uncached(tc, toks, pos, memo)
        }
    }

    /// The body of [`parse_at`] (without the memo lookup/store).
    fn parse_uncached(
        &self,
        tc: &str,
        toks: &[&str],
        pos: usize,
        memo: &mut Memo,
    ) -> Option<(Term, usize)> {
        // A bare metavariable of this typecode (its `$f` typecode must match).
        if let Some(head) = toks.get(pos)
            && self.db.is_variable(head)
            && self.var_typecode(head) == Some(tc)
        {
            return Some((self.leaf(head), pos + 1));
        }
        // Try each former whose result typecode is `tc` (via the typecode index,
        // database order preserved); first full match wins.
        if let Some(idxs) = self.by_typecode.get(tc) {
            for &i in idxs {
                if let Some(hit) = self.try_former_at(&self.formers[i], toks, pos, memo) {
                    return Some(hit);
                }
            }
        }
        None
    }

    /// Attempt to match former `f` at `pos`. On success returns the compact
    /// encoding (the former body re-folded with its metavars filled by the
    /// parsed sub-trees) and the next position.
    fn try_former_at(
        &self,
        f: &Former,
        toks: &[&str],
        mut pos: usize,
        memo: &mut Memo,
    ) -> Option<(Term, usize)> {
        // Formers have only a handful of floats, so a small Vec with a linear
        // scan beats a HashMap (no hashing, no map allocation) on this hot path.
        let mut args: Vec<(&str, Term)> = Vec::new();
        for pat in &f.body {
            if let Some((_, sub_tc)) = f.floats.iter().find(|(v, _)| v == pat) {
                // A metavar position: recursively parse a sub-expression.
                let (sub, end) = self.parse_at(sub_tc, toks, pos, memo)?;
                args.push((pat.as_str(), sub));
                pos = end;
            } else {
                // A literal constant: it must match the next input token.
                match toks.get(pos) {
                    Some(head) if *head == pat => pos += 1,
                    _ => return None,
                }
            }
        }
        // Re-fold the former body with metavars → their parsed encodings.
        let resolve = |tok: &str| -> Result<Term> {
            Ok(match args.iter().find(|(k, _)| *k == tok) {
                Some((_, t)) => t.clone(),
                None => self.leaf(tok),
            })
        };
        // `encode` only fails on an empty body, which a former never has.
        let term = encode(&f.body, &resolve).ok()?;
        Some((term, pos))
    }

    /// Parse a token body **as typecode `tc`**, but with the floats in `subst`
    /// pre-resolved to supplied argument sub-trees rather than encoded as bare
    /// leaves. This is the structured counterpart of a flat right-fold: nested
    /// formers written out literally in the body (e.g. the `( ph -> ps )` inside
    /// a syntactic theorem's `( ( ph -> ps ) -> ch )`) are recursively grouped,
    /// so the result matches [`encode_expr`] of the same instance byte-for-byte.
    fn parse_subst<'t>(
        &self,
        tc: &str,
        toks: &'t [&'t str],
        subst: &[(&str, Term)],
    ) -> Result<(Term, &'t [&'t str])> {
        // A bare metavariable of this typecode: use the substituted arg if one
        // is supplied, else its leaf encoding.
        if let Some((head, rest)) = toks.split_first()
            && self.db.is_variable(head)
            && self.var_typecode(head) == Some(tc)
        {
            let term = match subst.iter().find(|(k, _)| k == head) {
                Some((_, t)) => t.clone(),
                None => self.leaf(head),
            };
            return Ok((term, rest));
        }
        if let Some(idxs) = self.by_typecode.get(tc) {
            for &i in idxs {
                if let Some((term, rest)) = self.try_former_subst(&self.formers[i], toks, subst)? {
                    return Ok((term, rest));
                }
            }
        }
        Err(replay_err(format!(
            "cannot parse a `{tc}` from `{}`",
            toks.join(" ")
        )))
    }

    /// [`try_former`] threading a float→arg substitution into its recursive
    /// sub-parses (so nested metavars resolve to the supplied args).
    fn try_former_subst<'t>(
        &self,
        f: &Former,
        mut toks: &'t [&'t str],
        subst: &[(&str, Term)],
    ) -> Result<Option<(Term, &'t [&'t str])>> {
        let mut args: Vec<(&str, Term)> = Vec::new();
        for pat in &f.body {
            if let Some((_, sub_tc)) = f.floats.iter().find(|(v, _)| v == pat) {
                let Ok((sub, rest)) = self.parse_subst(sub_tc, toks, subst) else {
                    return Ok(None);
                };
                args.push((pat.as_str(), sub));
                toks = rest;
            } else {
                match toks.split_first() {
                    Some((head, rest)) if head == pat => toks = rest,
                    _ => return Ok(None),
                }
            }
        }
        let resolve = |tok: &str| -> Result<Term> {
            Ok(match args.iter().find(|(k, _)| *k == tok) {
                Some((_, t)) => t.clone(),
                None => self.leaf(tok),
            })
        };
        let term = encode(&f.body, &resolve)?;
        Ok(Some((term, toks)))
    }

    /// The `$f` typecode declared for variable `var`, if any.
    fn var_typecode(&self, var: &str) -> Option<&str> {
        self.var_tc.get(var).map(String::as_str)
    }

    /// Cached [`leaf`]: clone the precomputed `Arc` on a hit, build on a miss.
    fn leaf(&self, tok: &str) -> Term {
        self.leaves
            .get(tok)
            .cloned()
            .unwrap_or_else(|| leaf(self.db, tok))
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
            let prems: Vec<Term> = self.ess_encs.iter().map(d_apply).collect::<Result<_>>()?;
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

/// A reusable cache of compiled `|-` `Clause`s, keyed by assertion label. A
/// clause depends only on the assertion (not the proof using it), so it is
/// identical every time — build one per import worker and thread it across
/// [`derive_theorem_cached`] calls so each lemma's conclusion is encoded **once**
/// instead of being re-parsed in every proof that cites it (lemmas like `ax-mp`
/// / `simp*` are cited by thousands of proofs). Opaque: the inner `Clause`
/// stays crate-private.
#[derive(Default)]
pub struct ClauseCache(HashMap<String, Clause>);

impl ClauseCache {
    /// An empty cache.
    pub fn new() -> Self {
        Self::default()
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
    let mut index = HashMap::default();
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
    cache: &mut ClauseCache,
) -> Result<(Vec<Clause>, HashMap<String, usize>)> {
    let mut clauses = Vec::new();
    let mut index = HashMap::default();
    for step in steps {
        let crate::metamath::ProofStep::Label(label) = step else {
            continue;
        };
        if index.contains_key(label) {
            continue;
        }
        let Some(Statement::Assert(a)) = db.statement_by_label(label) else {
            continue;
        };
        // Reuse the compiled clause if we've seen this lemma before (this worker),
        // else compile it once and cache it.
        let clause = if let Some(c) = cache.0.get(label) {
            c.clone()
        } else if let Some(c) = clause_from(parser, a) {
            cache.0.insert(label.clone(), c.clone());
            c
        } else {
            continue; // a syntactic former (not a `|-` clause), or encode failure
        };
        index.insert(label.clone(), clauses.len());
        clauses.push(clause);
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
    replay_with(db, &parser, assertion, &steps, &rs, &clause_index, &mut ())
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
    // No interning (`&mut ()`), no clause reuse: preserves the historical
    // per-call behaviour. To reuse compiled clauses across many theorems of one
    // database (the import path), use [`derive_theorem_cached`].
    derive_inner(db, parser, label, &mut (), &mut ClauseCache::new())
}

/// [`derive_theorem_with`] threading a reusable [`ClauseCache`] — the import
/// path. Pass one cache across all of a worker's theorems so each cited lemma's
/// clause is compiled once, not re-parsed per proof.
pub fn derive_theorem_cached(
    db: &Database,
    parser: &Parser,
    label: &str,
    cache: &mut ClauseCache,
) -> Result<Thm> {
    derive_inner(db, parser, label, &mut (), cache)
}

/// [`derive_theorem_with`] threading a caller-supplied [`TrustedCons`] through
/// the whole replay — encoded statements, schema instances ([`Thm::all_elim_with`]),
/// and the final conclusion are all routed through `cons`.
///
/// Pass a persistent [`covalence_core::HashCons`] across many `derive_*` calls
/// from one database to **hash-cons the imported HOL terms into one shared DAG**:
/// metamath statements share enormous structure (the same constants, the same
/// sub-expressions) across theorems, so interning collapses the retained terms
/// ~15× (measured on hol.mm/set.mm) and makes the `Arc::ptr_eq` fast path fire
/// during the replay's term comparisons. It also makes the result printable with
/// sharing (the cons *is* the DAG), the basis for pretty-printing the HOL
/// meaning of metamath definitions without materialising the massive tree.
pub fn derive_theorem_with_cons(
    db: &Database,
    parser: &Parser,
    label: &str,
    cons: &mut dyn TrustedCons,
) -> Result<Thm> {
    derive_inner(db, parser, label, cons, &mut ClauseCache::new())
}

/// The shared derive path: scope the proof's clauses (reusing `cache`), build the
/// rule set, and replay (routing constructed terms through `cons`).
fn derive_inner(
    db: &Database,
    parser: &Parser,
    label: &str,
    cons: &mut dyn TrustedCons,
    cache: &mut ClauseCache,
) -> Result<Thm> {
    let assertion = match db.statement_by_label(label) {
        Some(Statement::Assert(a)) if a.proof.is_some() => a,
        Some(Statement::Assert(_)) => {
            return Err(replay_err(format!(
                "`{label}` is an axiom (no proof to replay)"
            )));
        }
        _ => {
            return Err(replay_err(format!(
                "`{label}` is not a theorem of the database"
            )));
        }
    };
    let steps = crate::metamath::proof_steps(db, assertion)
        .map_err(|e| replay_err(format!("decoding proof: {e}")))?;
    let (clauses, clause_index) = scoped_clauses(db, parser, &steps, cache)?;
    let rs = clauses_to_ruleset(clauses);
    replay_with(db, parser, assertion, &steps, &rs, &clause_index, cons)
}

/// One theorem's interned **surface**: its encoded conclusion and essential
/// hypotheses (the `⌜S⌝` / `⌜eᵢ⌝` statement encodings), hash-consed into a
/// shared interner. This is the *displayed / retained* HOL form — what you
/// pretty-print — as opposed to the (transient, heavy) proof.
#[derive(Debug, Clone)]
pub struct InternedDecl {
    pub label: String,
    /// The interned encoded conclusion `⌜S⌝`.
    pub concl: Term,
    /// The interned encoded essential hypotheses `⌜eᵢ⌝`, in frame order.
    pub hyps: Vec<Term>,
}

/// **Pass 1 of a two-pass import.** On a *single thread*, encode and hash-cons
/// every listed assertion's conclusion + essential hypotheses into `cons`.
///
/// This is the cheap pass: it only parses/encodes each *statement* once — it
/// does **not** replay proofs. Metamath statements share enormous structure
/// across theorems (the same constants, the same sub-expressions), so the
/// resulting interner is a compact shared DAG (~15–20× fewer nodes than the sum
/// of the statement trees; see `tests::measure_dedup`). That DAG is the basis
/// for pretty-printing the HOL form and for cheap retention of the whole
/// imported surface.
///
/// Pass 2 then *proves* each theorem in parallel via
/// [`crate::metalogic::mm_import::import_theorems_parallel`] — deliberately
/// **without** interning, so the heavy intermediate proof terms stay transient
/// and proving keeps full speed. Pass a single-threaded `cons` here (no `Sync`
/// needed); the proofs in pass 2 are verified against these same statements.
///
/// `labels` may include syntactic-former / `df-*` definition assertions as well
/// as `|-` theorems — anything whose surface you want in the shared DAG.
pub fn intern_surface(
    db: &Database,
    parser: &Parser,
    labels: &[String],
    cons: &mut dyn TrustedCons,
) -> Result<Vec<InternedDecl>> {
    let mut out = Vec::with_capacity(labels.len());
    for label in labels {
        let Some(Statement::Assert(a)) = db.statement_by_label(label) else {
            continue;
        };
        let concl = parser.encode_expr(&a.conclusion)?.cons_with(cons);
        let hyps = a
            .frame
            .essentials
            .iter()
            .map(|h| Ok(parser.encode_expr(&h.expr)?.cons_with(cons)))
            .collect::<Result<Vec<_>>>()?;
        out.push(InternedDecl {
            label: label.clone(),
            concl,
            hyps,
        });
    }
    Ok(out)
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
    cons: &mut dyn TrustedCons,
) -> Result<Thm> {
    if assertion.proof.is_none() {
        return Err(replay_err("assertion has no proof to replay"));
    }

    // Build the rule-set's `{Closed d} ⊢ Closed d` assumption and *all* its
    // conjuncts ONCE per theorem (was: rebuilt on every `|-` step in
    // `derive_clause` — `closed_for_var` + `assume` + O(k) `nth_conjunct`,
    // i.e. O(S·D) big-term work). Now each `|-` step just clones the cached
    // conjunct (an `Arc` bump) and `all_elim`s its args.
    let clause_ctx = ClauseCtx::new(rs, cons)?;

    let mut stack: Vec<Slot> = Vec::new();
    let mut heap: Vec<Slot> = Vec::new();
    // `$e` essential hypotheses are referenced once per *use* in the proof, but
    // each reference builds the identical open form `{Closed d, Derivable ⌜h⌝}
    // ⊢ d ⌜h⌝` — and that build rebuilds the whole `Closed_L` conjunction
    // (`derivable` → `closed_conj`, O(#clauses)). Cache the built slot per `$e`
    // label so it is constructed once and cloned (an `Arc` bump) thereafter —
    // turning O(refs · clauses) into O(#distinct-hyps · clauses).
    let mut ess_cache: HashMap<String, Slot> = HashMap::default();

    for step in steps {
        match step {
            crate::metamath::ProofStep::Label(label) => {
                let slot = apply_label(
                    db,
                    rs,
                    clause_index,
                    &clause_ctx,
                    parser,
                    label,
                    &mut stack,
                    &mut ess_cache,
                    cons,
                )?;
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
                // `thm` is the **open** form `{Closed d} ∪ E ⊢ d ⌜S⌝`. Discharge
                // `Closed d` and generalise `d` ONCE here (vs once per `|-` step)
                // → `E ⊢ ∀d. Closed d ⟹ d ⌜S⌝` = `E ⊢ Derivable_L ⌜S⌝`.
                let derivable_thm = thm
                    .imp_intro(&clause_ctx.closed_t)?
                    .all_intro("d", clause_ctx.pred_ty.clone())?;
                // Sanity: the re-derived theorem is the derivability of the
                // claimed conclusion's encoding. Reuse the already-built `parser`
                // and cached `Closed d` — `Derivable_L A` is `∀d. closed_t ⟹ d A`.
                let concl_enc = parser.encode_expr(&assertion.conclusion)?.cons_with(cons);
                let want = clause_ctx
                    .closed_t
                    .clone()
                    .imp(clause_ctx.d.clone().apply(concl_enc)?)?
                    .forall("d", clause_ctx.pred_ty.clone())?;
                if derivable_thm.concl() != &want {
                    eprintln!("=== PROOF-BUILT concl ===\n{:#?}", derivable_thm.concl());
                    eprintln!("=== ENCODE want ===\n{:#?}", want);
                    return Err(replay_err(format!(
                        "replayed conclusion does not match the claimed `{}`",
                        crate::metamath::expr::render(&assertion.conclusion),
                    )));
                }
                Ok(derivable_thm)
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
// Threads the full replay state (database, rules, caches, cons) through one
// proof step; bundling into a struct would just rename the problem.
#[allow(clippy::too_many_arguments)]
fn apply_label(
    db: &Database,
    rs: &RuleSet,
    clause_index: &HashMap<String, usize>,
    clause_ctx: &ClauseCtx,
    parser: &Parser,
    label: &str,
    stack: &mut Vec<Slot>,
    ess_cache: &mut HashMap<String, Slot>,
    cons: &mut dyn TrustedCons,
) -> Result<Slot> {
    let stmt = db
        .statement_by_label(label)
        .ok_or_else(|| replay_err(format!("unknown proof label `{label}`")))?;
    match stmt {
        Statement::Float(f) => {
            // `$f <typecode> <var>` — push the metavariable as a plain term.
            Ok(Slot::Wff(Term::free(mv(&f.var), phi()).cons_with(cons)))
        }
        Statement::Essential(h) => {
            // `$e |- <hyp>` — its derivability is *assumed* (surfaces as a hyp of
            // the final theorem). Kept in the **open** form `{Closed d, Derivable
            // ⌜hyp⌝} ⊢ d ⌜hyp⌝` (instantiate `∀d`, discharge `Closed d` against
            // the cached assumption) so the proof never re-opens/re-closes it.
            // Built once per `$e` label and cached: every later reference clones
            // the slot instead of rebuilding the full `Closed_L` conjunction.
            if let Some(slot) = ess_cache.get(label) {
                return Ok(slot.clone());
            }
            let enc = parser.encode_expr(&h.expr)?.cons_with(cons);
            let open = Thm::assume(derivable(rs, &enc)?)?
                .all_elim_with(clause_ctx.d.clone(), cons)?
                .imp_elim(clause_ctx.assumed.clone())?;
            let slot = Slot::Proved(open);
            ess_cache.insert(label.to_string(), slot.clone());
            Ok(slot)
        }
        Statement::Assert(target) => {
            apply_assert(parser, clause_index, clause_ctx, target, label, stack, cons)
        }
        _ => Err(replay_err(format!("label `{label}` is not applicable"))),
    }
}

/// Apply a target assertion during replay: pop its mandatory operands (floats
/// first, then essentials, in frame order) and dispatch on whether it is a
/// syntactic former or a `|-` rule.
fn apply_assert(
    parser: &Parser,
    clause_index: &HashMap<String, usize>,
    clause_ctx: &ClauseCtx,
    target: &Assertion,
    label: &str,
    stack: &mut Vec<Slot>,
    cons: &mut dyn TrustedCons,
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
            Slot::Proved(_) => Err(replay_err(format!(
                "`{label}`: float operand {i} is not a wff"
            ))),
        })
        .collect::<Result<_>>()?;

    if target.conclusion.typecode() != "|-" {
        // --- syntactic former: build the encoded instance, no proof ---
        // The float args are already compact sub-trees; re-fold the former's
        // conclusion body with each metavar filled by its arg. This is the
        // *same* compact encoding `Parser` produces for a literal of this
        // shape, so substitution into a `|-` schema (via `all_elim`) matches.
        let enc = encode_former(parser, target, label, &float_args)?.cons_with(cons);
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
        derive_clause(clause_ctx, k, &float_args, prems, cons).map(Slot::Proved)
    }
}

/// Encode a **syntactic-former application** during replay: structurally parse
/// the former's conclusion body **as its own typecode**, mapping each float
/// metavariable `target.frame.floats[i].var` to the i-th popped argument
/// sub-tree `float_args[i]`. The structured parse (rather than a flat
/// right-fold of the raw body) is required for *syntactic theorems* like
/// set.mm's `bj-0 $p wff ( ( ph -> ps ) -> ch )`, whose body contains a nested
/// former (`( ph -> ps )`) written out in literal tokens: parsing groups that
/// sub-expression so the result is identical to [`Parser::encode_expr`] of the
/// same instance. For an ordinary atomic-bodied former (`wi`'s `( ph -> ps )`,
/// metavars in leaf positions) the two encodings already agree.
fn encode_former(
    parser: &Parser,
    target: &Assertion,
    label: &str,
    float_args: &[Term],
) -> Result<Term> {
    let body = body_of(&target.conclusion)
        .ok_or_else(|| replay_err(format!("`{label}`: malformed former conclusion")))?;
    let mut subst: Vec<(&str, Term)> = Vec::with_capacity(target.frame.floats.len());
    for (i, f) in target.frame.floats.iter().enumerate() {
        subst.push((f.var.as_str(), float_args[i].clone()));
    }
    let toks: Vec<&str> = body.iter().map(|s| s.as_str()).collect();
    let tc = target.conclusion.typecode();
    let (term, rest) = parser.parse_subst(tc, &toks, &subst)?;
    if !rest.is_empty() {
        return Err(replay_err(format!(
            "`{label}`: trailing symbols after parsing former body"
        )));
    }
    Ok(term)
}

/// **Per-theorem precomputed clause assumptions.** Built ONCE per theorem (was:
/// rebuilt on every `|-` proof step inside `derive_clause`), this caches the
/// rule set's `{Closed d} ⊢ Closed d` assumption, the predicate variable `d`,
/// the `Closed d` term (for the final `imp_intro`), and — the big win — **all
/// `n` conjuncts already extracted** into an `O(1)`-indexable `Vec<Thm>`.
///
/// Extracting all conjuncts up front is O(n) total (one left walk peeling
/// `and_elim_r`/`and_elim_l`), versus a per-step `nth_conjunct(k)` which would
/// be O(k) each → O(S·D) across a proof. Each `Thm` is `Arc`-backed, so cloning
/// a cached conjunct is a cheap refcount bump.
struct ClauseCtx {
    d: Term,
    closed_t: Term,
    assumed: Thm,
    pred_ty: Type,
    conjuncts: Vec<Thm>,
}

impl ClauseCtx {
    fn new(rs: &RuleSet, cons: &mut dyn TrustedCons) -> Result<Self> {
        let d = rs.d_var();
        // Lay the clauses out ONCE (was: `n_clauses` laid them out to count, then
        // `closed_for_var` laid them out again to conjoin — two full builds of D
        // `bool` terms per theorem). One build gives us both the count and the
        // `Closed d` conjunction. Intern each laid-out clause so the schema
        // interiors dedup across theorems (and with the encoded statements that
        // `all_elim_with` substitutes into them).
        let clause_terms: Vec<Term> = (rs.clauses)(&|f| d.clone().apply(f.clone()))?
            .into_iter()
            .map(|t| t.cons_with(cons))
            .collect();
        let n = clause_terms.len();
        let closed_t = conj(clause_terms)?;
        let assumed = Thm::assume(closed_t.clone())?; // {Closed d} ⊢ Closed d
        // Extract all n conjuncts in ONE pass (`Thm::into_conjuncts`): O(n)
        // rather than an O(n²) walk of `and_elim_l`/`and_elim_r`, each of
        // which would re-type-check the (shrinking but still O(n)) tail *and*
        // the whole `Closed d` hypothesis — which would make proofs citing
        // hundreds of lemmas (cantnf*, yonedainv, psdmul) blow up. For an empty
        // rule set `Closed d = T` is a *non*-conjunction, so there are no
        // clauses.
        let conjuncts = if n == 0 {
            Vec::new()
        } else {
            assumed.clone().into_conjuncts()
        };
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
fn derive_clause(
    ctx: &ClauseCtx,
    k: usize,
    args: &[Term],
    prems: Vec<Thm>,
    cons: &mut dyn TrustedCons,
) -> Result<Thm> {
    // {Closed d} ⊢ ∀floats. (prem_conj ⟹)? d ⌜concl⌝ — clone the cached conjunct.
    let mut clause = ctx
        .conjuncts
        .get(k)
        .ok_or_else(|| replay_err(format!("clause index {k} out of range")))?
        .clone();
    for a in args {
        // `all_elim_with`: the (already-interned) arg is inserted by reference at
        // the binder, and the schema interior is interned against `cons` — so the
        // substitution instance is built as a shared DAG, not a fresh tree.
        clause = clause.all_elim_with(a.clone(), cons)?; // strip float_vars[0..] in order
    }

    // Stay in the **open** form `{Closed d} ∪ … ⊢ d ⌜concl⌝`. Premises are
    // already open (essentials and earlier `|-` steps both produce open slots),
    // so they conjoin directly — no per-premise `∀d`-instantiate/`Closed`-
    // discharge, and crucially **no per-step `imp_intro`/`all_intro`**: the
    // single `Closed d ⟹ … ∀d` discharge happens once, in `replay_with`. (The
    // old design closed every step and the next step re-opened it — O(steps)
    // closes over the large `Closed d`.)
    if prems.is_empty() {
        Ok(clause) // {Closed d} ⊢ d ⌜concl⌝
    } else {
        clause.imp_elim(conj_thms(prems)?) // {…} ⊢ d ⌜concl⌝
    }
}

// ============================================================================
// Tests — genericity over three unrelated databases (one function, three logics)
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[ignore = "repro bj-1"]
    fn repro_bj1() {
        let path = std::env::var("COV_SET_MM").expect("COV_SET_MM");
        let source = std::fs::read_to_string(&path).expect("read set.mm");
        let db = crate::metamath::parse(&source).expect("set.mm parses");
        let parser = Parser::new(&db);
        let a = db.assertions().find(|a| a.label == "bj-1").expect("bj-1");
        let thm = derive_theorem_with(&db, &parser, "bj-1").expect("replay bj-1");
        let rs = rule_set(&db);
        let expected = derivable(&rs, &encode_conclusion(&db, a).unwrap()).unwrap();
        if thm.concl() != &expected {
            eprintln!("PROOF-BUILT:\n{:#?}", thm.concl());
            eprintln!("ENCODE_EXPR:\n{:#?}", expected);
        }
        assert_eq!(thm.concl(), &expected, "bj-1 concl mismatch");
    }

    /// **Regression for the `bj-1` mismatch** (a *nesting* syntactic former).
    ///
    /// The proof applies a syntactic `$p` theorem `bj0` — proving the *compound*
    /// wff `( ( ph -> ps ) -> ch )` — as a former, then the rule `id`
    /// (`|- ( ph -> ph )`) with that wff as `ph`. The buggy `encode_former`
    /// right-folded `bj0`'s literal body *flat*, so the inner `( ph -> ps )` was
    /// not nested as a sub-tree; the proof-built encoding then disagreed with
    /// `encode_expr` of the stated conclusion and replay failed the final check.
    /// The fix parses the former body structurally before substituting. This is
    /// the minimal `.mm` reproducing the exact `( p -> p )`, `p := ((ph->ps)->ch)`
    /// shape of set.mm's `bj-1`.
    #[test]
    fn replay_nesting_former_bj1_shape() {
        // `bj0` is a syntactic `$p` theorem proving the *compound* wff
        // `( ( ph -> ps ) -> ch )`; `idax` is `|- ( ph -> ph )` (an axiom here —
        // the exact `|-` rule shape is irrelevant; what matters is applying it
        // with the compound `bj0`-built wff substituted for `ph`). `bj1` does
        // exactly that, reproducing set.mm `bj-1`'s `( p -> p )` shape.
        let src = format!(
            "{PROP}\n\
            bj0 $p wff ( ( ph -> ps ) -> ch ) $=\n\
              wph wps wi wch wi $.\n\
            idax $a |- ( ph -> ph ) $.\n\
            bj1 $p |- ( ( ( ph -> ps ) -> ch ) -> ( ( ph -> ps ) -> ch ) ) $=\n\
              wph wps wch bj0 idax $.\n"
        );
        let db = crate::metamath::parse(&src).unwrap();
        // The Metamath verifier accepts both `$p` proofs (`bj0` and `bj1`).
        assert_eq!(crate::metamath::verify_all(&db).unwrap(), 2);

        let a = db.assertions().find(|a| a.label == "bj1").unwrap();

        // Full-database rule set (`replay_db`): the conclusion is exactly
        // `Derivable_L ⌜concl⌝` for the *structured* encoding of the stated
        // conclusion (the proof-built encoding now matches `encode_expr`).
        let thm = replay_db(&db, a).unwrap();
        assert!(thm.hyps().is_empty(), "bj1 replay must be hypothesis-free");
        let rs = rule_set(&db);
        let expected = derivable(&rs, &encode_conclusion(&db, a).unwrap()).unwrap();
        assert_eq!(thm.concl(), &expected);

        // The proof-scoped fast path (`derive_theorem`) also succeeds: its final
        // self-check (proof-built `concl()` vs `encode_expr`) is the exact check
        // set.mm's `bj-1` was failing. A successful return *is* that match.
        let scoped = derive_theorem(&db, "bj1").unwrap();
        assert!(scoped.hyps().is_empty());
    }

    /// The real `bj-1` from set.mm — the first set.mm theorem whose proof uses a
    /// nesting syntactic former (`bj-0`). Gated on `COV_SET_MM`.
    #[test]
    fn replay_set_mm_bj1() {
        let Ok(path) = std::env::var("COV_SET_MM") else {
            eprintln!("skipping replay_set_mm_bj1 (set COV_SET_MM to run)");
            return;
        };
        let source = std::fs::read_to_string(&path).expect("read set.mm");
        let db = crate::metamath::parse(&source).expect("set.mm parses");
        let parser = Parser::new(&db);
        // `derive_theorem_with` returning `Ok` *is* the assertion: its final
        // self-check compares the proof-built `concl()` against
        // `encode_expr(conclusion)` and errors on mismatch — the exact check
        // that was failing before the fix. The result is genuine + oracle-free.
        let thm = derive_theorem_with(&db, &parser, "bj-1").expect("bj-1 replays");
        assert!(thm.hyps().is_empty(), "bj-1 is hypothesis-free");
    }

    /// The vendored real `hol.mm` (CC0; all 151 `$p` proofs are *compressed*).
    const HOL_MM: &str = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../../proof/metamath/tests/fixtures/hol.mm"
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
            let _thm = derive_theorem_with(&db, &parser, label)
                .unwrap_or_else(|e| panic!("hol.mm `{label}` failed: {e}"));
            timings.push((label.clone(), t.elapsed()));
        }
        let total = t0.elapsed();
        timings.sort_by_key(|t| std::cmp::Reverse(t.1));
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
                "a1i", "mp2", "syl", "3syl", "sylib", "mpbir", "imim1i", "con2d", "pm2.61i",
                "ax12v", "19.21t", "exlimdv", "dvelimhw",
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
            timings.sort_by_key(|t| std::cmp::Reverse(t.1));
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

    /// Count a term as a **tree** (following shared `Arc`s repeatedly — what a
    /// naive structural printer would emit).
    fn tree_size(t: &Term) -> u64 {
        use covalence_core::term::TermKind;
        1 + match t.kind() {
            TermKind::App(f, x) => tree_size(f) + tree_size(x),
            TermKind::Abs(_, b) => tree_size(b),
            _ => 0,
        }
    }

    /// **Dedup measurement**: how much does hash-consing shrink the imported
    /// theorem terms? Reports the summed tree-node count vs the distinct
    /// structural nodes once every conclusion is interned into one shared
    /// [`HashCons`] (the fully-shared cross-theorem DAG). Run:
    /// `cargo test -p covalence-hol --lib --release \
    ///   metalogic::mm_database::tests::measure_dedup -- --ignored --nocapture`
    #[test]
    #[ignore = "measurement; run with --ignored --nocapture"]
    fn measure_dedup() {
        use covalence_core::HashCons;

        let report = |name: &str, source: &str, limit: usize| {
            let db = crate::metamath::parse(source).expect("parses");
            let parser = Parser::new(&db);
            let labels: Vec<String> = db
                .assertions()
                .filter(|a| a.proof.is_some() && a.conclusion.typecode() == "|-")
                .map(|a| a.label.clone())
                .take(limit)
                .collect();

            // Pass 1 (single-thread): intern every conclusion + hypothesis.
            let mut cons = HashCons::new();
            let t_pass1 = std::time::Instant::now();
            let decls = intern_surface(&db, &parser, &labels, &mut cons)
                .unwrap_or_else(|e| panic!("{name} intern_surface failed: {e}"));
            let pass1_ms = t_pass1.elapsed();
            // Tree-size of the same surface (conclusions + hyps), un-interned.
            let mut tree_total: u64 = 0;
            let mut max_tree: u64 = 0;
            for d in &decls {
                let sz = tree_size(&d.concl) + d.hyps.iter().map(tree_size).sum::<u64>();
                tree_total += sz;
                max_tree = max_tree.max(sz);
            }
            let dag = cons.len() as u64;

            // Pass 2 (the import's actual path): prove each, plain / no interning.
            let t_pass2 = std::time::Instant::now();
            for label in &labels {
                let _ = derive_theorem_with(&db, &parser, label)
                    .unwrap_or_else(|e| panic!("{name} `{label}` failed: {e}"));
            }
            let pass2_ms = t_pass2.elapsed();
            eprintln!(
                "\n=== {name}: {} thms ===\n  surface tree nodes : {tree_total}\n  max single tree    : {max_tree}\n  shared DAG nodes   : {dag}\n  dedup factor       : {:.1}x\n  pass1 intern (1thr): {pass1_ms:?}\n  pass2 prove (plain): {pass2_ms:?}",
                labels.len(),
                tree_total as f64 / dag.max(1) as f64,
            );
        };

        report("hol.mm", HOL_MM, usize::MAX);
        if let Ok(path) = std::env::var("COV_SET_MM") {
            let source = std::fs::read_to_string(&path).expect("read set.mm");
            report("set.mm (first 2000)", &source, 2000);
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

        let rs = rule_set(&db);
        let expected = derivable(&rs, &encode_conclusion(&db, a).unwrap()).unwrap();
        assert_eq!(thm.concl(), &expected);
    }
}
