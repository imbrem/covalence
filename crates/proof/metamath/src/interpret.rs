//! Cross-database **interpretation** metatheorems: symbol renaming and
//! statement-preserving maps between Metamath databases, with O(1)
//! existence-transport of derivability.
//!
//! This is the general form of the axiom-set [`Implication`](crate::axioms)
//! (which is the special case *same database, σ = identity, witnesses only for
//! the weaker set's axioms*). Here the source and target may be **different
//! databases** related by a symbol map σ — the "anything derivable in IZF is
//! derivable in ZF" shape, where σ is (often) the identity on shared syntax.
//!
//! ## Renaming (the isomorphism metatheorem)
//!
//! [`Database::map_symbols`](crate::Database::map_symbols) applies an injective,
//! kind-preserving symbol map to an entire database. **Metatheorem:** a symbol
//! renaming is an isomorphism of the substitution calculus. Substitution
//! splices symbol sequences positionally ([`crate::subst`]); frame computation
//! and `$d` checking only ask "is this symbol a variable?" and "are these two
//! variables distinct?" — both preserved by an injective kind-preserving map.
//! Therefore every proof that verifies against a database verifies **verbatim**
//! against the renamed database, and derivability is preserved in *both*
//! directions. (Injectivity is essential: a non-injective map could identify
//! two variables and collapse a `$d`, unsoundly.)
//!
//! ## Interpretation + existence-transport
//!
//! An [`Interpretation`] from `src` to `tgt` is: a symbol map σ (injective and
//! kind-preserving on `src`'s declared symbols, mapping into `tgt`'s symbols),
//! together with, for **every** `$a` statement of `src` (syntax formers,
//! definitions, and logical axioms alike), a `tgt` **witness** assertion whose
//! statement is exactly σ(the src axiom's statement) — same conclusion, same
//! essentials in order, same mandatory-variable typing, and the witness's
//! mandatory `$d` ⊆ σ(the src axiom's `$d`). Witnesses are found by an override
//! map or auto-searched by statement key.
//!
//! **Transport metatheorem** (`InterpretationCert::transport`): if σ is such an
//! interpretation, then for every `src` assertion `L` there exists a `tgt`
//! derivation of σ(statement of `L`). *Proof, by induction on the src
//! derivation DAG* (an assertion's proof cites earlier assertions; the relation
//! is well-founded): a step applying src assertion `X` with substitution `s`
//! maps to using `X`'s witness `W` with substitution σ∘s. For a `$a` axiom `X`,
//! `W` is a single tgt assertion with statement σ(stmt X), so σ∘s applied to it
//! yields σ(s applied to stmt X) — σ commutes with substitution. For a `$p`
//! theorem `X`, `W` is `X` itself under σ and we appeal to the induction
//! hypothesis on `X`'s own derivation. σ injective on variables sends `$d`
//! obligations to `$d` obligations; the witness's ⊆-weaker `$d` keeps them
//! dischargeable; distinct dummy proof variables of `src` map to distinct
//! `tgt` variables. ∎
//!
//! **Caveat:** transport certifies the *existence* of a tgt derivation; it does
//! **not** materialise it (that is the point — the spliced derivation may be
//! astronomically large). Like [`crate::axioms`], these are Rust-level checked
//! certificates (untrusted tooling), not kernel `⊢ Derivable` theorems.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::axioms::{MetaError, axiom_closure, same_statement};
use crate::database::{Assertion, Database, FloatHyp, Frame, Hypothesis, Statement};
use crate::error::MmError;
use crate::expr::{Expr, Symbol, map_symbols};

/// Errors from interpretation checking.
#[derive(Debug, thiserror::Error)]
pub enum InterpError {
    #[error("σ is not injective on source symbols: `{a}` and `{b}` both map to `{image}`")]
    SigmaNotInjective { a: String, b: String, image: String },
    #[error("σ maps `{symbol}` to `{image}`: {detail}")]
    SigmaKind {
        symbol: String,
        image: String,
        detail: String,
    },
    #[error("source axiom `{src_axiom}` has no target witness{}",
        .tried.as_ref().map(|t| format!(" (tried `{t}`)")).unwrap_or_default())]
    NoWitness {
        src_axiom: String,
        tried: Option<String>,
    },
    #[error("target witness `{witness}` does not state σ(`{src_axiom}`): {reason}")]
    StatementMismatch {
        src_axiom: String,
        witness: String,
        reason: String,
    },
    #[error("`{label}` is not an assertion of the source database")]
    NotInSource { label: String },
    #[error(transparent)]
    Mm(#[from] MmError),
    #[error(transparent)]
    Meta(#[from] MetaError),
}

// --- assertion renaming (σ applied to a single assertion) ------------------

fn rename_float(h: &FloatHyp, f: &dyn Fn(&str) -> Symbol) -> FloatHyp {
    FloatHyp {
        label: h.label.clone(),
        typecode: f(&h.typecode).to_string(),
        var: f(&h.var).to_string(),
    }
}

fn rename_ess(h: &Hypothesis, f: &dyn Fn(&str) -> Symbol) -> Hypothesis {
    Hypothesis {
        label: h.label.clone(),
        expr: map_symbols(&h.expr, f),
    }
}

fn rename_frame(fr: &Frame, f: &dyn Fn(&str) -> Symbol) -> Frame {
    Frame {
        floats: fr.floats.iter().map(|h| rename_float(h, f)).collect(),
        essentials: fr.essentials.iter().map(|h| rename_ess(h, f)).collect(),
        disjoints: fr
            .disjoints
            .iter()
            .map(|(a, b)| (f(a).to_string(), f(b).to_string()))
            .collect(),
    }
}

/// σ applied to an assertion's *statement* (label/proof are irrelevant to
/// [`same_statement`]; we clear them).
fn rename_assertion(a: &Assertion, f: &dyn Fn(&str) -> Symbol) -> Assertion {
    Assertion {
        label: a.label.clone(),
        conclusion: map_symbols(&a.conclusion, f),
        frame: rename_frame(&a.frame, f),
        proof: None,
        scope_disjoints: Vec::new(),
    }
}

/// The statement key used to index target assertions for witness search:
/// conclusion plus essentials (in order). Frame typing and `$d` are confirmed
/// separately by [`same_statement`].
type StmtKey = (Expr, Vec<Expr>);

fn stmt_key(a: &Assertion) -> StmtKey {
    (
        a.conclusion.clone(),
        a.frame.essentials.iter().map(|h| h.expr.clone()).collect(),
    )
}

/// One resolved witness: a `src` `$a` axiom and the `tgt` assertion that states
/// its σ-image.
#[derive(Debug, Clone)]
pub struct InterpWitness {
    pub src_axiom: String,
    pub tgt_witness: String,
    /// Whether the target witness is itself a `$a` axiom (vs a `$p` theorem).
    pub tgt_is_axiom: bool,
    /// The `$a` axioms of `tgt` this witness transitively rests on (its
    /// [`axiom_closure`]) — lets callers see which target postulates the
    /// interpretation ultimately leans on.
    pub tgt_axioms_used: BTreeSet<String>,
}

/// A coverage report: which `src` `$a` statements matched a `tgt` witness and
/// which did not. [`check_interpretation`] is this plus "error if any
/// unmatched"; the raw report is for exploratory cross-database mapping (e.g.
/// iset.mm → set.mm) where partial coverage is expected.
#[derive(Debug, Clone, Default)]
pub struct Coverage {
    pub matched: Vec<InterpWitness>,
    /// `src` `$a` labels with no σ-image witness in `tgt`.
    pub unmatched: Vec<String>,
}

impl Coverage {
    /// Labels of matched src axioms, sorted.
    pub fn matched_labels(&self) -> BTreeSet<&str> {
        self.matched.iter().map(|w| w.src_axiom.as_str()).collect()
    }
}

/// Collect `src`'s declared symbols with their kind (`true` = variable).
fn declared_symbols(db: &Database) -> Vec<(String, bool)> {
    let mut out = Vec::new();
    for s in db.statements() {
        match s {
            Statement::Constant(ns) => out.extend(ns.iter().map(|n| (n.clone(), false))),
            Statement::Variable(ns) => out.extend(ns.iter().map(|n| (n.clone(), true))),
            _ => {}
        }
    }
    out
}

/// Check σ is injective and kind-preserving on `src`'s declared symbols, and
/// that each image is a `tgt` symbol of the same kind.
fn check_sigma(
    src: &Database,
    tgt: &Database,
    sigma: &dyn Fn(&str) -> Symbol,
) -> Result<(), InterpError> {
    let mut image: HashMap<String, String> = HashMap::new(); // image → source
    for (name, is_var) in declared_symbols(src) {
        let img = sigma(&name).to_string();
        if let Some(prev) = image.insert(img.clone(), name.clone()) {
            if prev != name {
                return Err(InterpError::SigmaNotInjective {
                    a: prev,
                    b: name,
                    image: img,
                });
            }
            continue;
        }
        if !tgt.is_symbol(&img) {
            return Err(InterpError::SigmaKind {
                symbol: name,
                image: img,
                detail: "image is not a declared symbol of the target".into(),
            });
        }
        let img_is_var = tgt.is_variable(&img);
        if img_is_var != is_var {
            return Err(InterpError::SigmaKind {
                symbol: name,
                image: img,
                detail: format!(
                    "kind mismatch: source {} maps to target {}",
                    if is_var { "variable" } else { "constant" },
                    if img_is_var { "variable" } else { "constant" },
                ),
            });
        }
    }
    Ok(())
}

/// Index `tgt` assertions by statement key. Multiple assertions may share a key
/// (an axiom and its restatements); we keep all, in source order, so witness
/// search can try each until [`same_statement`] confirms one.
fn build_index(tgt: &Database) -> HashMap<StmtKey, Vec<&Assertion>> {
    let mut idx: HashMap<StmtKey, Vec<&Assertion>> = HashMap::new();
    for a in tgt.assertions() {
        idx.entry(stmt_key(a)).or_default().push(a);
    }
    idx
}

/// Compute the coverage of an interpretation candidate (does not error on
/// unmatched src axioms — see [`check_interpretation`] for the strict form).
///
/// `overrides(src_label)` may name a specific `tgt` witness label for a src
/// axiom (used when auto-search by identical statement cannot find it — e.g.
/// the tgt states the axiom up to a definitional or `$d` variant). An override
/// that fails the [`same_statement`] check is a hard error (a wrong witness),
/// not a fallthrough to auto-search.
pub fn interpretation_coverage(
    src: &Database,
    tgt: &Database,
    sigma: &dyn Fn(&str) -> Symbol,
    overrides: &dyn Fn(&str) -> Option<String>,
) -> Result<Coverage, InterpError> {
    check_sigma(src, tgt, sigma)?;
    let index = build_index(tgt);
    let mut cov = Coverage::default();

    for ax in src.assertions() {
        if ax.proof.is_some() {
            continue; // only $a statements need witnesses
        }
        let renamed = rename_assertion(ax, sigma);

        // Candidate witnesses: an explicit override, else the index by key.
        let candidates: Vec<&Assertion> = if let Some(lbl) = overrides(&ax.label) {
            match tgt.statement_by_label(&lbl) {
                Some(Statement::Assert(a)) => vec![a],
                _ => {
                    return Err(InterpError::NoWitness {
                        src_axiom: ax.label.clone(),
                        tried: Some(lbl),
                    });
                }
            }
        } else {
            index.get(&stmt_key(&renamed)).cloned().unwrap_or_default()
        };

        // First candidate that passes the full same-statement check wins. If an
        // override was given, a mismatch is a hard error (it named a wrong
        // witness); for auto-search we simply fall through to "unmatched".
        let is_override = overrides(&ax.label).is_some();
        let mut matched = None;
        let mut last_err = None;
        for cand in &candidates {
            match same_statement(&renamed, cand) {
                Ok(()) => {
                    matched = Some(*cand);
                    break;
                }
                Err(e) => last_err = Some((cand.label.clone(), e)),
            }
        }

        match matched {
            Some(w) => {
                let closure = axiom_closure(tgt, &w.label)?;
                cov.matched.push(InterpWitness {
                    src_axiom: ax.label.clone(),
                    tgt_witness: w.label.clone(),
                    tgt_is_axiom: w.proof.is_none(),
                    tgt_axioms_used: closure,
                });
            }
            None if is_override => {
                let (witness, reason) = last_err.unwrap_or(("<none>".into(), "not found".into()));
                return Err(InterpError::StatementMismatch {
                    src_axiom: ax.label.clone(),
                    witness,
                    reason,
                });
            }
            None => cov.unmatched.push(ax.label.clone()),
        }
    }
    Ok(cov)
}

/// Every assertion of `tgt` whose statement equals `axiom`'s (via
/// [`same_statement`]: identical conclusion/essentials/float-typing, with the
/// candidate's `$d` ⊆ `axiom`'s). This is the identity-σ statement search used
/// for exploratory cross-database mapping (e.g. "does set.mm prove this exact
/// iset.mm axiom?") where a total symbol map is unavailable because the two
/// databases declare different symbol sets. Axioms sort before theorems.
pub fn matching_witnesses<'db>(tgt: &'db Database, axiom: &Assertion) -> Vec<&'db Assertion> {
    let mut hits: Vec<&Assertion> = tgt
        .assertions()
        .filter(|c| same_statement(axiom, c).is_ok())
        .collect();
    hits.sort_by_key(|a| a.proof.is_some()); // axioms (proof None) first
    hits
}

// --- α / variable-renaming statement matching -----------------------------

/// A bijective renaming of variable names discovered by
/// [`same_statement_mod_renaming`]: `forward` maps each `a`-variable to its
/// `b`-image, `backward` is its inverse. Both are total on the variables that
/// occur in the matched statement and mutually inverse (the map is a bijection).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Renaming {
    /// `a`-variable → `b`-variable.
    pub forward: BTreeMap<String, String>,
    /// `b`-variable → `a`-variable (the inverse of `forward`).
    pub backward: BTreeMap<String, String>,
}

impl Renaming {
    /// Try to extend the bijection with `a_var ↔ b_var`, returning `false` on a
    /// conflict (either direction already bound to a different partner). This is
    /// the injectivity guard in *both* directions — the soundness crux: a
    /// non-injective map could identify two distinct metavariables and mint a
    /// false witness.
    fn bind(&mut self, a_var: &str, b_var: &str) -> bool {
        // Check both directions BEFORE mutating, so a rejected bind leaves the
        // maps untouched (transactional — no stale forward entry on a backward
        // conflict).
        let fwd_ok = self.forward.get(a_var).is_none_or(|prev| prev == b_var);
        let bwd_ok = self.backward.get(b_var).is_none_or(|prev| prev == a_var);
        if !fwd_ok || !bwd_ok {
            return false;
        }
        self.forward.insert(a_var.to_string(), b_var.to_string());
        self.backward.insert(b_var.to_string(), a_var.to_string());
        true
    }
}

/// Match two flat expression bodies of `a` and `b` position-for-position under
/// `is_var`, binding variables into `ren`. Constants must be *identical*
/// (constants and typecodes are fixed under a variable renaming); a var must
/// match a var (kind-preserving), a constant must match the same constant.
fn match_symbols(
    a: &[Symbol],
    b: &[Symbol],
    is_var: &dyn Fn(&str) -> bool,
    ren: &mut Renaming,
) -> bool {
    if a.len() != b.len() {
        return false;
    }
    for (sa, sb) in a.iter().zip(b) {
        let (sa, sb) = (sa.as_str(), sb.as_str());
        match (is_var(sa), is_var(sb)) {
            (true, true) => {
                if !ren.bind(sa, sb) {
                    return false;
                }
            }
            (false, false) => {
                if sa != sb {
                    return false; // distinct constants — a renaming can't change these
                }
            }
            // A variable can never match a constant or vice versa.
            _ => return false,
        }
    }
    true
}

/// Match a single expression (typecode + body): the typecode is a constant and
/// must be identical; the body matches symbol-for-symbol under `is_var`.
fn match_expr(a: &Expr, b: &Expr, is_var: &dyn Fn(&str) -> bool, ren: &mut Renaming) -> bool {
    a.typecode() == b.typecode() && match_symbols(&a.body, &b.body, is_var, ren)
}

/// Do `a` and `b` assert the **same statement up to a consistent bijective
/// renaming of their variables**? Returns `Some(renaming)` iff `b`'s statement
/// is `a`'s conclusion + essentials (in order) under some bijection on variable
/// names, with constants and typecodes held fixed, matched float typecodes
/// agreeing, and `b`'s `$d` mapping *into* `a`'s (`ren`-image of each `b`-`$d`
/// pair is an `a`-`$d` pair). `None` on any conflict.
///
/// A Metamath schema is invariant under a consistent bijective renaming of its
/// variables ([`Database::map_symbols`](crate::Database::map_symbols) docs), so
/// a witness that matches `mod renaming` is a sound substitute at every use site
/// of the axiom — *provided* the renaming is a **bijection**. Non-injectivity
/// (two `a`-vars to one `b`-var, or the reverse) would identify distinct
/// metavariables and is rejected. `$d` is checked in the direction that keeps
/// the witness no *stronger* than the axiom: every distinctness the witness
/// requires (a `b`-`$d` pair, mapped back to `a`-vars) must already be granted
/// by `a`'s `$d`.
///
/// This is the α-variant of [`crate::axioms::same_statement`] (which demands
/// syntactic equality). `is_var(name)` classifies a symbol as a
/// variable; over a single database use `|s| db.is_variable(s)`. A caller whose
/// `is_var` misclassifies a constant as a variable cannot mint a false
/// renaming: every matched variable is required to carry an agreeing `$f`
/// typecode, and a constant has no `$f` — so the match is rejected.
pub fn same_statement_mod_renaming(
    a: &Assertion,
    b: &Assertion,
    is_var: &dyn Fn(&str) -> bool,
) -> Option<Renaming> {
    if a.frame.essentials.len() != b.frame.essentials.len() {
        return None;
    }
    let mut ren = Renaming::default();
    // Conclusion first, then essentials in order — one shared bijection.
    if !match_expr(&a.conclusion, &b.conclusion, is_var, &mut ren) {
        return None;
    }
    for (ha, hb) in a.frame.essentials.iter().zip(&b.frame.essentials) {
        if !match_expr(&ha.expr, &hb.expr, is_var, &mut ren) {
            return None;
        }
    }

    // Matched-variable float typecodes must agree: if a-var `x` was bound to
    // b-var `y`, their `$f` typecodes must be the same (a renaming preserves
    // typing). Every matched variable occurs in the conclusion/essentials, so
    // it is a *mandatory* variable and MUST have a floating hypothesis in a
    // well-formed frame — so we **require** both sides to have a typecode and
    // agree. This also hardens against a caller whose `is_var` misclassifies a
    // constant as a variable: a constant has no `$f`, so the pair has no
    // typecode on that side and the match is rejected rather than minting a
    // false renaming.
    let a_ty: BTreeMap<&str, &str> = a
        .frame
        .floats
        .iter()
        .map(|f| (f.var.as_str(), f.typecode.as_str()))
        .collect();
    let b_ty: BTreeMap<&str, &str> = b
        .frame
        .floats
        .iter()
        .map(|f| (f.var.as_str(), f.typecode.as_str()))
        .collect();
    for (av, bv) in &ren.forward {
        match (a_ty.get(av.as_str()), b_ty.get(bv.as_str())) {
            (Some(ta), Some(tb)) if ta == tb => {}
            _ => return None,
        }
    }

    // $d: every distinctness the witness `b` requires must be granted by `a`.
    // Map each b-$d pair back to a-vars via the bijection; it must be an a-$d
    // pair. A b-$d over a variable outside the bijection cannot be discharged,
    // so it fails.
    let a_pairs: BTreeSet<(String, String)> = a
        .frame
        .disjoints
        .iter()
        .map(|(x, y)| ordered(x, y))
        .collect();
    for (x, y) in &b.frame.disjoints {
        let (Some(ax), Some(ay)) = (ren.backward.get(x), ren.backward.get(y)) else {
            return None; // a b-$d variable with no a-preimage: undischargeable
        };
        if !a_pairs.contains(&ordered(ax, ay)) {
            return None;
        }
    }

    Some(ren)
}

fn ordered(x: &str, y: &str) -> (String, String) {
    if x <= y {
        (x.to_string(), y.to_string())
    } else {
        (y.to_string(), x.to_string())
    }
}

/// Every assertion of `tgt` whose statement equals `axiom`'s **up to a
/// consistent bijective variable renaming** (via [`same_statement_mod_renaming`]
/// with `tgt`'s variable classification). The α-variant of
/// [`matching_witnesses`]: it also finds witnesses that state the same schema
/// with different bound-variable names (e.g. `|- ( ph -> ph )` witnessing
/// `|- ( ps -> ps )`). Axioms sort before theorems.
///
/// Each hit is paired with the discovered renaming so callers can see the
/// variable correspondence. `is_var` classifies `axiom`'s symbols; witnesses'
/// symbols are classified by `tgt`.
pub fn matching_witnesses_mod_renaming<'db>(
    tgt: &'db Database,
    axiom: &Assertion,
    is_var: &dyn Fn(&str) -> bool,
) -> Vec<(&'db Assertion, Renaming)> {
    // A symbol is a variable if it is a variable in either the axiom's world or
    // the target's — the two databases may declare different symbol sets, and a
    // name that is a var in one but a constant in the other is genuinely a
    // kind mismatch that `match_symbols`'s `(true,false)` arm rejects.
    let classify = |s: &str| is_var(s) || tgt.is_variable(s);
    let mut hits: Vec<(&Assertion, Renaming)> = tgt
        .assertions()
        .filter_map(|c| same_statement_mod_renaming(axiom, c, &classify).map(|r| (c, r)))
        .collect();
    hits.sort_by_key(|(a, _)| a.proof.is_some()); // axioms (proof None) first
    hits
}

/// A **checked interpretation**: every `src` `$a` axiom has a σ-image witness in
/// `tgt`. Holds the source/target/σ so [`transport`](Self::transport) can move
/// derivability claims across. Build with [`check_interpretation`].
pub struct InterpretationCert<'a> {
    src: &'a Database,
    tgt: &'a Database,
    sigma: &'a dyn Fn(&str) -> Symbol,
    witnesses: HashMap<String, InterpWitness>,
}

impl std::fmt::Debug for InterpretationCert<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("InterpretationCert")
            .field("witnesses", &self.witnesses.len())
            .finish_non_exhaustive()
    }
}

impl<'a> InterpretationCert<'a> {
    /// The per-axiom witnesses.
    pub fn witnesses(&self) -> impl Iterator<Item = &InterpWitness> {
        self.witnesses.values()
    }

    /// The target database being interpreted into.
    pub fn target(&self) -> &Database {
        self.tgt
    }

    /// **Existence-transport** (the metatheorem in the module docs): certify
    /// that a `tgt` derivation of σ(statement of `src_label`) exists, without
    /// materialising it. `src_label` may be any `src` assertion (`$a` or `$p`).
    pub fn transport(&self, src_label: &str) -> Result<TransportedTheorem, InterpError> {
        let Some(Statement::Assert(a)) = self.src.statement_by_label(src_label) else {
            return Err(InterpError::NotInSource {
                label: src_label.to_string(),
            });
        };
        // Target axioms the existence rests on: every src $a in src_label's
        // closure maps to its witness; union those witnesses' tgt closures.
        let mut tgt_axioms_used = BTreeSet::new();
        for src_ax in axiom_closure(self.src, src_label)? {
            let w = self
                .witnesses
                .get(&src_ax)
                .ok_or_else(|| InterpError::NoWitness {
                    src_axiom: src_ax.clone(),
                    tried: None,
                })?;
            tgt_axioms_used.extend(w.tgt_axioms_used.iter().cloned());
        }
        Ok(TransportedTheorem {
            src_label: src_label.to_string(),
            statement: map_symbols(&a.conclusion, self.sigma),
            essentials: a
                .frame
                .essentials
                .iter()
                .map(|h| map_symbols(&h.expr, self.sigma))
                .collect(),
            tgt_axioms_used,
        })
    }
}

/// The result of [`InterpretationCert::transport`]: the σ-image statement whose
/// `tgt`-derivability is certified, plus the target axioms the certified
/// existence rests on. The derivation itself is *not* built.
#[derive(Debug, Clone)]
pub struct TransportedTheorem {
    pub src_label: String,
    /// σ(conclusion of the source theorem) — provable in the target.
    pub statement: Expr,
    /// σ(essential hypotheses) — the transported theorem's premises.
    pub essentials: Vec<Expr>,
    /// The `$a` axioms of `tgt` the certified existence transitively rests on.
    pub tgt_axioms_used: BTreeSet<String>,
}

/// Check that σ is an interpretation of `src` into `tgt`: injective and
/// kind-preserving, with a σ-image witness for **every** `src` `$a` axiom.
/// Returns a certificate supporting O(1) [`transport`](InterpretationCert::transport).
///
/// The special case `src == tgt`, σ = identity, is exactly an
/// [`Implication`](crate::axioms::Implication) that witnesses *every* axiom
/// (rather than only a weaker set's).
pub fn check_interpretation<'a>(
    src: &'a Database,
    tgt: &'a Database,
    sigma: &'a dyn Fn(&str) -> Symbol,
    overrides: &dyn Fn(&str) -> Option<String>,
) -> Result<InterpretationCert<'a>, InterpError> {
    let cov = interpretation_coverage(src, tgt, sigma, overrides)?;
    if let Some(first) = cov.unmatched.first() {
        return Err(InterpError::NoWitness {
            src_axiom: first.clone(),
            tried: None,
        });
    }
    let witnesses = cov
        .matched
        .into_iter()
        .map(|w| (w.src_axiom.clone(), w))
        .collect();
    Ok(InterpretationCert {
        src,
        tgt,
        sigma,
        witnesses,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::make_expr;
    use crate::parse::parse;

    /// Source: implicational fragment {ax-mp, ax-1, ax-2} with a
    /// trivially-checkable theorem `th : |- ( ph -> ( ph -> ph ) )` (one step:
    /// instantiate ax-1 at ps := ph).
    const SRC: &str = "\
        $c wff |- ( ) -> $.\n\
        $v ph ps ch $.\n\
        wph $f wff ph $.\n\
        wps $f wff ps $.\n\
        wch $f wff ch $.\n\
        wi $a wff ( ph -> ps ) $.\n\
        ${ mp1 $e |- ph $.  mp2 $e |- ( ph -> ps ) $.  ax-mp $a |- ps $. $}\n\
        ax-1 $a |- ( ph -> ( ps -> ph ) ) $.\n\
        ax-2 $a |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $.\n\
        th $p |- ( ph -> ( ph -> ph ) ) $= wph wph ax-1 $.\n\
    ";

    /// Target with the SAME implicational fragment under a renaming
    /// (`->` ↦ `=>`, `ph` ↦ `P`, `ps` ↦ `Q`, `ch` ↦ `R`), plus an extra axiom
    /// `ax-3` and the corresponding theorem `tht`.
    fn tgt_fixed() -> &'static str {
        "\
        $c wff |- ( ) => $.\n\
        $v P Q R $.\n\
        wP $f wff P $.\n\
        wQ $f wff Q $.\n\
        wR $f wff R $.\n\
        wi $a wff ( P => Q ) $.\n\
        ${ mp1 $e |- P $.  mp2 $e |- ( P => Q ) $.  ax-mp $a |- Q $. $}\n\
        ax-1 $a |- ( P => ( Q => P ) ) $.\n\
        ax-2 $a |- ( ( P => ( Q => R ) ) => ( ( P => Q ) => ( P => R ) ) ) $.\n\
        ax-3 $a |- ( ( ( P => Q ) => P ) => P ) $.\n\
        tht $p |- ( P => ( P => P ) ) $= wP wP ax-1 $.\n\
    "
    }

    /// The renaming σ for the fixtures.
    fn sigma(s: &str) -> Symbol {
        match s {
            "->" => "=>".into(),
            "ph" => "P".into(),
            "ps" => "Q".into(),
            "ch" => "R".into(),
            other => other.into(),
        }
    }

    #[test]
    fn renaming_preserves_verification() {
        // demo0-style database renamed by a suffixing map still verifies.
        let src = "\
            $c 0 + = -> ( ) term wff |- $.\n\
            $v t r s P Q $.\n\
            tt $f term t $.\n\
            tr $f term r $.\n\
            ts $f term s $.\n\
            wp $f wff P $.\n\
            wq $f wff Q $.\n\
            tze $a term 0 $.\n\
            tpl $a term ( t + r ) $.\n\
            weq $a wff t = r $.\n\
            wim $a wff ( P -> Q ) $.\n\
            a1 $a |- ( t = r -> ( t = s -> r = s ) ) $.\n\
            a2 $a |- ( t + 0 ) = t $.\n\
            ${  min $e |- P $.  maj $e |- ( P -> Q ) $.  mp $a |- Q $.  $}\n\
            th1 $p |- t = t $= tt tze tpl tt weq tt tt weq tt a2 tt tze tpl \
                tt weq tt tze tpl tt weq tt tt weq wim tt a2 tt tze tpl \
                tt tt a1 mp mp $.\n";
        let db = parse(src).unwrap();
        assert_eq!(crate::verify_all(&db).unwrap(), 1);
        // Suffix every symbol with `_x` (injective, kind-preserving).
        let renamed = db.map_symbols(&|s| format!("{s}_x")).unwrap();
        assert_eq!(crate::verify_all(&renamed).unwrap(), 1);
        // A collision map (everything to one constant) is rejected.
        assert!(db.map_symbols(&|_| "z".to_string()).is_err());
    }

    #[test]
    fn interpretation_auto_finds_witnesses_and_transports() {
        let src = parse(SRC).unwrap();
        let tgt = parse(tgt_fixed()).unwrap();
        assert_eq!(crate::verify_all(&src).unwrap(), 1);
        assert_eq!(crate::verify_all(&tgt).unwrap(), 1);

        let cert = check_interpretation(&src, &tgt, &sigma, &|_| None)
            .expect("σ interprets the src implicational fragment into tgt");
        // Every src $a (wi, ax-mp, ax-1, ax-2) has a witness.
        assert_eq!(cert.witnesses().count(), 4);
        for w in cert.witnesses() {
            assert!(
                w.tgt_is_axiom,
                "{} → {} should be an axiom witness",
                w.src_axiom, w.tgt_witness
            );
        }

        // Transport `th`: σ(|- ( ph -> ( ph -> ph ) )) = |- ( P => ( P => P ) ).
        let t = cert.transport("th").unwrap();
        assert_eq!(
            t.statement,
            make_expr("|-", ["(", "P", "=>", "(", "P", "=>", "P", ")", ")"])
        );
        assert!(t.essentials.is_empty());
        // Sanity: the transported statement really is provable in tgt (tht).
        let tht = tgt.statement_by_label("tht").unwrap();
        let Statement::Assert(tht) = tht else {
            unreachable!()
        };
        assert_eq!(t.statement, tht.conclusion);
    }

    #[test]
    fn interpretation_missing_axiom_fails() {
        let src = parse(SRC).unwrap();
        // A target that lacks ax-2: check_interpretation requires every src $a
        // witnessed, so it fails on ax-2.
        let tgt = parse(
            "$c wff |- ( ) => $.\n$v P Q R $.\n\
             wP $f wff P $.\nwQ $f wff Q $.\nwR $f wff R $.\n\
             wi $a wff ( P => Q ) $.\n\
             ${ mp1 $e |- P $.  mp2 $e |- ( P => Q ) $.  ax-mp $a |- Q $. $}\n\
             ax-1 $a |- ( P => ( Q => P ) ) $.\n",
        )
        .unwrap();
        let err = check_interpretation(&src, &tgt, &sigma, &|_| None).unwrap_err();
        match err {
            InterpError::NoWitness { src_axiom, .. } => assert_eq!(src_axiom, "ax-2"),
            other => panic!("expected NoWitness for ax-2, got {other}"),
        }
        // But coverage still reports the 3 that DO match (wi, ax-mp, ax-1).
        let cov = interpretation_coverage(&src, &tgt, &sigma, &|_| None).unwrap();
        assert_eq!(cov.unmatched, ["ax-2"]);
        assert!(cov.matched_labels().contains("ax-1"));
    }

    // --- α / variable-renaming matching --------------------------------

    /// A one-axiom database whose sole `$a` states `|- ( <p> -> <p> )` over a
    /// variable `p` typed `wff`; used to build renaming fixtures.
    fn self_impl_db(var: &str, label: &str) -> Database {
        let src = format!(
            "$c wff |- ( ) -> $.\n$v {var} $.\n\
             w{var} $f wff {var} $.\n\
             {label} $a |- ( {var} -> {var} ) $.\n"
        );
        parse(&src).unwrap()
    }

    fn sole_axiom<'a>(db: &'a Database, label: &str) -> &'a Assertion {
        match db.statement_by_label(label).unwrap() {
            Statement::Assert(a) => a,
            _ => unreachable!(),
        }
    }

    #[test]
    fn renaming_matches_alpha_variant() {
        // |- ( ph -> ph ) matches |- ( ps -> ps ) with ph ↔ ps.
        let a_db = self_impl_db("ph", "aid");
        let b_db = self_impl_db("ps", "bid");
        let a = sole_axiom(&a_db, "aid");
        let b = sole_axiom(&b_db, "bid");
        let is_var = |s: &str| matches!(s, "ph" | "ps");
        let ren = same_statement_mod_renaming(a, b, &is_var)
            .expect("|- ( ph -> ph ) matches |- ( ps -> ps ) up to renaming");
        assert_eq!(ren.forward.get("ph").map(String::as_str), Some("ps"));
        assert_eq!(ren.backward.get("ps").map(String::as_str), Some("ph"));
    }

    #[test]
    fn renaming_rejects_non_injective() {
        // |- ( ph -> ps ) vs |- ( ph -> ph ): matching needs ph↦ph AND ps↦ph,
        // which is non-injective (two a-vars to one b-var) → None. A wrong
        // renaming here would be unsound.
        let a_db = parse(
            "$c wff |- ( ) -> $.\n$v ph ps $.\n\
             wph $f wff ph $.\nwps $f wff ps $.\n\
             adiff $a |- ( ph -> ps ) $.\n",
        )
        .unwrap();
        let b_db = self_impl_db("ph", "bid");
        let a = sole_axiom(&a_db, "adiff");
        let b = sole_axiom(&b_db, "bid");
        let is_var = |s: &str| matches!(s, "ph" | "ps");
        assert!(same_statement_mod_renaming(a, b, &is_var).is_none());
        // And the reverse (|- ( ph -> ph ) as `a`, |- ( ph -> ps ) as `b`) also
        // fails: ph↦ph then ph↦ps conflicts in the forward map.
        assert!(same_statement_mod_renaming(b, a, &is_var).is_none());
    }

    #[test]
    fn renaming_holds_constants_fixed() {
        // Same shape but a different constant connective (`->` vs `=>`) must NOT
        // match — constants are never renamed.
        let a_db = self_impl_db("ph", "aid");
        let b_db = parse(
            "$c wff |- ( ) => $.\n$v ph $.\n\
             wph $f wff ph $.\n\
             bid $a |- ( ph => ph ) $.\n",
        )
        .unwrap();
        let a = sole_axiom(&a_db, "aid");
        let b = sole_axiom(&b_db, "bid");
        let is_var = |s: &str| s == "ph";
        assert!(same_statement_mod_renaming(a, b, &is_var).is_none());
    }

    #[test]
    fn renaming_var_cannot_match_constant() {
        // A variable in `a` cannot align with a constant in `b` at the same slot.
        let a_db = self_impl_db("ph", "aid");
        // b: |- ( 0 -> 0 ) where 0 is a constant.
        let b_db = parse(
            "$c wff |- ( ) -> 0 $.\n\
             bid $a |- ( 0 -> 0 ) $.\n",
        )
        .unwrap();
        let a = sole_axiom(&a_db, "aid");
        let b = sole_axiom(&b_db, "bid");
        let is_var = |s: &str| s == "ph";
        assert!(same_statement_mod_renaming(a, b, &is_var).is_none());
    }

    #[test]
    fn renaming_witness_dd_must_be_granted() {
        // a grants $d ph ps; b requires $d over its renamed images → OK.
        let a_db = parse(
            "$c wff |- ( ) -> $.\n$v ph ps $.\n\
             wph $f wff ph $.\nwps $f wff ps $.\n\
             ${ $d ph ps $. aimp $a |- ( ph -> ps ) $. $}\n",
        )
        .unwrap();
        // b renames to P,Q and requires $d P Q.
        let b_db = parse(
            "$c wff |- ( ) -> $.\n$v P Q $.\n\
             wP $f wff P $.\nwQ $f wff Q $.\n\
             ${ $d P Q $. bimp $a |- ( P -> Q ) $. $}\n",
        )
        .unwrap();
        // b' requires NO $d — a stronger schema, still fine (⊆).
        let bnod_db = parse(
            "$c wff |- ( ) -> $.\n$v P Q $.\n\
             wP $f wff P $.\nwQ $f wff Q $.\n\
             bimp $a |- ( P -> Q ) $.\n",
        )
        .unwrap();
        // Classifier must cover both databases' variables (see
        // `matching_witnesses_mod_renaming`, which unions the two var sets).
        let is_var = |s: &str| matches!(s, "ph" | "ps" | "P" | "Q");
        let a = sole_axiom(&a_db, "aimp");
        assert!(same_statement_mod_renaming(a, sole_axiom(&b_db, "bimp"), &is_var).is_some());
        assert!(same_statement_mod_renaming(a, sole_axiom(&bnod_db, "bimp"), &is_var).is_some());

        // Now the reverse: a grants NO $d, b requires one → witness is STRONGER
        // in the wrong direction (needs distinctness a doesn't grant) → None.
        let anod_db = parse(
            "$c wff |- ( ) -> $.\n$v ph ps $.\n\
             wph $f wff ph $.\nwps $f wff ps $.\n\
             aimp $a |- ( ph -> ps ) $.\n",
        )
        .unwrap();
        assert!(
            same_statement_mod_renaming(
                sole_axiom(&anod_db, "aimp"),
                sole_axiom(&b_db, "bimp"),
                &is_var
            )
            .is_none()
        );
    }

    #[test]
    fn renaming_rejects_misclassified_constant() {
        // Hardening: a caller whose `is_var` wrongly classifies a *constant* as a
        // variable must not mint a false renaming. Here `0` is a constant in both
        // dbs (no `$f`), but `is_var` lies and calls it a variable. The two
        // statements would "match" `0 ↦ 1` structurally — but a matched variable
        // has no float typecode, so the typecode guard rejects it.
        let a_db = parse(
            "$c wff |- ( ) -> 0 1 $.\n\
             aid $a |- ( 0 -> 0 ) $.\n",
        )
        .unwrap();
        let b_db = parse(
            "$c wff |- ( ) -> 0 1 $.\n\
             bid $a |- ( 1 -> 1 ) $.\n",
        )
        .unwrap();
        let a = sole_axiom(&a_db, "aid");
        let b = sole_axiom(&b_db, "bid");
        let lying_is_var = |s: &str| matches!(s, "0" | "1"); // WRONG: 0,1 are constants
        assert!(
            same_statement_mod_renaming(a, b, &lying_is_var).is_none(),
            "a misclassified constant must not produce a renaming"
        );
    }

    #[test]
    fn matching_witnesses_mod_renaming_finds_alpha() {
        // tgt has |- ( ps -> ps ); axiom is |- ( ph -> ph ). Exact match fails,
        // renaming match succeeds.
        let tgt = self_impl_db("ps", "bid");
        let axiom_db = self_impl_db("ph", "aid");
        let axiom = sole_axiom(&axiom_db, "aid");
        // Exact matcher finds nothing (different variable name).
        assert!(matching_witnesses(&tgt, axiom).is_empty());
        // Renaming matcher finds `bid`.
        let is_var = |s: &str| s == "ph";
        let hits = matching_witnesses_mod_renaming(&tgt, axiom, &is_var);
        assert_eq!(hits.len(), 1);
        assert_eq!(hits[0].0.label, "bid");
    }

    #[test]
    fn override_wrong_witness_is_hard_error() {
        let src = parse(SRC).unwrap();
        let tgt = parse(tgt_fixed()).unwrap();
        // Force ax-1's witness to be ax-3 (wrong statement).
        let err = check_interpretation(&src, &tgt, &sigma, &|l| {
            (l == "ax-1").then(|| "ax-3".to_string())
        })
        .unwrap_err();
        assert!(
            matches!(err, InterpError::StatementMismatch { src_axiom, .. } if src_axiom == "ax-1")
        );
    }
}
