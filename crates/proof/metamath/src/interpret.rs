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

use std::collections::{BTreeSet, HashMap};

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
