//! **A high-level session over a real imported Metamath database.** The
//! deliverable of the composition engine: given a [`metamath::Database`], build a
//! [`MmSession`] and then
//!
//! - [`theorem`](MmSession::theorem)`(label)` re-derives `⊢ Derivable_L ⌜S⌝` for a
//!   stored `$p` theorem (via [`mm_database::replay_db`] — construct, don't trust);
//! - [`apply`](MmSession::apply)`(rule_label, floats, premises)` applies *any* of
//!   the database's `|-` rules (axiom or inference) in the HOL kernel to compose a
//!   *new* `⊢ Derivable_L (σ concl)` — including statements the database contains
//!   **no `$p` proof for** (the Metamath derivation is never written down, yet its
//!   existence is certified in HOL);
//! - [`mp`](MmSession::mp) is the convenience wrapper for an `ax-mp`-shaped rule.
//!
//! All results share the **same** `Derivable_L` head — `L = `[`mm_database::rule_set`]`(db)`,
//! the full-database rule set — so a `theorem(…)` result and an `apply(…)` result
//! compose directly (a `theorem` premise feeds an `apply`, and vice versa). Both
//! `replay_db` and `rule_set`/`clause_infos` iterate `db.assertions()` in database
//! order, so a clause index is consistent across all three.
//!
//! # Soundness (no new trusted code)
//!
//! Every theorem is built through [`mm_database::replay_db`] (a verified,
//! kernel-re-checked replay) or [`super::apply_rule`] (existing kernel rules
//! only). Nothing is postulated. `apply` re-checks each `imp_elim`/`all_elim`
//! through the kernel; a bad witness or premise fails a kernel check.
//!
//! # What `apply` checks vs. Metamath `$d`/typecodes (honest caveat)
//!
//! `apply` (like the replay it shares a rule set with) uses the **over-approximated**
//! rule set: each clause quantifies its metavariables over *all* of `Φ = nat`
//! rather than the metavariable's typecode sub-language, and **`$d`
//! (disjoint-variable) conditions are not enforced**. This is *sound for the
//! construct direction* we land in — a larger rule set only makes *more* formulas
//! derivable, and we only ever construct the specific witness the caller names —
//! but it means `apply` does **not** verify that a substitution respects `$d` or
//! that a float witness is a well-typed expression of the metavariable's typecode.
//! It is the caller's responsibility (as with `replay_db`) that the composed
//! instance is a legitimate Metamath step; the HOL theorem is genuine either way,
//! but a `$d`-violating composite would not be a valid Metamath proof. This is the
//! *same* caveat the replay carries. See [`SKELETONS.md`](./SKELETONS.md).

use fnv::FnvHashMap as HashMap;

use covalence_core::{Error, Result, Term};
use covalence_hol_eval::EvalThm as Thm;

use super::mm_database::{self, ClauseInfo, Parser};
use super::{RuleSet, apply_rule};
use crate::metamath::{Database, Expr, Statement};

fn session_err(msg: impl Into<String>) -> Error {
    Error::ConnectiveRule(format!("mm-session: {}", msg.into()))
}

/// A composition session over a real, imported Metamath database. Owns the
/// [`Database`], the full-database [`RuleSet`] `L`, and the per-`|-`-assertion
/// [`ClauseInfo`]s with a `label → clause index` map. See the [module docs](self).
pub struct MmSession {
    db: Database,
    rs: RuleSet<'static>,
    n_clauses: usize,
    clause_infos: Vec<ClauseInfo>,
    clause_index: HashMap<String, usize>,
}

impl MmSession {
    /// Build a session over `db`. Compiles the full-database rule set once (used
    /// by every [`apply`](Self::apply)) and the per-clause info + label index.
    pub fn new(db: Database) -> Result<Self> {
        let rs = mm_database::rule_set(&db);
        let n_clauses = rs.n_clauses()?;
        let (clause_infos, clause_index) = mm_database::clause_infos(&db);
        Ok(MmSession {
            db,
            rs,
            n_clauses,
            clause_infos,
            clause_index,
        })
    }

    /// The database this session wraps.
    pub fn database(&self) -> &Database {
        &self.db
    }

    /// The full-database rule set `L` (every result is `Derivable_L …`).
    pub fn rule_set(&self) -> &RuleSet<'static> {
        &self.rs
    }

    /// A fresh [`Parser`] over this session's database (for encoding witnesses).
    /// Building it is O(database size); [`encode`](Self::encode) builds one per
    /// call. Callers encoding *many* witnesses can build one [`Parser::new`]
    /// directly and reuse it.
    pub fn parser(&self) -> Parser<'_> {
        Parser::new(&self.db)
    }

    /// Encode a Metamath expression to its `Φ = nat` HOL term, so callers can
    /// build the float witnesses [`apply`](Self::apply) substitutes. Builds a
    /// fresh [`Parser`] per call (see [`parser`](Self::parser) to reuse one).
    pub fn encode(&self, e: &Expr) -> Result<Term> {
        self.parser().encode_expr(e)
    }

    /// **Re-derive `⊢ Derivable_L ⌜S⌝` for the stored `$p` theorem `label`.** Via
    /// [`mm_database::replay_db`] — a verified, kernel-re-checked replay (the
    /// Metamath verifier's say-so is not trusted). Errors if `label` is not a `$p`
    /// theorem of the database. Essential hypotheses of the assertion surface as
    /// the result's hypotheses.
    pub fn theorem(&self, label: &str) -> Result<Thm> {
        let assertion = match self.db.statement_by_label(label) {
            Some(Statement::Assert(a)) if a.proof.is_some() => a,
            Some(Statement::Assert(_)) => {
                return Err(session_err(format!(
                    "`{label}` is an axiom / has no proof to replay"
                )));
            }
            _ => {
                return Err(session_err(format!(
                    "`{label}` is not a theorem of the database"
                )));
            }
        };
        mm_database::replay_db(&self.db, assertion)
    }

    /// **Apply the database rule `rule_label` in the HOL kernel.** Instantiates
    /// the rule's clause: substitutes its metavariables by `float_witnesses` (in
    /// frame / binder order — `float_witnesses[0]` is the outermost binder) and
    /// discharges its essential antecedents with `premises`, yielding
    /// `⊢ Derivable_L (σ concl)`.
    ///
    /// `rule_label` must name a `|-` assertion (axiom or inference rule) of the
    /// database. `premises[i]` must be `⊢ Derivable_L (σ essᵢ)` for the rule's
    /// `i`-th essential. The number of premises must equal the rule's essential
    /// count and the number of witnesses its float count — a mismatch is a clear
    /// error. See the [module docs](self) for the `$d`/typecode caveat.
    pub fn apply(
        &self,
        rule_label: &str,
        float_witnesses: &[Term],
        premises: &[&Thm],
    ) -> Result<Thm> {
        let &k = self.clause_index.get(rule_label).ok_or_else(|| {
            session_err(format!("`{rule_label}` is not a `|-` rule of the database"))
        })?;
        let info = &self.clause_infos[k];
        if float_witnesses.len() != info.float_vars.len() {
            return Err(session_err(format!(
                "`{rule_label}` takes {} float witness(es), got {}",
                info.float_vars.len(),
                float_witnesses.len()
            )));
        }
        if premises.len() != info.ess_encs.len() {
            return Err(session_err(format!(
                "`{rule_label}` has {} essential premise(s), got {}",
                info.ess_encs.len(),
                premises.len()
            )));
        }
        apply_rule(&self.rs, k, self.n_clauses, float_witnesses, premises)
    }

    /// **Modus-ponens convenience** for an `ax-mp`-shaped rule. `rule_label`
    /// defaults to `"ax-mp"` when `None`. `major : ⊢ Derivable_L ⌜A⌝`,
    /// `minor : ⊢ Derivable_L ⌜A ⟹ B⌝`; `floats` are the two float witnesses the
    /// rule expects (frame order). Returns `⊢ Derivable_L ⌜B⌝`.
    ///
    /// This is exactly [`apply`](Self::apply)`(label, floats, &[major, minor])`
    /// with `label` defaulted — a thin, readable alias for the ubiquitous case.
    pub fn mp(
        &self,
        rule_label: Option<&str>,
        floats: &[Term],
        major: &Thm,
        minor: &Thm,
    ) -> Result<Thm> {
        let label = rule_label.unwrap_or("ax-mp");
        self.apply(label, floats, &[major, minor])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A minimal propositional-calculus database (wff former `wi`, axioms
    /// `ax-1`/`ax-2`, inference rule `ax-mp`) plus a `$p` theorem `a1i`.
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
        ${
          a1i.1 $e |- ph $.
          a1i $p |- ( ps -> ph ) $=
            wph  wps wph wi  a1i.1  wph wps ax-1  ax-mp $.
        $}
    ";

    fn parse(src: &str) -> Database {
        crate::metamath::parse(src).expect("parses")
    }

    fn mk_wff(body: &str) -> Expr {
        crate::metamath::expr::from_symbols(std::iter::once("wff").chain(body.split_whitespace()))
            .expect("non-empty")
    }
    fn mk_prov(body: &str) -> Expr {
        crate::metamath::expr::from_symbols(std::iter::once("|-").chain(body.split_whitespace()))
            .expect("non-empty")
    }

    /// Two `theorem()` results share the SAME `Derivable_L` head.
    #[test]
    fn theorem_shares_derivable_head() {
        let src = format!(
            "{PROP}\n\
            ${{\n\
              a2i.1 $e |- ph $.\n\
              a2i $p |- ( ps -> ph ) $=\n\
                wph  wps wph wi  a2i.1  wph wps ax-1  ax-mp $.\n\
            $}}\n"
        );
        let db = parse(&src);
        assert_eq!(crate::metamath::verify_all(&db).unwrap(), 2);
        let sess = MmSession::new(db).unwrap();

        let t1 = sess.theorem("a1i").unwrap();
        let t2 = sess.theorem("a2i").unwrap();
        // Both are `Derivable_L ⌜( ps -> ph )⌝` at the *same* rule-set head, hence
        // structurally equal (same conclusion, same one essential hypothesis).
        assert_eq!(t1.concl(), t2.concl(), "same Derivable_L head + statement");
        assert_eq!(t1.hyps().len(), 1);
        assert_eq!(t2.hyps().len(), 1);
    }

    /// `theorem()` re-derives a stored `$p` (`a1i`), carrying its one essential.
    #[test]
    fn theorem_replays_stored_p() {
        let db = parse(PROP);
        assert_eq!(crate::metamath::verify_all(&db).unwrap(), 1);
        let sess = MmSession::new(db).unwrap();
        let a1i = sess.theorem("a1i").unwrap();
        assert_eq!(a1i.hyps().len(), 1, "a1i carries its one essential |- ph");
        // Its conclusion is `Derivable_L ⌜( ps -> ph )⌝`.
        let want = super::super::derivable(
            sess.rule_set(),
            &sess.encode(&mk_prov("( ps -> ph )")).unwrap(),
        )
        .unwrap();
        assert_eq!(a1i.concl(), &want);
    }

    /// **Compose statements the database has no `$p` for.** `apply("ax-1", …)`
    /// mints an ax-1 instance; `apply("ax-mp", …)` (via [`MmSession::mp`])
    /// composes an assumed major with a stored/derived implication.
    #[test]
    fn apply_axiom_and_mp_compose_non_theorem() {
        let db = parse(PROP);
        let sess = MmSession::new(db).unwrap();

        // ax-1 @ (ph := ( ph -> ph ), ps := ph): a hypothesis-free instance the
        // database never states as a `$p`.
        let php = sess.encode(&mk_wff("( ph -> ph )")).unwrap();
        let ph = sess.encode(&mk_wff("ph")).unwrap();
        let ax1 = sess.apply("ax-1", &[php.clone(), ph.clone()], &[]).unwrap();
        assert!(ax1.hyps().is_empty(), "ax-1 instance is hypothesis-free");
        let want = super::super::derivable(
            sess.rule_set(),
            &sess
                .encode(&mk_prov("( ( ph -> ph ) -> ( ph -> ( ph -> ph ) ) )"))
                .unwrap(),
        )
        .unwrap();
        assert_eq!(ax1.concl(), &want, "ax-1 instance conclusion");

        // Now compose by MP: from an assumed `Der ⌜A⌝` and a derived
        // `Der ⌜A ⟹ B⌝`, get `Der ⌜B⌝`. Use A := ( ph -> ph ), B := ( ph -> ( ph -> ph ) ).
        // Major (assumed): Der ⌜( ph -> ph )⌝.
        let a_enc = sess.encode(&mk_prov("( ph -> ph )")).unwrap();
        let major = Thm::assume(super::super::derivable(sess.rule_set(), &a_enc).unwrap()).unwrap();
        // Minor: the ax-1 instance IS `Der ⌜( ph -> ph ) ⟹ ( ph -> ( ph -> ph ) )⌝`.
        let minor = ax1;
        // ax-mp floats (frame order): ph := ( ph -> ph ), ps := ( ph -> ( ph -> ph ) ).
        let b_ph = sess.encode(&mk_wff("( ph -> ph )")).unwrap();
        let b_ps = sess.encode(&mk_wff("( ph -> ( ph -> ph ) )")).unwrap();
        let composed = sess
            .mp(None, &[b_ph, b_ps], &major, &minor)
            .expect("MP composes");
        // Conclusion: Der ⌜( ph -> ( ph -> ph ) )⌝, carrying the assumed major hyp.
        let want_b = super::super::derivable(
            sess.rule_set(),
            &sess.encode(&mk_prov("( ph -> ( ph -> ph ) )")).unwrap(),
        )
        .unwrap();
        assert_eq!(composed.concl(), &want_b, "MP composite conclusion");
        assert_eq!(
            composed.hyps().len(),
            1,
            "carries the assumed major premise"
        );
    }

    /// Arity errors: wrong float / premise counts are clear errors.
    #[test]
    fn apply_arity_errors() {
        let db = parse(PROP);
        let sess = MmSession::new(db).unwrap();
        let ph = sess.encode(&mk_wff("ph")).unwrap();
        // ax-1 takes 2 floats, 0 premises.
        assert!(
            sess.apply("ax-1", &[ph.clone()], &[]).is_err(),
            "too few floats"
        );
        let major = Thm::assume(
            super::super::derivable(sess.rule_set(), &sess.encode(&mk_prov("ph")).unwrap())
                .unwrap(),
        )
        .unwrap();
        assert!(
            sess.apply("ax-1", &[ph.clone(), ph.clone()], &[&major])
                .is_err(),
            "premise supplied to premise-free ax-1"
        );
        // Unknown rule.
        assert!(sess.apply("nope", &[], &[]).is_err(), "unknown rule label");
    }
}
