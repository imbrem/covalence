//! **A HOL-backed [`DatabaseSink`]** — construct `⊢ Derivable_Prop ⌜S⌝`
//! *while reading* a `.mm` source, rather than building an in-memory
//! [`Database`] and replaying it afterwards.
//!
//! `covalence-metamath`'s reader drives the high-level [`DatabaseSink`] builder
//! API; the *backend* decides what to build. The in-memory [`Database`] is the
//! HOL-free "sanity-check" backend; [`HolPropSink`] here is the **HOL backend**:
//! as each `$p` theorem is read, it replays the (verified-by-construction)
//! proof through the kernel ([`super::mm_replay::replay_prop`]) and accumulates
//! the constructed theorem `⊢ Derivable_Prop ⌜S⌝`.
//!
//! This is the "construct, don't trust" discipline at the *reader* level: the
//! Metamath proof is untrusted, every kernel step is re-checked, and the result
//! lands in *pure derivability over the encoded syntax* — no denotation, no
//! observer, no oracle (see [`super::mm_replay`]).
//!
//! ## Scope
//!
//! This first HOL backend handles the **propositional fragment** (set.mm's
//! `ax-1`/`ax-2`/`ax-mp` shape — whatever [`replay_prop`](super::mm_replay::replay_prop)
//! interprets). A backend over an *arbitrary* database (one substitution-instance
//! clause per assertion — the `RuleSet`-from-`Database` generalisation, landing
//! `⊢ Derivable_DB ⌜db⌝ ⌜S⌝`) is the follow-on north star; see
//! [`SKELETONS.md`](./SKELETONS.md).
//!
//! ## How the frame reaches the replay
//!
//! [`DatabaseSink::add_assertion`] is handed only `label`/`conclusion`/`proof`
//! (the mandatory frame is computed from the active scope). So `HolPropSink`
//! keeps an **inner [`Database`]**, forwards every builder call to it, and — for
//! a `$p` — reads the just-built [`Assertion`] (now carrying its frame) back out
//! and replays it. Because Metamath proofs only reference *earlier* statements
//! and the assertion is added with the scope still open, the inner database has
//! exactly what the replay needs at that point.

use covalence_core::Thm;

use crate::metamath::{
    Assertion, Database, DatabaseSink, Expr, MmError, Proof, Statement, SymbolKind,
};

use super::mm_replay::replay_prop;

/// A [`DatabaseSink`] that constructs `⊢ Derivable_Prop ⌜S⌝` for every `$p`
/// theorem as the `.mm` source is read. Forwards all structural building to an
/// inner [`Database`]; collects the replayed theorems.
pub struct HolPropSink {
    db: Database,
    theorems: Vec<(String, Thm)>,
}

impl HolPropSink {
    /// A fresh, empty HOL-backed sink.
    pub fn new() -> Self {
        HolPropSink {
            db: Database::new(),
            theorems: Vec::new(),
        }
    }

    /// The theorems constructed so far, in read order: `(label, ⊢ Derivable_Prop ⌜S⌝)`.
    pub fn theorems(&self) -> &[(String, Thm)] {
        &self.theorems
    }

    /// Look up the constructed theorem for a `$p` label.
    pub fn theorem(&self, label: &str) -> Option<&Thm> {
        self.theorems
            .iter()
            .find(|(l, _)| l == label)
            .map(|(_, t)| t)
    }

    /// Consume the sink, yielding the constructed theorems in read order.
    pub fn into_theorems(self) -> Vec<(String, Thm)> {
        self.theorems
    }
}

impl Default for HolPropSink {
    fn default() -> Self {
        Self::new()
    }
}

impl DatabaseSink for HolPropSink {
    fn declare(&mut self, kind: SymbolKind, names: &[&str]) -> Result<(), MmError> {
        <Database as DatabaseSink>::declare(&mut self.db, kind, names)
    }

    fn push_scope(&mut self) {
        <Database as DatabaseSink>::push_scope(&mut self.db)
    }

    fn pop_scope(&mut self) -> Result<(), MmError> {
        <Database as DatabaseSink>::pop_scope(&mut self.db)
    }

    fn add_float(&mut self, label: &str, typecode: &str, var: &str) -> Result<(), MmError> {
        <Database as DatabaseSink>::add_float(&mut self.db, label, typecode, var)
    }

    fn add_essential(&mut self, label: &str, expr: Expr) -> Result<(), MmError> {
        <Database as DatabaseSink>::add_essential(&mut self.db, label, expr)
    }

    fn add_disjoint(&mut self, vars: &[&str]) -> Result<(), MmError> {
        <Database as DatabaseSink>::add_disjoint(&mut self.db, vars)
    }

    fn add_assertion(
        &mut self,
        label: &str,
        conclusion: Expr,
        proof: Option<Proof>,
    ) -> Result<(), MmError> {
        let has_proof = proof.is_some();
        // Build the assertion into the inner database first (computes its frame).
        <Database as DatabaseSink>::add_assertion(&mut self.db, label, conclusion, proof)?;
        if has_proof {
            // Read the just-built assertion (with frame) back out and replay it.
            let assertion: Assertion = match self.db.statement_by_label(label) {
                Some(Statement::Assert(a)) => a.clone(),
                _ => return Ok(()), // not an assertion (cannot happen for a $p)
            };
            let thm = replay_prop(&self.db, &assertion).map_err(|e| MmError::Backend {
                label: label.to_string(),
                message: e.to_string(),
            })?;
            self.theorems.push((label.to_string(), thm));
        }
        Ok(())
    }
}

/// Read a propositional `.mm` source and **construct** `⊢ Derivable_Prop ⌜S⌝`
/// for each `$p` theorem, in read order. The Metamath proofs are untrusted; the
/// kernel re-checks every step (see the [module docs](self)).
pub fn read_prop(source: &str) -> Result<Vec<(String, Thm)>, MmError> {
    let mut sink = HolPropSink::new();
    crate::metamath::parse_into(source, &mut sink)?;
    Ok(sink.into_theorems())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::init::prop;
    use crate::metamath::expr::typecode_of;

    /// The propositional-calculus database (set.mm's ax-1/ax-2/ax-mp), plus two
    /// `$p` theorems: `ax2i` (a single ax-2 instance, hypothesis-free) and `a1i`
    /// (a derived rule carrying one essential). Mirrors
    /// `covalence-metamath/tests/theories.rs`.
    const PROP_WITH_THEOREMS: &str = "\
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
        ax2i $p |- ( ( ph -> ( ps -> ph ) ) -> ( ( ph -> ps ) -> ( ph -> ph ) ) ) $=
          wph wps wph ax-2 $.
        ${
          a1i.1 $e |- ph $.
          a1i $p |- ( ps -> ph ) $=
            wph wps wph wi a1i.1 wph wps ax-1 ax-mp $.
        $}
    ";

    /// **The headline: construct `⊢ Derivable_Prop ⌜S⌝` while reading a `.mm`.**
    /// Driving the HOL-backed sink over the source yields one constructed
    /// theorem per `$p`, every one genuine (kernel-checked) and oracle-free.
    #[test]
    fn read_prop_constructs_derivable_theorems() {
        let thms = read_prop(PROP_WITH_THEOREMS).expect("read + replay");
        assert_eq!(thms.len(), 2, "two $p theorems → two constructed theorems");

        // ax2i: hypothesis-free, oracle-free, conclusion exactly `Derivable_Prop ⌜ax-2
        // instance⌝`. Proof order `wph wps wph` → ph := 0, ps := 1, and ax-2's third
        // arg (ch) := ph = 0, so the instance is axiom-2 at (v0, v1, v0).
        let (l0, ax2i) = &thms[0];
        assert_eq!(l0, "ax2i");
        assert!(ax2i.hyps().is_empty(), "ax2i is hypothesis-free");
        assert!(ax2i.has_no_obs(), "ax2i is oracle-free");
        let v = |k| prop::p_var_lit(k);
        let imp = prop::p_imp;
        let ax2_inst = imp(
            imp(v(0), imp(v(1), v(0))),
            imp(imp(v(0), v(1)), imp(v(0), v(0))),
        );
        assert_eq!(
            ax2i.concl(),
            &prop::derivable(&ax2_inst).unwrap(),
            "ax2i conclusion is Derivable_Prop of the ax-2 instance"
        );

        // a1i: carries exactly one hypothesis (its essential `|- ph`), oracle-free.
        let (l1, a1i) = &thms[1];
        assert_eq!(l1, "a1i");
        assert!(a1i.has_no_obs(), "a1i is oracle-free");
        assert_eq!(
            a1i.hyps().len(),
            1,
            "a1i carries its one essential as a hypothesis"
        );
    }

    /// The constructed `ax2i` theorem is **exactly** what the direct replay
    /// produces — the sink path agrees with `replay_prop` byte-for-byte.
    #[test]
    fn sink_agrees_with_direct_replay() {
        // Build the database directly and replay ax2i.
        let db = crate::metamath::parse(PROP_WITH_THEOREMS).unwrap();
        assert_eq!(crate::metamath::verify_all(&db).unwrap(), 2);
        let assertion = db.assertions().find(|a| a.label == "ax2i").unwrap();
        let direct = replay_prop(&db, assertion).unwrap();

        // Read via the sink.
        let via_sink = read_prop(PROP_WITH_THEOREMS).unwrap();
        let sink_ax2i = &via_sink.iter().find(|(l, _)| l == "ax2i").unwrap().1;

        assert_eq!(
            direct.concl(),
            sink_ax2i.concl(),
            "sink and direct replay agree"
        );
    }

    /// Sanity: the conclusions really are over `prop`'s reified syntax (no
    /// denotation leaked in). `prop::derivable` of the parsed wff matches.
    #[test]
    fn conclusion_is_pure_derivability() {
        let thms = read_prop(PROP_WITH_THEOREMS).unwrap();
        let a1i = &thms.iter().find(|(l, _)| l == "a1i").unwrap().1;
        // a1i concludes `Derivable_Prop ⌜(ps -> ph)⌝`. With proof-order indices
        // ph := 0, ps := 1 (the proof opens `wph wps`), `(ps -> ph)` encodes as
        // `p_imp(p_var 1, p_var 0)`.
        let expected =
            prop::derivable(&prop::p_imp(prop::p_var_lit(1), prop::p_var_lit(0))).unwrap();
        assert_eq!(
            a1i.concl(),
            &expected,
            "a1i conclusion is pure Derivable_Prop"
        );
        // And it is not a `|-` denotation artifact — the conclusion is the
        // `Derivable_Prop` predicate applied to encoded syntax.
        let _ = typecode_of; // keep the import meaningful across refactors
    }
}
