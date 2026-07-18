//! Axiom sets and axiom-level **metatheory** over a Metamath [`Database`].
//!
//! A Metamath database mixes several *theories* in one file: `set.mm` contains
//! propositional calculus, predicate calculus, ZF, ZFC, Tarski–Grothendieck,
//! and the axiomatic reals, all as `$a` statements with the `|-` typecode.
//! This module makes those subsets first-class:
//!
//! * [`AxiomSet`] — a named, layered set of `$a` labels. The common sets are
//!   **vendored as constants** ([`sets`] for `set.mm`, [`iset`] for `iset.mm`,
//!   [`hol`] for the `hol.mm` HOL encoding) against the pinned database
//!   revision used by `bun run bench:setmm` (`scripts/_setmm.mjs`).
//! * [`axiom_closure`] — the set of `$a` statements a theorem's proof
//!   transitively rests on (Metamath's "this theorem was proved from axioms"
//!   list). This is what lets us *reason about* axiom usage.
//! * [`check_implication`] — a checked certificate that axiom set `A` implies
//!   axiom set `B` over a database: every axiom of `B` has a witness theorem
//!   with the **same statement** whose proof uses only `A`-axioms (plus
//!   explicitly admitted `$a`s — definitions, typically).
//!
//! ## The transport metatheorem (why an [`Implication`] is useful)
//!
//! Metamath derivations are closed under replacing an axiom step by a proof of
//! the same statement: if `A ⇒ B` (every `B`-axiom has an `A`-proof) and a
//! statement `S` has a derivation from `B`, then splicing the witness proofs
//! in place of the `B`-axiom steps yields a derivation of `S` from `A` — no
//! replay required, and the spliced derivation is never materialised. Under
//! the "a theorem *means* ∃ a Metamath derivation" reading, an [`Implication`]
//! therefore transports every `B`-theorem to an `A`-theorem in O(1). The
//! splice is statement-local (substitution instances of an assertion only
//! depend on its statement, and the witness's `$d` obligations are required to
//! be no stronger than the axiom's), which is exactly what
//! [`same_statement`] checks.
//!
//! ## Definitions
//!
//! `set.mm` definitions (`df-*`) are also `|-`-typecode `$a`s. An implication
//! check lists every non-`A` axiom a witness rests on and only admits the ones
//! the caller's `allow` predicate accepts (conventionally
//! [`allow_definitions`]). So the checked reals result is precisely: *every
//! reals axiom is provable in ZFC **plus definitions*** — the definitional
//! extension itself being conservative is a separate (deferred) metatheorem;
//! see the generated open-work index.

use std::collections::{BTreeMap, BTreeSet, HashSet};

use crate::database::{Assertion, Database, Proof, Statement};
use crate::error::MmError;

/// The provability typecode shared by `set.mm` / `iset.mm` / `hol.mm`.
pub const PROVABLE_TC: &str = "|-";

/// A named set of axiom labels (`$a` statements with the [`PROVABLE_TC`]
/// typecode), layered so extensions share their base (`ZFC` extends `ZF`
/// extends predicate calculus, …).
///
/// The set is defined by **labels**, not statements: it names axioms *of a
/// particular database* (the pinned `set.mm` / `iset.mm` revision). All checks
/// resolve the labels against the database at hand and fail loudly if one is
/// missing, so a database drift cannot silently weaken a result.
#[derive(Debug, Clone, Copy)]
pub struct AxiomSet {
    /// Human-readable name (`"ZFC"`, `"IZF"`, …).
    pub name: &'static str,
    /// Sets this one extends; the full label set is the union.
    pub extends: &'static [&'static AxiomSet],
    /// Labels this layer adds.
    pub delta: &'static [&'static str],
}

impl AxiomSet {
    /// The full label set (this layer plus everything it extends).
    pub fn labels(&self) -> BTreeSet<&'static str> {
        let mut out = BTreeSet::new();
        self.collect(&mut out);
        out
    }

    fn collect(&self, out: &mut BTreeSet<&'static str>) {
        for base in self.extends {
            base.collect(out);
        }
        out.extend(self.delta.iter().copied());
    }

    /// Whether `label` is in the set.
    pub fn contains(&self, label: &str) -> bool {
        self.delta.contains(&label) || self.extends.iter().any(|b| b.contains(label))
    }

    /// Resolve every label against `db`, checking each is a `$a` axiom with
    /// the [`PROVABLE_TC`] typecode. This is the "the vendored constant still
    /// matches the pinned database" sanity check.
    pub fn resolve<'db>(&self, db: &'db Database) -> Result<Vec<&'db Assertion>, MetaError> {
        self.labels()
            .into_iter()
            .map(|l| {
                let a = axiom_by_label(db, l)?;
                if a.conclusion.typecode() != PROVABLE_TC {
                    return Err(MetaError::NotAnAxiom {
                        label: l.to_string(),
                        reason: format!(
                            "typecode `{}` is not `{PROVABLE_TC}`",
                            a.conclusion.typecode()
                        ),
                    });
                }
                Ok(a)
            })
            .collect()
    }
}

/// Errors from axiom-level metatheory checks.
#[derive(Debug, thiserror::Error)]
pub enum MetaError {
    #[error("label `{0}` not found in database")]
    MissingLabel(String),
    #[error("`{label}` is not a `$a` axiom: {reason}")]
    NotAnAxiom { label: String, reason: String },
    #[error("axiom `{axiom}` has no witness theorem (tried `{tried}`)")]
    NoWitness { axiom: String, tried: String },
    #[error("witness `{witness}` does not state axiom `{axiom}`: {reason}")]
    StatementMismatch {
        axiom: String,
        witness: String,
        reason: String,
    },
    #[error(
        "witness `{witness}` for `{axiom}` rests on `{used}`, which is neither in `{stronger}` nor admitted"
    )]
    ForbiddenAxiom {
        axiom: String,
        witness: String,
        used: String,
        stronger: String,
    },
    #[error("`{label}` rests on `{used}`, which is neither in `{set}` nor admitted")]
    NotDerivableFrom {
        label: String,
        used: String,
        set: String,
    },
    #[error(transparent)]
    Mm(#[from] MmError),
}

fn assertion_by_label<'db>(db: &'db Database, label: &str) -> Result<&'db Assertion, MetaError> {
    match db.statement_by_label(label) {
        Some(Statement::Assert(a)) => Ok(a),
        Some(_) => Err(MetaError::NotAnAxiom {
            label: label.to_string(),
            reason: "label names a hypothesis, not an assertion".into(),
        }),
        None => Err(MetaError::MissingLabel(label.to_string())),
    }
}

fn axiom_by_label<'db>(db: &'db Database, label: &str) -> Result<&'db Assertion, MetaError> {
    let a = assertion_by_label(db, label)?;
    if a.proof.is_some() {
        return Err(MetaError::NotAnAxiom {
            label: label.to_string(),
            reason: "label names a `$p` theorem".into(),
        });
    }
    Ok(a)
}

/// The labels an assertion's proof cites. For a compressed proof this is the
/// label block — the letter body only addresses mandatory hypotheses (never
/// assertions), label-block entries, and heap saves, so the block is a sound
/// over-approximation of the assertions used (and exact in practice).
fn cited_labels(a: &Assertion) -> &[String] {
    match &a.proof {
        None => &[],
        Some(Proof::Normal(labels)) => labels,
        Some(Proof::Compressed { labels, .. }) => labels,
    }
}

/// The set of `$a` axiom labels (any typecode: logical axioms, definitions,
/// and syntax formers) that `label`'s proof transitively rests on.
///
/// An axiom rests on itself. Hypothesis references contribute nothing. The
/// walk is a worklist over cited labels, so cost is linear in the reachable
/// sub-database — cheap enough to call per theorem even on `set.mm`.
pub fn axiom_closure(db: &Database, label: &str) -> Result<BTreeSet<String>, MetaError> {
    let mut axioms = BTreeSet::new();
    let mut seen: HashSet<&str> = HashSet::new();
    let mut stack: Vec<&str> = vec![label];
    seen.insert(label);
    while let Some(l) = stack.pop() {
        match db.statement_by_label(l) {
            Some(Statement::Assert(a)) => {
                if a.proof.is_none() {
                    axioms.insert(a.label.clone());
                } else {
                    for cited in cited_labels(a) {
                        if seen.insert(cited) {
                            stack.push(cited);
                        }
                    }
                }
            }
            // $f/$e hypothesis references are not axioms.
            Some(_) => {}
            None => return Err(MetaError::MissingLabel(l.to_string())),
        }
    }
    Ok(axioms)
}

/// The subset of an [`axiom_closure`] with the [`PROVABLE_TC`] typecode — the
/// *logical* axioms (and definitions) used, excluding syntax formers.
pub fn provable_closure(db: &Database, label: &str) -> Result<BTreeSet<String>, MetaError> {
    let mut closure = axiom_closure(db, label)?;
    closure.retain(|l| {
        matches!(db.statement_by_label(l), Some(Statement::Assert(a))
            if a.conclusion.typecode() == PROVABLE_TC)
    });
    Ok(closure)
}

/// Check that `label` is derivable from `axioms` (plus `allow`-admitted `$a`s,
/// conventionally definitions). On success returns the admitted extras its
/// proof actually rests on.
pub fn derivable_from(
    db: &Database,
    label: &str,
    axioms: &AxiomSet,
    allow: &dyn Fn(&Database, &str) -> bool,
) -> Result<BTreeSet<String>, MetaError> {
    let mut admitted = BTreeSet::new();
    for used in provable_closure(db, label)? {
        if axioms.contains(&used) {
            continue;
        }
        if allow(db, &used) {
            admitted.insert(used);
        } else {
            return Err(MetaError::NotDerivableFrom {
                label: label.to_string(),
                used,
                set: axioms.name.to_string(),
            });
        }
    }
    Ok(admitted)
}

/// Do `a` and `b` assert the **same statement**, with `b`'s distinct-variable
/// requirements no stronger than `a`'s?
///
/// Same statement = identical conclusion [`crate::Expr`], identical essential
/// hypotheses (in order), identical mandatory float typing (the same
/// `{variable ↦ typecode}` map — `$f`s are usually global, but a scoped `$f`
/// could type the same variable name differently at the two statements, so
/// this is checked rather than assumed), and `b.frame.disjoints ⊆
/// a.frame.disjoints` as unordered pairs. Requiring `⊆` (not `=`) on `$d` is
/// deliberate: a witness that needs *fewer* distinctness side conditions
/// proves a stronger schema, which is still a valid substitute at every use
/// site of the axiom.
pub fn same_statement(a: &Assertion, b: &Assertion) -> Result<(), String> {
    fn float_map(asrt: &Assertion) -> BTreeMap<&str, &str> {
        asrt.frame
            .floats
            .iter()
            .map(|f| (f.var.as_str(), f.typecode.as_str()))
            .collect()
    }
    if float_map(a) != float_map(b) {
        return Err("mandatory variables are typed differently".into());
    }
    if a.conclusion != b.conclusion {
        return Err(format!(
            "conclusion `{}` ≠ `{}`",
            b.conclusion.render(),
            a.conclusion.render()
        ));
    }
    if a.frame.essentials.len() != b.frame.essentials.len() {
        return Err(format!(
            "{} essential hypotheses ≠ {}",
            b.frame.essentials.len(),
            a.frame.essentials.len()
        ));
    }
    for (ha, hb) in a.frame.essentials.iter().zip(&b.frame.essentials) {
        if ha.expr != hb.expr {
            return Err(format!(
                "essential `{}` ≠ `{}`",
                hb.expr.render(),
                ha.expr.render()
            ));
        }
    }
    let pairs = |asrt: &Assertion| -> BTreeSet<(String, String)> {
        asrt.frame
            .disjoints
            .iter()
            .map(|(x, y)| {
                if x <= y {
                    (x.clone(), y.clone())
                } else {
                    (y.clone(), x.clone())
                }
            })
            .collect()
    };
    let (da, db_) = (pairs(a), pairs(b));
    if let Some((x, y)) = db_.difference(&da).next() {
        return Err(format!(
            "witness requires `$d {x} {y}` which the axiom does not grant"
        ));
    }
    Ok(())
}

/// One checked entailment: the axiom (of the weaker set) and the theorem that
/// proves it from the stronger set. `theorem == None` when the axiom is
/// already a member of the stronger set.
#[derive(Debug, Clone)]
pub struct AxiomWitness {
    pub axiom: String,
    pub theorem: Option<String>,
    /// Non-stronger `|-` axioms the witness rests on that `allow` admitted
    /// (definitions, typically).
    pub admitted: BTreeSet<String>,
}

/// A checked certificate that `stronger ⇒ weaker` over a database: every
/// axiom of `weaker` is either in `stronger` or has a same-statement witness
/// theorem proved from `stronger` (plus admitted `$a`s). See the module docs
/// for the transport metatheorem this certifies.
#[derive(Debug, Clone)]
pub struct Implication {
    pub stronger: &'static str,
    pub weaker: &'static str,
    pub witnesses: Vec<AxiomWitness>,
}

impl Implication {
    /// Every admitted (non-`stronger`) `$a` any witness rests on — for the
    /// reals-over-ZFC check, the definitions the constructions go through.
    pub fn admitted(&self) -> BTreeSet<&str> {
        self.witnesses
            .iter()
            .flat_map(|w| w.admitted.iter().map(String::as_str))
            .collect()
    }
}

/// `set.mm`'s naming convention for restated axioms: axiom `ax-foo` is proved
/// as theorem `axfoo` (e.g. `ax-cnex`/`axcnex`, `ax-pre-sup`/`axpre-sup`).
pub fn setmm_witness(axiom: &str) -> Option<String> {
    axiom.strip_prefix("ax-").map(|rest| format!("ax{rest}"))
}

/// Admit definitional `$a`s under `set.mm`'s `df-*` naming convention.
pub fn allow_definitions(_db: &Database, label: &str) -> bool {
    label.starts_with("df-")
}

/// Check that `stronger ⇒ weaker` over `db`; see [`Implication`].
///
/// * `witness` maps an axiom label of `weaker` to its candidate witness
///   theorem label (conventionally [`setmm_witness`]).
/// * `allow` admits `|-` `$a`s beyond `stronger` that witnesses may rest on
///   (conventionally [`allow_definitions`]); everything else is an error.
pub fn check_implication(
    db: &Database,
    stronger: &AxiomSet,
    weaker: &AxiomSet,
    witness: &dyn Fn(&str) -> Option<String>,
    allow: &dyn Fn(&Database, &str) -> bool,
) -> Result<Implication, MetaError> {
    // Fail early if either constant has drifted from the database.
    stronger.resolve(db)?;
    let weaker_axioms = weaker.resolve(db)?;

    let mut witnesses = Vec::new();
    for ax in weaker_axioms {
        if stronger.contains(&ax.label) {
            witnesses.push(AxiomWitness {
                axiom: ax.label.clone(),
                theorem: None,
                admitted: BTreeSet::new(),
            });
            continue;
        }
        let w_label = witness(&ax.label).ok_or_else(|| MetaError::NoWitness {
            axiom: ax.label.clone(),
            tried: "<none>".into(),
        })?;
        let w = assertion_by_label(db, &w_label).map_err(|_| MetaError::NoWitness {
            axiom: ax.label.clone(),
            tried: w_label.clone(),
        })?;
        if w.proof.is_none() {
            return Err(MetaError::StatementMismatch {
                axiom: ax.label.clone(),
                witness: w_label,
                reason: "witness is itself an axiom (`$a`), not a theorem".into(),
            });
        }
        same_statement(ax, w).map_err(|reason| MetaError::StatementMismatch {
            axiom: ax.label.clone(),
            witness: w_label.clone(),
            reason,
        })?;
        let mut admitted = BTreeSet::new();
        for used in provable_closure(db, &w_label)? {
            if stronger.contains(&used) {
                continue;
            }
            if allow(db, &used) {
                admitted.insert(used);
            } else {
                return Err(MetaError::ForbiddenAxiom {
                    axiom: ax.label.clone(),
                    witness: w_label.clone(),
                    used,
                    stronger: stronger.name.to_string(),
                });
            }
        }
        witnesses.push(AxiomWitness {
            axiom: ax.label.clone(),
            theorem: Some(w_label),
            admitted,
        });
    }
    Ok(Implication {
        stronger: stronger.name,
        weaker: weaker.name,
        witnesses,
    })
}

/// Group every `|-` axiom of the database by whether each vendored set
/// contains it — a quick "what does this database postulate" report.
pub fn classify_axioms<'db>(
    db: &'db Database,
    sets: &[&AxiomSet],
) -> BTreeMap<&'db str, Vec<&'static str>> {
    let mut out: BTreeMap<&str, Vec<&'static str>> = BTreeMap::new();
    for a in db.assertions() {
        if a.proof.is_none() && a.conclusion.typecode() == PROVABLE_TC {
            let members = sets
                .iter()
                .filter(|s| s.contains(&a.label))
                .map(|s| s.name)
                .collect();
            out.insert(&a.label, members);
        }
    }
    out
}

// ---------------------------------------------------------------------------
// Vendored axiom-set constants
// ---------------------------------------------------------------------------

/// Axiom sets of **`set.mm`** (pinned via `scripts/_setmm.mjs`; resolve
/// against the database to detect drift).
///
/// `set.mm` deliberately postulates some *redundant* axioms (`ax-sep`,
/// `ax-nul`, `ax-pr` follow from replacement &c.) so usage tracking stays
/// honest; [`ZF_KERNEL`](sets::ZF_KERNEL) is the non-redundant core, and
/// `ZF_KERNEL ⇒ ZF` is itself a checkable [`Implication`].
pub mod sets {
    use super::AxiomSet;

    /// Classical propositional calculus: Łukasiewicz's three axioms + modus
    /// ponens.
    pub static PROP: AxiomSet = AxiomSet {
        name: "PROP",
        extends: &[],
        delta: &["ax-mp", "ax-1", "ax-2", "ax-3"],
    };

    /// Classical first-order predicate calculus with equality (Tarski's S2
    /// plus auxiliary schemes), over [`PROP`].
    pub static PRED: AxiomSet = AxiomSet {
        name: "PRED",
        extends: &[&PROP],
        delta: &[
            "ax-gen", "ax-4", "ax-5", "ax-6", "ax-7", "ax-8", "ax-9", "ax-10", "ax-11", "ax-12",
            "ax-13",
        ],
    };

    /// The non-redundant ZF core as postulated by `set.mm`: extensionality,
    /// replacement, power set, union, regularity, infinity.
    pub static ZF_KERNEL: AxiomSet = AxiomSet {
        name: "ZF_KERNEL",
        extends: &[&PRED],
        delta: &["ax-ext", "ax-rep", "ax-pow", "ax-un", "ax-reg", "ax-inf"],
    };

    /// Full ZF as `set.mm` states it, including the redundant-but-tracked
    /// separation, null set, pairing, and the `ax-inf2` form of infinity.
    pub static ZF: AxiomSet = AxiomSet {
        name: "ZF",
        extends: &[&ZF_KERNEL],
        delta: &["ax-sep", "ax-nul", "ax-pr", "ax-inf2"],
    };

    /// ZFC: ZF plus choice (`set.mm` postulates the `ax-ac2` form; `ax-ac` is
    /// the classic form, redundant given `ax-ac2`).
    pub static ZFC: AxiomSet = AxiomSet {
        name: "ZFC",
        extends: &[&ZF],
        delta: &["ax-ac2", "ax-ac"],
    };

    /// Tarski–Grothendieck: ZFC plus Grothendieck universes (`ax-groth`).
    pub static TARSKI_GROTHENDIECK: AxiomSet = AxiomSet {
        name: "TARSKI_GROTHENDIECK",
        extends: &[&ZFC],
        delta: &["ax-groth"],
    };

    /// The axiomatic complex/real numbers: `set.mm`'s 27 `ax-*cn*`/`ax-pre-*`
    /// postulates over ZFC. Every one is *provable* from the ZFC construction
    /// (witnesses `axcnex`, …, `axpre-sup`) — the implication
    /// `ZFC ⇒ REALS` is the vendored conservativity-over-ZFC(-with-
    /// definitions) check.
    pub static REALS: AxiomSet = AxiomSet {
        name: "REALS",
        extends: &[&ZFC],
        delta: &[
            "ax-cnex",
            "ax-resscn",
            "ax-1cn",
            "ax-icn",
            "ax-addcl",
            "ax-addrcl",
            "ax-mulcl",
            "ax-mulrcl",
            "ax-mulcom",
            "ax-addass",
            "ax-mulass",
            "ax-distr",
            "ax-i2m1",
            "ax-1ne0",
            "ax-1rid",
            "ax-rnegex",
            "ax-rrecex",
            "ax-cnre",
            "ax-pre-lttri",
            "ax-pre-lttrn",
            "ax-pre-ltadd",
            "ax-pre-mulgt0",
            "ax-pre-sup",
            "ax-addf",
            "ax-mulf",
        ],
    };
}

/// Axiom sets of **`iset.mm`** (intuitionistic logic + IZF; same pinned
/// revision). Note the *logic itself* differs from `set.mm`'s: intuitionistic
/// propositional calculus splits conjunction/negation into separate axioms
/// and omits `ax-3` (excluded middle's engine).
pub mod iset {
    use super::AxiomSet;

    /// Intuitionistic propositional calculus as `iset.mm` postulates it.
    pub static PROP: AxiomSet = AxiomSet {
        name: "iPROP",
        extends: &[],
        delta: &[
            "ax-mp", "ax-1", "ax-2", "ax-ia1", "ax-ia2", "ax-ia3", "ax-in1", "ax-in2", "ax-io",
        ],
    };

    /// Intuitionistic predicate calculus over [`PROP`].
    pub static PRED: AxiomSet = AxiomSet {
        name: "iPRED",
        extends: &[&PROP],
        delta: &[
            "ax-5", "ax-7", "ax-gen", "ax-ie1", "ax-ie2", "ax-8", "ax-10", "ax-11", "ax-i12",
            "ax-bndl", "ax-4", "ax-17", "ax-i9", "ax-ial", "ax-i5r", "ax-13", "ax-14",
        ],
    };

    /// IZF: intuitionistic ZF as `iset.mm` postulates it (collection instead
    /// of replacement, set induction instead of regularity, `ax-iinf`).
    pub static IZF: AxiomSet = AxiomSet {
        name: "IZF",
        extends: &[&PRED],
        delta: &[
            "ax-ext",
            "ax-coll",
            "ax-sep",
            "ax-nul",
            "ax-pow",
            "ax-pr",
            "ax-un",
            "ax-setind",
            "ax-iinf",
        ],
    };
}

/// Axiom sets of the vendored **`hol.mm`** fixture (Mario Carneiro's HOL
/// encoding; `crates/proof/metamath/tests/fixtures/hol.mm`) — the `|-` `$a`
/// postulates, definitions excluded (admit them via [`allow_definitions`]).
pub mod hol {
    use super::AxiomSet;

    /// The HOL deductive core: sequent plumbing, equality/beta/eta, the
    /// typedef axioms, choice, and infinity.
    pub static HOL: AxiomSet = AxiomSet {
        name: "HOL",
        extends: &[],
        delta: &[
            "ax-syl",
            "ax-jca",
            "ax-simpl",
            "ax-simpr",
            "ax-id",
            "ax-trud",
            "ax-cb1",
            "ax-cb2",
            "ax-wctl",
            "ax-wctr",
            "ax-weq",
            "ax-refl",
            "ax-eqmp",
            "ax-ded",
            "ax-wct",
            "ax-wc",
            "ax-ceq",
            "ax-wv",
            "ax-wl",
            "ax-beta",
            "ax-distrc",
            "ax-leq",
            "ax-distrl",
            "ax-wov",
            "ax-eqtypi",
            "ax-eqtypri",
            "ax-hbl1",
            "ax-17",
            "ax-inst",
            "ax-wabs",
            "ax-wrep",
            "ax-tdef",
            "ax-eta",
            "ax-wat",
            "ax-ac",
            "ax-inf",
        ],
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::parse;

    /// A miniature two-theory database: `BASE = {axA, axAB, mp}` proves (as
    /// `tht1`) the axiom `ax-t1` of `EXT = BASE + ax-t1`.
    const TWO_THEORIES: &str = "\
        $c wff |- T0 T1 ( ) -> $.\n\
        $v P Q $.\n\
        wp $f wff P $.\n\
        wq $f wff Q $.\n\
        t0 $a wff T0 $.\n\
        t1 $a wff T1 $.\n\
        wi $a wff ( P -> Q ) $.\n\
        axA $a |- T0 $.\n\
        axAB $a |- ( T0 -> T1 ) $.\n\
        ${  mpp $e |- P $.  mpi $e |- ( P -> Q ) $.\n\
            mp $a |- Q $.\n\
        $}\n\
        tht0 $p |- T0 $= axA $.\n\
        tht1 $p |- T1 $= t0 t1 axA axAB mp $.\n\
        ax-t1 $a |- T1 $.\n\
        down $p |- T1 $= ax-t1 $.\n\
    ";

    static BASE: AxiomSet = AxiomSet {
        name: "BASE",
        extends: &[],
        delta: &["axA", "axAB", "mp"],
    };
    static EXT: AxiomSet = AxiomSet {
        name: "EXT",
        extends: &[&BASE],
        delta: &["ax-t1"],
    };

    #[test]
    fn closure_and_derivable_from() {
        let db = parse(TWO_THEORIES).unwrap();
        #[cfg(feature = "checker")]
        assert_eq!(crate::verify_all(&db).unwrap(), 3);
        let cl = provable_closure(&db, "tht1").unwrap();
        assert_eq!(
            cl.iter().map(String::as_str).collect::<Vec<_>>(),
            ["axA", "axAB", "mp"]
        );
        // Syntax formers appear in the full closure but not the provable one.
        let full = axiom_closure(&db, "tht1").unwrap();
        assert!(full.contains("t0") && full.contains("t1"));
        assert!(derivable_from(&db, "tht1", &BASE, &|_, _| false).is_ok());
        // `down` uses ax-t1, underivable from BASE alone…
        assert!(matches!(
            derivable_from(&db, "down", &BASE, &|_, _| false),
            Err(MetaError::NotDerivableFrom { used, .. }) if used == "ax-t1"
        ));
        // …but fine from EXT.
        assert!(derivable_from(&db, "down", &EXT, &|_, _| false).is_ok());
    }

    #[test]
    fn implication_base_implies_ext() {
        let db = parse(TWO_THEORIES).unwrap();
        let imp = check_implication(
            &db,
            &BASE,
            &EXT,
            &|ax| (ax == "ax-t1").then(|| "tht1".to_string()),
            &|_, _| false,
        )
        .unwrap();
        assert_eq!(imp.witnesses.len(), 4); // 3 trivial members + 1 witnessed
        let w = imp.witnesses.iter().find(|w| w.axiom == "ax-t1").unwrap();
        assert_eq!(w.theorem.as_deref(), Some("tht1"));
        assert!(imp.admitted().is_empty());
    }

    #[test]
    fn implication_rejects_wrong_witness() {
        let db = parse(TWO_THEORIES).unwrap();
        // `down` HAS the right statement but rests on ax-t1 itself — forbidden.
        let err = check_implication(
            &db,
            &BASE,
            &EXT,
            &|ax| (ax == "ax-t1").then(|| "down".to_string()),
            &|_, _| false,
        )
        .unwrap_err();
        assert!(matches!(err, MetaError::ForbiddenAxiom { used, .. } if used == "ax-t1"));
        // `tht0` states `|- T0`, not `|- T1` — statement mismatch.
        let err = check_implication(
            &db,
            &BASE,
            &EXT,
            &|ax| (ax == "ax-t1").then(|| "tht0".to_string()),
            &|_, _| false,
        )
        .unwrap_err();
        assert!(matches!(err, MetaError::StatementMismatch { .. }));
    }

    #[test]
    fn axiom_set_layering() {
        let zfc = sets::ZFC.labels();
        assert!(zfc.contains("ax-mp") && zfc.contains("ax-ext") && zfc.contains("ax-ac2"));
        assert!(!zfc.contains("ax-groth"));
        assert!(sets::TARSKI_GROTHENDIECK.contains("ax-groth"));
        assert!(sets::REALS.contains("ax-pre-sup") && sets::REALS.contains("ax-mp"));
    }

    #[test]
    fn hol_fixture_axioms_resolve() {
        let src = include_str!("../tests/fixtures/hol.mm");
        let db = parse(src).unwrap();
        // Every vendored HOL label resolves to a `|-` $a in the fixture.
        assert_eq!(
            hol::HOL.resolve(&db).unwrap().len(),
            hol::HOL.labels().len()
        );
    }
}
