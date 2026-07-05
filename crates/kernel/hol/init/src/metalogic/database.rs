//! Databases as HOL predicates, database-parameterized derivability, the
//! extension relation `⊑`, and the monotonicity theorem.
//!
//! See the [module docs](super) for the design. Everything here works at the
//! reified propositional carrier `Φ⟨bool⟩` from [`crate::init::prop`]: a
//! formula is genuine HOL data, a **database is a HOL term** `db : Φ⟨bool⟩ →
//! bool`, and derivability / the relations are ordinary HOL predicates over
//! that term — so the kernel re-checks every step and the relation theorems are
//! honest HOL theorems.

use covalence_core::{Result, Term, Thm, Type};
use covalence_hol_eval::mk_nat;

use crate::init::ext::TermExt;
use crate::init::prop::{p_imp_at, p_var_at};

// ============================================================================
// Carrier plumbing — everything at `Φ⟨bool⟩`.
// ============================================================================

fn bool_ty() -> Type {
    Type::bool()
}

/// `Φ⟨bool⟩` — the reified-formula carrier, rebuilt at `'r := bool` so the
/// database predicate `Φ⟨bool⟩ → bool` and the formulas it ranges over share
/// one concrete type. (We reuse [`crate::init::prop`]'s encoding by building
/// formulas at `bool` via its `*_at` constructors.)
pub(crate) fn phi() -> Type {
    // `enc(var 0) : Φ⟨bool⟩` has exactly the carrier type we want; read it off.
    p_var_at(
        &bool_ty(),
        mk_nat(covalence_types::Nat::from_inner(0u32.into())),
    )
    .type_of()
    .expect("enc(var 0) is well-typed")
}

/// The type `Database = Φ⟨bool⟩ → bool` — the type of a reified database value.
pub fn database_ty() -> Type {
    Type::fun(phi(), bool_ty())
}

/// `Φ⟨bool⟩ → bool` — the type of the impredicative predicate variable `d`
/// (same as a database; a database *is* a set of formulas and `d` is the
/// candidate "derivable" set).
pub(crate) fn pred_ty() -> Type {
    Type::fun(phi(), bool_ty())
}

/// The database variable `db : Φ⟨bool⟩ → bool`.
fn db_var() -> Term {
    Term::free("db", database_ty())
}

/// The impredicative predicate variable `d : Φ⟨bool⟩ → bool`.
pub(crate) fn d_var() -> Term {
    Term::free("d", pred_ty())
}

/// `p A` — apply a predicate `p : Φ → bool` to an encoded formula `A`.
pub(crate) fn app(p: &Term, a: &Term) -> Result<Term> {
    p.clone().apply(a.clone())
}

/// An encoded-formula free variable `name : Φ⟨bool⟩`.
pub(crate) fn fvar(name: &str) -> Term {
    Term::free(name, phi())
}

/// `enc(A ⟹ B) : Φ⟨bool⟩`.
pub(crate) fn enc_imp(a: &Term, b: &Term) -> Term {
    p_imp_at(&bool_ty(), a.clone(), b.clone())
}

// ============================================================================
// `Closed_DB db d` — the closure conditions, parameterized by the database.
//
//   Closed_DB db d :=
//       (∀A B. d A ∧ d ⌜A ⟹ B⌝ ⟹ d B)     -- modus ponens (structural, shared)
//     ∧ (∀ax. db ax ⟹ d ax)                 -- db's axioms: every axiom is in d
//
// The first conjunct is the fixed inference-rule frame every database shares;
// the second reads the axioms OFF the database value `db`. This is the only
// place the database enters — which is what makes derivability a function of
// the HOL database value, and the relations statable.
// ============================================================================

/// The closure clauses of a database `db`, built against an arbitrary
/// `d ⌜·⌝` applier `d_apply` (so the *same* layout serves the bound predicate
/// variable `d`, used to state `Closed_DB`/`Derivable_DB`, and `d := pred`,
/// used to discharge it in rule induction). Returns the two clauses in fold
/// order: `[modus-ponens, axioms]`.
///
/// This is the [`super::RuleSet`] clause builder for a database value — the
/// bridge that makes `Derivable_DB` a genuine **instance of the generic engine**
/// ([`db_rule_set`]) rather than a parallel re-implementation.
pub(crate) fn db_clauses(db: &Term, d_apply: &dyn Fn(&Term) -> Result<Term>) -> Result<Vec<Term>> {
    let a = fvar("A");
    let b = fvar("B");

    // Clause 1 — modus ponens: ∀A B. d A ∧ d ⌜A ⟹ B⌝ ⟹ d B.
    let mp = {
        let da = d_apply(&a)?;
        let dab = d_apply(&enc_imp(&a, &b))?;
        let db_concl = d_apply(&b)?;
        da.and(dab)?
            .imp(db_concl)?
            .forall("A", phi())?
            .forall("B", phi())?
    };

    // Clause 2 — axioms: ∀ax. db ax ⟹ d ax.
    let ax_clause = {
        let ax = fvar("ax");
        app(db, &ax)?.imp(d_apply(&ax)?)?.forall("ax", phi())?
    };

    Ok(vec![mp, ax_clause])
}

/// **The database as a [`super::RuleSet`].** A database value `db` is exactly a
/// rule set over the carrier `Φ⟨bool⟩`: the fixed structural modus-ponens frame
/// plus the axiom clause reading `db`. Driving the generic engine off this is
/// the unification of the two former `Derivable` notions — `Derivable_DB` is now
/// `metalogic::derivable(&db_rule_set(db), ·)` (see [`derivable_db`]).
pub fn db_rule_set(db: Term) -> super::RuleSet<'static> {
    super::RuleSet::new(phi(), move |d_apply| db_clauses(&db, d_apply))
}

/// `Closed_DB db d` for the given database and predicate terms, as a single
/// `bool` term (a two-clause conjunction). Built generically so the same code
/// serves the definition and the proofs. Equals `super::closed_conj` over
/// [`db_rule_set`]'s clauses by construction.
pub(crate) fn closed(db: &Term, d: &Term) -> Result<Term> {
    super::conj(db_clauses(db, &|f| app(d, f))?)
}

// ============================================================================
// `Derivable_DB db A := ∀d. Closed_DB db d ⟹ d A`
// ============================================================================

/// `Derivable_DB db A := ∀d. Closed_DB db d ⟹ d A` — derivability of encoded
/// formula `A` from database `db`, as a HOL `bool` term over the supplied
/// `db`/`A`. This is now literally an **instance of the generic engine**:
/// `metalogic::derivable(&db_rule_set(db), A)`, the axiom set read off the **HOL
/// database value** `db`. (The standalone [`crate::init::prop`] /
/// [`crate::peano::pa`] derivabilities are the same shape over a Rust `RuleSet`
/// closure; this one's rule set *is* the database value — the unification.)
pub fn derivable_db(db: &Term, a: &Term) -> Result<Term> {
    super::derivable(&db_rule_set(db.clone()), a)
}

/// `Derivable_DB db A` over the free variables `db : Database`, `A : Φ⟨bool⟩` —
/// the most general statement (specialise `db`/`A` with
/// [`Thm::inst`](covalence_core::Thm) or [`subst`](covalence_core::subst)).
pub fn derivable() -> Result<Term> {
    derivable_db(&db_var(), &fvar("A"))
}

/// **Axioms are derivable.** Given `⊢ db A` (that `A` is an axiom of `db`),
/// produce `⊢ Derivable_DB db A`. Opens `∀d. Closed_DB db d ⟹ d A`, assumes
/// `Closed_DB db d`, pulls its axiom clause `∀ax. db ax ⟹ d ax`, specialises at
/// `A`, and feeds it the membership proof. `db_a` must be a hypothesis-free
/// `⊢ db A`. A genuine HOL theorem (no postulates).
pub fn derive_axiom_from_membership(db_a: Thm) -> Result<Thm> {
    // Read `db` and `A` off the membership conclusion `db A`.
    let (db, a) = db_a
        .concl()
        .as_app()
        .map(|(f, x)| (f.clone(), x.clone()))
        .ok_or_else(|| {
            covalence_core::Error::ConnectiveRule(
                "derive_axiom_from_membership: conclusion is not `db A`".into(),
            )
        })?;
    let closed_d = closed(&db, &d_var())?;
    let assumed = Thm::assume(closed_d.clone())?; // {Closed} ⊢ Closed_DB db d
    let ax_clause = assumed.and_elim_r()?; // {Closed} ⊢ ∀ax. db ax ⟹ d ax
    let at_a = ax_clause.all_elim(a.clone())?; // {Closed} ⊢ db A ⟹ d A
    let d_a = at_a.imp_elim(db_a)?; // {Closed} ⊢ d A
    d_a.imp_intro(&closed_d)? // ⊢ Closed_DB db d ⟹ d A
        .all_intro("d", pred_ty())
}

// ============================================================================
// `extends` — the extension relation `A ⊑ B`.
//
//   A ⊑ B := ∀ax. A ax ⟹ B ax        -- B's axiom set ⊇ A's.
// ============================================================================

/// `A ⊑ B := ∀ax. A ax ⟹ B ax` — the **extension relation** on databases:
/// every axiom of `A` is an axiom of `B`. A HOL `bool` term over the two
/// database terms `a`, `b`.
pub fn extends(a: &Term, b: &Term) -> Result<Term> {
    let ax = fvar("ax");
    app(a, &ax)?.imp(app(b, &ax)?)?.forall("ax", phi())
}

// ============================================================================
// Monotonicity — the theorem for the extension relation.
//
//   ⊢ A ⊑ B ⟹ Derivable_DB A S ⟹ Derivable_DB B S
//
// PROOF (purely logical, no induction on a verifier needed):
//   Assume  H_ext : A ⊑ B
//           H_der : Derivable_DB A S        ( = ∀d. Closed_DB A d ⟹ d S )
//           H_cb  : Closed_DB B d           (for arbitrary fixed d)
//   Goal: d S.
//   From H_cb get its two conjuncts: MP(d) and  (∀ax. B ax ⟹ d ax).
//   Build Closed_DB A d:
//     - MP(d): the *same* clause (structural, database-independent).      [reuse]
//     - ∀ax. A ax ⟹ d ax: fix ax, assume A ax; H_ext@ax gives B ax;
//       B's axiom clause @ax gives d ax.                                  [compose]
//   Instantiate H_der at d, discharge Closed_DB A d  ⟹  d S.
// ============================================================================

/// **Monotonicity of derivability under extension.**
///
/// ```text
///   ⊢ A ⊑ B ⟹ Derivable_DB A S ⟹ Derivable_DB B S
/// ```
///
/// An honest HOL theorem (no postulates / oracles): anything derivable in a
/// database stays derivable in any extension. `A`, `B : Database`, `S :
/// Φ⟨bool⟩` are free, so the result specialises to any concrete databases /
/// formula by [`Thm::inst`](covalence_core::Thm).
pub fn monotone() -> Result<Thm> {
    let a = Term::free("A", database_ty());
    let b = Term::free("B", database_ty());
    let s = fvar("S");
    let d = d_var();

    let ext_ab = extends(&a, &b)?; // A ⊑ B
    let der_a = derivable_db(&a, &s)?; // Derivable_DB A S
    let closed_b_d = closed(&b, &d)?; // Closed_DB B d

    // --- assume the three hypotheses ---
    let h_ext = Thm::assume(ext_ab.clone())?; // {ext} ⊢ A ⊑ B
    let h_der = Thm::assume(der_a.clone())?; // {der} ⊢ Derivable_DB A S
    let h_cb = Thm::assume(closed_b_d.clone())?; // {cb}  ⊢ Closed_DB B d

    // --- decompose Closed_DB B d into MP(d) and B's axiom clause ---
    let mp_d = h_cb.clone().and_elim_l()?; // {cb} ⊢ ∀A B. d A ∧ d⌜A⟹B⌝ ⟹ d B
    let b_ax = h_cb.and_elim_r()?; // {cb} ⊢ ∀ax. B ax ⟹ d ax

    // --- build A's axiom clause `∀ax. A ax ⟹ d ax` from `A ⊑ B` + `b_ax` ---
    let ax = fvar("ax");
    let a_ax_at = app(&a, &ax)?; // A ax
    let assume_a_ax = Thm::assume(a_ax_at.clone())?; // {A ax} ⊢ A ax
    // A ⊑ B @ ax : A ax ⟹ B ax
    let ext_at_ax = h_ext.all_elim(ax.clone())?; // {ext} ⊢ A ax ⟹ B ax
    let b_ax_thm = ext_at_ax.imp_elim(assume_a_ax)?; // {ext, A ax} ⊢ B ax
    // B's axiom clause @ ax : B ax ⟹ d ax
    let b_ax_at = b_ax.all_elim(ax.clone())?; // {cb} ⊢ B ax ⟹ d ax
    let d_ax = b_ax_at.imp_elim(b_ax_thm)?; // {ext, cb, A ax} ⊢ d ax
    let a_axiom_clause = d_ax
        .imp_intro(&a_ax_at)? // {ext, cb} ⊢ A ax ⟹ d ax
        .all_intro("ax", phi())?; // {ext, cb} ⊢ ∀ax. A ax ⟹ d ax

    // --- assemble Closed_DB A d = MP(d) ∧ (∀ax. A ax ⟹ d ax) ---
    let closed_a_d_thm = mp_d.and_intro(a_axiom_clause)?; // {ext, cb} ⊢ Closed_DB A d
    debug_assert_eq!(closed_a_d_thm.concl(), &closed(&a, &d)?);

    // --- instantiate Derivable_DB A S at d, discharge Closed_DB A d ---
    let der_at_d = h_der.all_elim(d.clone())?; // {der} ⊢ Closed_DB A d ⟹ d S
    let d_s = der_at_d.imp_elim(closed_a_d_thm)?; // {ext, der, cb} ⊢ d S

    // --- discharge Closed_DB B d, generalise d ⟹ Derivable_DB B S ---
    let der_b = d_s
        .imp_intro(&closed_b_d)? // {ext, der} ⊢ Closed_DB B d ⟹ d S
        .all_intro("d", pred_ty())?; // {ext, der} ⊢ Derivable_DB B S
    debug_assert_eq!(der_b.concl(), &derivable_db(&b, &s)?);

    // --- discharge the two outer hypotheses ---
    der_b
        .imp_intro(&der_a)? // {ext} ⊢ Derivable_DB A S ⟹ Derivable_DB B S
        .imp_intro(&ext_ab) // ⊢ A ⊑ B ⟹ Derivable_DB A S ⟹ Derivable_DB B S
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_genuine(thm: &Thm) {
        assert!(thm.hyps().is_empty(), "theorem is hypothesis-free");
    }

    /// A literal propositional variable `var k`, encoded at `Φ⟨bool⟩`.
    fn var(k: u32) -> Term {
        p_var_at(
            &bool_ty(),
            mk_nat(covalence_types::Nat::from_inner(k.into())),
        )
    }

    /// A concrete singleton database `{ax}`: the predicate `λf. f = ax`.
    fn singleton_db(ax: &Term) -> Term {
        let f = Term::free("__f", phi());
        let body = f.clone().equals(ax.clone()).unwrap();
        Term::abs(phi(), covalence_core::subst::close(&body, "__f"))
    }

    /// A concrete two-element database `{ax1, ax2}`: `λf. f = ax1 ∨ f = ax2`.
    fn pair_db(ax1: &Term, ax2: &Term) -> Term {
        let f = Term::free("__f", phi());
        let body = f
            .clone()
            .equals(ax1.clone())
            .unwrap()
            .or(f.clone().equals(ax2.clone()).unwrap())
            .unwrap();
        Term::abs(phi(), covalence_core::subst::close(&body, "__f"))
    }

    #[test]
    fn database_ty_is_phi_to_bool() {
        // The database type is exactly `Φ⟨bool⟩ → bool`.
        let dbt = database_ty();
        assert_eq!(dbt, Type::fun(phi(), Type::bool()));
        // And `Φ⟨bool⟩` is the reified-formula carrier, not bool itself.
        assert_ne!(phi(), Type::bool());
    }

    /// `Derivable_DB`, routed through the generic [`super::db_rule_set`] engine,
    /// is **byte-identical** to the hand-built `∀d. Closed_DB db d ⟹ d A`. Pins
    /// one derivability notion, no term drift.
    #[test]
    fn derivable_db_matches_inline_definition() {
        // The inline definition, reproduced verbatim here.
        fn inline(db: &Term, a: &Term) -> Result<Term> {
            let closed_d = closed(db, &d_var())?;
            closed_d.imp(app(&d_var(), a)?)?.forall("d", pred_ty())
        }
        let db = db_var();
        let a = fvar("A");
        assert_eq!(
            derivable_db(&db, &a).unwrap(),
            inline(&db, &a).unwrap(),
            "engine-routed Derivable_DB equals the inline impredicative form"
        );
        // And it is literally `metalogic::derivable` of the database rule set.
        assert_eq!(
            derivable_db(&db, &a).unwrap(),
            crate::metalogic::derivable(&db_rule_set(db.clone()), &a).unwrap(),
        );
    }

    #[test]
    fn derivable_db_is_well_typed_and_reads_the_database() {
        // Derivable_DB db A typechecks as a `bool` and genuinely mentions `db`.
        let t = derivable().unwrap();
        assert_eq!(t.type_of().unwrap(), Type::bool());
        assert!(
            format!("{t}").contains("db"),
            "derivability mentions the database value"
        );
    }

    #[test]
    fn extends_is_well_typed() {
        let a = Term::free("A", database_ty());
        let b = Term::free("B", database_ty());
        let t = extends(&a, &b).unwrap();
        assert_eq!(t.type_of().unwrap(), Type::bool());
    }

    /// The headline: **monotonicity** is a single genuine HOL theorem of the
    /// right shape `A ⊑ B ⟹ Derivable_DB A S ⟹ Derivable_DB B S`.
    #[test]
    fn monotonicity_is_genuine() {
        let thm = monotone().unwrap();
        assert_genuine(&thm);

        let a = Term::free("A", database_ty());
        let b = Term::free("B", database_ty());
        let s = fvar("S");
        let expected = extends(&a, &b)
            .unwrap()
            .imp(
                derivable_db(&a, &s)
                    .unwrap()
                    .imp(derivable_db(&b, &s).unwrap())
                    .unwrap(),
            )
            .unwrap();
        assert_eq!(
            thm.concl(),
            &expected,
            "monotonicity has the expected shape"
        );
    }

    /// **Concrete instance.** Base database `A = {p0}` (one axiom: the variable
    /// `var 0`), extension `B = A + {p1} = {p0, p1}`. We prove:
    ///   1. `⊢ A ⊑ B`               (B's axioms ⊇ A's),
    ///   2. `⊢ Derivable_DB A p0`   (p0 is an axiom of A, hence derivable), and
    ///   3. transport it across monotonicity to `⊢ Derivable_DB B p0`.
    #[test]
    fn concrete_extension_transports_a_fact() {
        let p0 = var(0);
        let p1 = var(1);
        let base = singleton_db(&p0); // A = {p0}
        let ext = pair_db(&p0, &p1); // B = {p0, p1}

        // ---- 1. ⊢ A ⊑ B : every axiom of A (i.e. f = p0) is an axiom of B ----
        // Goal ∀ax. (ax = p0) ⟹ (ax = p0 ∨ ax = p1).
        let ax = fvar("ax");
        let a_ax = app(&base, &ax).unwrap(); // (λf. f = p0) ax
        let a_ax_beta = prop_beta(&a_ax); // ⊢ A ax = (ax = p0)
        let b_ax = app(&ext, &ax).unwrap();
        let b_ax_beta = prop_beta(&b_ax); // ⊢ B ax = (ax = p0 ∨ ax = p1)

        // assume A ax, normalise to ax = p0, weaken to the disjunction, fold to B ax.
        let h = Thm::assume(a_ax.clone()).unwrap(); // {A ax} ⊢ A ax
        let eq0 = a_ax_beta.clone().eq_mp(h).unwrap(); // {A ax} ⊢ ax = p0
        let right_disjunct = ax.clone().equals(p1.clone()).unwrap(); // term `ax = p1`
        let disj = eq0.or_intro_l(right_disjunct).unwrap(); // {A ax} ⊢ (ax=p0) ∨ (ax=p1)
        let b_ax_thm = b_ax_beta.sym().unwrap().eq_mp(disj).unwrap(); // {A ax} ⊢ B ax
        let ext_thm = b_ax_thm
            .imp_intro(&a_ax)
            .unwrap()
            .all_intro("ax", phi())
            .unwrap(); // ⊢ A ⊑ B
        assert_genuine(&ext_thm);
        assert_eq!(ext_thm.concl(), &extends(&base, &ext).unwrap());

        // ---- 2. ⊢ Derivable_DB A p0 : p0 is an axiom of A, hence derivable ----
        let der_a_p0 = derive_axiom(&base, &p0).unwrap();
        assert_genuine(&der_a_p0);
        assert_eq!(der_a_p0.concl(), &derivable_db(&base, &p0).unwrap());

        // ---- 3. transport across monotonicity ⟹ ⊢ Derivable_DB B p0 ----
        let mono = monotone()
            .unwrap()
            .inst("A", base.clone())
            .unwrap()
            .inst("B", ext.clone())
            .unwrap()
            .inst("S", p0.clone())
            .unwrap(); // ⊢ A⊑B ⟹ Der_A p0 ⟹ Der_B p0
        let der_b_p0 = mono.imp_elim(ext_thm).unwrap().imp_elim(der_a_p0).unwrap();
        assert_genuine(&der_b_p0);
        assert_eq!(der_b_p0.concl(), &derivable_db(&ext, &p0).unwrap());

        // Sanity: the transported fact is over the *extension* database, distinct
        // from the base statement.
        assert_ne!(
            der_b_p0.concl(),
            &derivable_db(&base, &p0).unwrap(),
            "transported fact ranges over B, not A"
        );
    }

    /// β-reduce `(λf. body) ax` to `body[ax/f]`: `⊢ (λf. body) ax = body[ax/f]`.
    fn prop_beta(app_term: &Term) -> Thm {
        Thm::beta_conv(app_term.clone()).unwrap()
    }

    /// `⊢ Derivable_DB db A` when `A` is a (concrete) axiom of `db`: prove the
    /// membership `⊢ db A`, then lift it through [`derive_axiom_from_membership`].
    fn derive_axiom(db: &Term, a: &Term) -> Result<Thm> {
        let db_a = app(db, a)?; // db A
        let db_a_thm = prove_membership(a, &db_a)?; // ⊢ db A
        derive_axiom_from_membership(db_a_thm)
    }

    /// Prove `⊢ db A` for our concrete singleton/pair databases: β-reduce
    /// `db A` and discharge the resulting equality/disjunction by reflexivity.
    fn prove_membership(a: &Term, db_a: &Term) -> Result<Thm> {
        let beta = Thm::beta_conv(db_a.clone())?; // ⊢ db A = (membership prop)
        let prop = beta.concl().as_eq().expect("beta eq").1.clone();
        // The membership prop is either `A = A` (singleton) or `A = A ∨ A = q`
        // (pair, A the left). Reflexivity proves the equand `A = A`; weaken for ∨.
        let refl = Thm::refl(a.clone())?; // ⊢ A = A
        let mem_thm = if format!("{prop}").contains("bool.or") {
            // pair: prove the LEFT disjunct `A = A`, then weaken (`or_intro_l`).
            let (_op_lhs, right) = prop.as_app().expect("or app"); // (or lhs, right)
            refl.or_intro_l(right.clone())? // ⊢ (A = A) ∨ right
        } else {
            refl
        };
        beta.sym()?.eq_mp(mem_thm) // ⊢ db A
    }
}
