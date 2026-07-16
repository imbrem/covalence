//! **S3 — `Derivable_ACL2`: the reified ACL2 derivability predicate**
//! (design `notes/vibes/lisp/acl2-s0-s3-design.md` §6.2–§6.3).
//!
//! An [`Acl2Env`] is the *data* defining the logic: a list of closed
//! encoded axiom formulas plus the S1 primitive table
//! ([`super::prims::PrimRow`]). [`acl2_rule_set`] lays it out as a unary
//! [`crate::metalogic::RuleSet`] over the carrier `A` (clause order is
//! deterministic, [`Acl2Env::clause_index`]):
//!
//! ```text
//!   axioms   one clause per env axiom:  d ⌜ax⌝
//!   MP       ∀p q:A.  d ⌜(IF p (IF q 'T 'NIL) 'T)⌝ ⟹ d p ⟹ d q
//!   INST     ∀s:(bytes→A). ∀f:A.  d f ⟹ d (subst f s)
//!   cong(F)  ∀x⃗ y⃗:A.  d ⌜(EQUAL x₁ y₁)⌝ ⟹ … ⟹ d ⌜(EQUAL (F x⃗) (F y⃗))⌝
//!   comp(F)  ∀x⃗:A.    d ⌜(EQUAL (F 'x₁ … 'xₙ) '(f_model x⃗))⌝
//! ```
//!
//! and `Derivable_ACL2 φ := ∀d:A→bool. Closed d ⟹ d φ` — the
//! impredicative least predicate closed under those clauses
//! ([`derivable`]). A **derivation is a value `⊢ Derivable_ACL2 ⌜φ⌝`**:
//! pure syntactic data produced by the `derive_*` constructors (thin
//! wrappers over [`super::ladder::derive_mixed`]), each a genuine
//! hypothesis-free theorem about the *defined* predicate — no soundness
//! assumption anywhere. The certificate side (S11's book importer)
//! drives exactly these constructors.
//!
//! The ground S3 axiom list ([`ground_env`]): `equal-refl`, `equal-symm`,
//! `equal-trans` (curried through the `IMPLIES` macro shape), `if-true`,
//! `if-false` — closed carrier values with object variables encoded as
//! `asym "X"` etc.; instances flow from the INST clause through S2's
//! `subst` (with [`subst_ground`] computing the ground image so the
//! derivation lands on the substituted formula itself).
//!
//! The **soundness half** (§6.4–§6.5) lives here too:
//!
//! - [`sound_pred`] — `pred := λφ:A. ∀σ. ¬(eval φ σ = anil)`, the
//!   soundness predicate with the valuation ∀ **internalized** (forced by
//!   the INST clause: its discharge must vary σ, which is exactly why
//!   prop/PA's free-valuation shape is blocked here);
//! - [`soundness`] — `⊢ ∀A. Derivable_ACL2 A ⟹ (∀σ. ¬(eval A σ = anil))`
//!   by [`crate::metalogic::rule_induction`]: each of the 29 clauses is
//!   discharged at `d := pred` (axioms via the S1/S2 computation laws,
//!   MP via the `mk_implies` `aif`-shape, INST via S2's `subst_sema`,
//!   congruence via `equal_holds`, computation via `eval_quote` +
//!   `equal_refl`);
//! - [`project_acl2`] / [`project_with`] — one-step projection of a
//!   derivation to `⊢ ∀σ. ¬(eval ⌜φ⌝ σ = anil)`;
//! - [`transport_equal`] — for a projected ground equation, instantiate
//!   `σ := λv. anil`, compute `eval` by the S2 laws ([`eval_open`]), and
//!   land the **base-HOL model equation** through S1's `equal_holds`
//!   (the S3 gate: `⊢ aplus (aint 2) (aint 2) = aint 4`).

use std::sync::Arc;

use covalence_core::{Error, Result, Term, Type, subst};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::derived::DerivedRules;
use covalence_hol_eval::{as_blob, mk_blob, mk_int};
use smol_str::SmolStr;

use crate::init::acl2::carrier::acl2_payload;
use crate::init::acl2::ladder::{self, Premise};
use crate::init::acl2::prims::{PrimRow, eqf_intro};
use crate::init::acl2::term::{Terms, arc_terms};
use crate::init::cat::fun_ext;
use crate::init::cond::{collapse_conds, cond, cond_false, cond_true};
use crate::init::eq::{beta_expand, beta_nf, beta_reduce};
use crate::init::ext::{TermExt, ThmExt};
use crate::metalogic::RuleSet;

// ============================================================================
// The environment
// ============================================================================

/// How an env axiom clause is discharged in the soundness proof at
/// `d := pred` — the per-row hook API of S4+S6 design §2.2 (this is what
/// fills the old "S4+ axiom-discharge gap"). A wrong or unprovable
/// discharge *fails safe*: `soundness` errors, no theorem is minted, and
/// every output is re-checked by the `rule_induction` conjunction build.
pub enum Discharge {
    /// One of the built-in ground schemas (`equal-refl`, `equal-symm`,
    /// `equal-trans`, `if-true`, `if-false`), dispatched by name.
    Schema,
    /// An `EQUAL`-form axiom over object variables, discharged from a
    /// proved model equation `⊢ ∀v⃗. L(v⃗) = R(v⃗)` whose ∀s (in
    /// first-occurrence order of the axiom's object variables) eliminate
    /// to exactly the [`eval_open`] images of the two sides.
    ModelEq(Thm),
    /// A holds-form axiom, from `⊢ ∀v⃗. ¬(V(v⃗) = anil)` with `V` the
    /// [`eval_open`] image of the axiom body (same ∀ discipline).
    ModelHolds(Thm),
    /// Anything else: must return `⊢ ∀σ. ¬(eval ⌜enc⌝ σ = anil)` for
    /// *this env's* `eval`; the engine does the `expand_to_pred`
    /// β-plumbing.
    #[allow(clippy::type_complexity)]
    Hook(Arc<dyn Fn(&Acl2Env, &Term) -> Result<Thm> + Send + Sync>),
}

impl Clone for Discharge {
    fn clone(&self) -> Self {
        match self {
            Discharge::Schema => Discharge::Schema,
            Discharge::ModelEq(t) => Discharge::ModelEq(t.clone()),
            Discharge::ModelHolds(t) => Discharge::ModelHolds(t.clone()),
            Discharge::Hook(f) => Discharge::Hook(f.clone()),
        }
    }
}

/// One env axiom: a closed encoded formula plus its soundness discharge.
#[derive(Clone)]
pub struct AxiomRow {
    /// The axiom's name (clause lookup key).
    pub name: SmolStr,
    /// The closed encoded formula `⌜ax⌝`, over object variables
    /// `asym "X"` etc. — instances flow from the INST clause.
    pub enc: Term,
    /// How the soundness proof discharges this clause.
    pub discharge: Discharge,
}

/// One admitted user `defun` (S4+S6 design §2.1). The model constant is
/// minted **once at admission** and never re-defined, so transported
/// theorems mentioning it compose across env generations; only
/// `Derivable`/`eval`/`subst` and derivations are env-scoped.
#[derive(Clone)]
pub struct UserRow {
    /// The surface symbol, e.g. `"APP"` (distinct from every primitive,
    /// `QUOTE`, `IF`, and every earlier user row).
    pub name: SmolStr,
    /// The distinct formal names (object variables `asym ⌜Xᵢ⌝`).
    pub formals: Vec<SmolStr>,
    /// The encoded body `⌜body⌝ : A` (a closed carrier value).
    pub body: Term,
    /// `Some(r)` = structurally recursive on formal `r`; `None` = plain.
    pub rec_formal: Option<usize>,
    /// The model constant `f_model : A → … → A`.
    pub model: Term,
    /// `⌜(EQUAL (f X₁ … Xₙ) body)⌝` — the `Def(j)` clause formula.
    pub def_enc: Term,
    /// `⊢ ∀x⃗. f_model x⃗ = ⟦body⟧(x⃗)` — the **proved** model defining
    /// equation ([`super::defun`]; drives [`discharge_def`]).
    pub def_eq_model: Thm,
    /// The raw `Thm::define` equation of `model` (law re-derivation).
    pub(crate) def_eq: Thm,
}

/// The data defining `Derivable_ACL2`: encoded axioms + the row table
/// (primitives ++ admitted user defuns) + the user rows themselves.
/// **Invariant:** `rows == tm.rows()` — the deep-term theory is built
/// over exactly this table ([`Terms::build_with`]); constructors
/// (`ground_env`, `s6_env`, `defun::admit_defun`) maintain it.
#[derive(Clone)]
pub struct Acl2Env {
    /// The S2 deep-term theory (encoders, `eval`/`subst`, the S1/S0
    /// layers), built over this env's row table. Per-env since S4.
    pub tm: Arc<Terms>,
    /// The env axioms with their soundness discharges.
    pub axioms: Vec<AxiomRow>,
    /// The row table (drives the congruence + computation clause
    /// families): the 11 primitives, then one row per user defun.
    pub rows: Vec<PrimRow>,
    /// The admitted user defuns (one `Def` clause each).
    pub users: Vec<UserRow>,
    /// S6 flag (design §2.1): when set, the clause set additionally has
    /// the structural-induction clause `IND` and the implication-form
    /// congruence family `CongImpl(k)` (one per row). [`s6_env`] also
    /// installs the prop-k/prop-s Hilbert axioms and the structural
    /// axiom pack. `ground_env` keeps the committed 29-clause layout.
    pub s6: bool,
}

/// Which clause of the layout (see [`Acl2Env::clause_index`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ClauseKind {
    /// Axiom clause `i` (index into [`Acl2Env::axioms`]).
    Axiom(usize),
    /// The modus-ponens clause.
    Mp,
    /// The instantiation clause.
    Inst,
    /// The structural-induction clause (S6 envs only, design §8).
    Ind,
    /// The congruence clause for table row `k`.
    Cong(usize),
    /// The computation (quote-homomorphism) clause for table row `k`.
    Comp(usize),
    /// The implication-form congruence clause for table row `k`
    /// (S6 envs only, design §7.4).
    CongImpl(usize),
    /// The defining-equation clause for user row `j`.
    Def(usize),
}

impl Acl2Env {
    /// The deterministic clause index of `kind` in the layout
    /// (axioms, MP, INST, [IND], congruence family, computation family,
    /// [CongImpl family], defining equations). Matches the S4+S6 design
    /// §2.1 layout; the ground env (`s6 = 0`) keeps the committed
    /// 29-clause layout.
    pub fn clause_index(&self, kind: ClauseKind) -> usize {
        let na = self.axioms.len();
        let nr = self.rows.len();
        let s6 = usize::from(self.s6);
        match kind {
            ClauseKind::Axiom(i) => i,
            ClauseKind::Mp => na,
            ClauseKind::Inst => na + 1,
            ClauseKind::Ind => na + 2,
            ClauseKind::Cong(k) => na + 2 + s6 + k,
            ClauseKind::Comp(k) => na + 2 + s6 + nr + k,
            ClauseKind::CongImpl(k) => na + 2 + s6 + 2 * nr + k,
            ClauseKind::Def(j) => na + 2 + s6 + (2 + s6) * nr + j,
        }
    }

    /// Total clause count: `|axioms| + 2 + s6 + (2+s6)·|table| + |users|`.
    pub fn n_clauses(&self) -> usize {
        let s6 = usize::from(self.s6);
        self.axioms.len() + 2 + s6 + (2 + s6) * self.rows.len() + self.users.len()
    }

    /// Look up an axiom by name: `(index, encoded formula)`.
    pub fn axiom(&self, name: &str) -> Result<(usize, &Term)> {
        self.axioms
            .iter()
            .position(|r| r.name == name)
            .map(|i| (i, &self.axioms[i].enc))
            .ok_or_else(|| Error::ConnectiveRule(format!("acl2 env: no axiom named `{name}`")))
    }

    /// Look up a table row (primitive or user) by surface symbol.
    pub fn row(&self, sym: &str) -> Result<usize> {
        self.rows
            .iter()
            .position(|r| r.sym == sym)
            .ok_or_else(|| Error::ConnectiveRule(format!("acl2 env: no table row `{sym}`")))
    }

    /// Look up a user defun by surface symbol.
    pub fn user(&self, sym: &str) -> Result<(usize, &UserRow)> {
        self.users
            .iter()
            .position(|u| u.name == sym)
            .map(|j| (j, &self.users[j]))
            .ok_or_else(|| Error::ConnectiveRule(format!("acl2 env: no user defun `{sym}`")))
    }
}

/// The ground S3 environment: the five equality/if axiom schemas over
/// the full 11-row primitive table.
pub fn ground_env() -> Result<Acl2Env> {
    let tm = arc_terms()?;
    let x = tm.sym(b"X")?;
    let y = tm.sym(b"Y")?;
    let z = tm.sym(b"Z")?;
    let ax = |name: &str, t: Term| AxiomRow {
        name: SmolStr::new(name),
        enc: t,
        discharge: Discharge::Schema,
    };
    let axioms = vec![
        // (EQUAL X X)
        ax("equal-refl", tm.mk_equal(&x, &x)?),
        // (IMPLIES (EQUAL X Y) (EQUAL Y X))
        ax(
            "equal-symm",
            tm.mk_implies(&tm.mk_equal(&x, &y)?, &tm.mk_equal(&y, &x)?)?,
        ),
        // (IMPLIES (EQUAL X Y) (IMPLIES (EQUAL Y Z) (EQUAL X Z)))
        ax(
            "equal-trans",
            tm.mk_implies(
                &tm.mk_equal(&x, &y)?,
                &tm.mk_implies(&tm.mk_equal(&y, &z)?, &tm.mk_equal(&x, &z)?)?,
            )?,
        ),
        // (IMPLIES X (EQUAL (IF X Y Z) Y))
        ax(
            "if-true",
            tm.mk_implies(&x, &tm.mk_equal(&tm.mk_if(&x, &y, &z)?, &y)?)?,
        ),
        // (IMPLIES (EQUAL X 'NIL) (EQUAL (IF X Y Z) Z))   ('NIL = quoted anil)
        ax(
            "if-false",
            tm.mk_implies(
                &tm.mk_equal(&x, &tm.quote(&tm.th.nil)?)?,
                &tm.mk_equal(&tm.mk_if(&x, &y, &z)?, &z)?,
            )?,
        ),
    ];
    let rows = tm.rows().to_vec();
    Ok(Acl2Env {
        tm,
        axioms,
        rows,
        users: vec![],
        s6: false,
    })
}

/// The S6 environment (design §7): the ground env plus
///
/// - the Hilbert propositional axioms `prop-k` / `prop-s`
///   ([`Discharge::Schema`] arms — no classical axiom, §7.2),
/// - the structural axiom pack `car-cons` / `cdr-cons` (from the S1
///   theorems via [`Discharge::ModelEq`]) and `consp-cons`
///   ([`Discharge::ModelHolds`], from `consp_cons` + `t_ne_nil`),
/// - the `s6` clause-set flag: the `IND` structural-induction clause
///   (§8) and the implication-form congruence family `CongImpl(k)`
///   (§7.4).
pub fn s6_env() -> Result<Acl2Env> {
    let mut env = ground_env()?;
    let tm = env.tm.clone();
    let pr = tm.pr;
    let x = tm.sym(b"X")?;
    let y = tm.sym(b"Y")?;
    let z = tm.sym(b"Z")?;
    // prop-k: (IMPLIES X (IMPLIES Y X)).
    env.axioms.push(AxiomRow {
        name: SmolStr::new("prop-k"),
        enc: tm.mk_implies(&x, &tm.mk_implies(&y, &x)?)?,
        discharge: Discharge::Schema,
    });
    // prop-s: (IMPLIES (IMPLIES X (IMPLIES Y Z))
    //                  (IMPLIES (IMPLIES X Y) (IMPLIES X Z))).
    env.axioms.push(AxiomRow {
        name: SmolStr::new("prop-s"),
        enc: tm.mk_implies(
            &tm.mk_implies(&x, &tm.mk_implies(&y, &z)?)?,
            &tm.mk_implies(&tm.mk_implies(&x, &y)?, &tm.mk_implies(&x, &z)?)?,
        )?,
        discharge: Discharge::Schema,
    });
    // The structural pack (§7.3).
    let cons_xy = tm.app(b"CONS", &[x.clone(), y.clone()])?;
    env.axioms.push(AxiomRow {
        name: SmolStr::new("car-cons"),
        enc: tm.mk_equal(&tm.app(b"CAR", &[cons_xy.clone()])?, &x)?,
        discharge: Discharge::ModelEq(pr.car_cons()?),
    });
    env.axioms.push(AxiomRow {
        name: SmolStr::new("cdr-cons"),
        enc: tm.mk_equal(&tm.app(b"CDR", &[cons_xy.clone()])?, &y)?,
        discharge: Discharge::ModelEq(pr.cdr_cons()?),
    });
    // consp-cons: ⊢ ∀h t. ¬(aconsp (acons h t) = anil).
    let consp_holds = {
        let a = tm.th.ty.clone();
        let (h, t) = (Term::free("h", a.clone()), Term::free("t", a.clone()));
        let eq = pr.consp_cons()?.all_elim(h)?.all_elim(t)?; // aconsp (acons h t) = t
        ne_from_eq(&tm, eq, pr.t_ne_nil()?)?
            .all_intro("t", a.clone())?
            .all_intro("h", a)?
    };
    env.axioms.push(AxiomRow {
        name: SmolStr::new("consp-cons"),
        enc: tm.app(b"CONSP", &[cons_xy])?,
        discharge: Discharge::ModelHolds(consp_holds),
    });
    env.s6 = true;
    Ok(env)
}

// ============================================================================
// The rule set + Derivable_ACL2
// ============================================================================

/// `λn:bytes. cond (n = v) e (asym n)` — the single-point valuation
/// update of the IND clause (design §8), at an arbitrary variable-name
/// term `v : bytes`. At a *literal* `v` this is exactly
/// `finite_sigma(tm, &[(v, e)])` (same binder shape), so the clause's
/// `subst f (s_upd v ⌜(CAR v)⌝)` instances fold by [`subst_ground`].
pub(crate) fn sigma_upd(tm: &Terms, v: &Term, e: &Term) -> Result<Term> {
    let n = Term::free("__n", Type::bytes());
    let body = cond(tm.th.ty.clone())
        .apply(n.clone().equals(v.clone())?)?
        .apply(e.clone())?
        .apply(tm.th.asym_at(&n)?)?;
    Ok(Term::abs(Type::bytes(), subst::close(&body, "__n")))
}

/// The pieces of the IND clause at a variable (or literal) name term
/// `v`: `(⌜(CONSP v)⌝, base encoding, step encoding)` with the two
/// `subst f (s_upd …)` step antecedents **unreduced** (design §8).
fn ind_encs(tm: &Terms, f: &Term, v: &Term) -> Result<(Term, Term, Term)> {
    let asym_v = tm.th.asym_at(v)?;
    let consp_v = tm.app(b"CONSP", &[asym_v.clone()])?;
    let base = tm.mk_implies(&tm.mk_equal(&consp_v, &tm.quote(&tm.th.nil)?)?, f)?;
    let car_v = tm.app(b"CAR", &[asym_v.clone()])?;
    let cdr_v = tm.app(b"CDR", &[asym_v])?;
    let sub = |e: &Term| -> Result<Term> {
        tm.subst
            .clone()
            .apply(f.clone())?
            .apply(sigma_upd(tm, v, e)?)
    };
    let step = tm.mk_implies(
        &consp_v,
        &tm.mk_implies(&sub(&car_v)?, &tm.mk_implies(&sub(&cdr_v)?, f)?)?,
    )?;
    Ok((consp_v, base, step))
}

/// The `CongImpl(k)` clause formula (design §7.4): the curried
/// implication-form congruence encoding
/// `⌜(IMPLIES (EQUAL x₁ y₁) (… (EQUAL (F x⃗) (F y⃗))))⌝` for table row
/// `row` at argument pairs `(xᵢ, yᵢ)`.
pub(crate) fn cong_impl_enc(tm: &Terms, row: &PrimRow, xs: &[Term], ys: &[Term]) -> Result<Term> {
    let f_xs = tm.app(row.sym.as_bytes(), xs)?;
    let f_ys = tm.app(row.sym.as_bytes(), ys)?;
    let mut body = tm.mk_equal(&f_xs, &f_ys)?;
    for (x, y) in xs.iter().zip(ys).rev() {
        body = tm.mk_implies(&tm.mk_equal(x, y)?, &body)?;
    }
    Ok(body)
}

/// Lay the environment out as a unary [`RuleSet`] over the carrier `A`
/// (clause order per [`Acl2Env::clause_index`]).
pub fn acl2_rule_set(env: &Acl2Env) -> RuleSet<'_> {
    let tm = &env.tm;
    let a = tm.th.ty.clone();
    RuleSet::new(a.clone(), move |d_apply| {
        let mut clauses = Vec::with_capacity(env.n_clauses());

        // Axiom clauses: d ⌜ax⌝.
        for row in &env.axioms {
            clauses.push(d_apply(&row.enc)?);
        }

        // MP: ∀p q. d ⌜(IMPLIES p q)⌝ ⟹ d p ⟹ d q.
        {
            let p = Term::free("p", a.clone());
            let q = Term::free("q", a.clone());
            let body = d_apply(&tm.mk_implies(&p, &q)?)?.imp(d_apply(&p)?.imp(d_apply(&q)?)?)?;
            clauses.push(body.forall("q", a.clone())?.forall("p", a.clone())?);
        }

        // INST: ∀s φ. d φ ⟹ d (subst φ s).
        {
            let s = Term::free("s", tm.val_ty.clone());
            let f = Term::free("f", a.clone());
            let sub = tm.subst.clone().apply(f.clone())?.apply(s.clone())?;
            let body = d_apply(&f)?.imp(d_apply(&sub)?)?;
            clauses.push(
                body.forall("f", a.clone())?
                    .forall("s", tm.val_ty.clone())?,
            );
        }

        // IND (S6 envs, design §8): tree induction over the formula-as-
        // data f and the designated variable name v, both IHs, premises
        // base then step, the `subst` step antecedents unreduced.
        if env.s6 {
            let f = Term::free("f", a.clone());
            let v = Term::free("v", Type::bytes());
            let (_, base, step) = ind_encs(tm, &f, &v)?;
            let body = d_apply(&base)?.imp(d_apply(&step)?.imp(d_apply(&f)?)?)?;
            clauses.push(body.forall("v", Type::bytes())?.forall("f", a.clone())?);
        }

        // Congruence clauses (arity-templated), one per table row:
        // ∀x⃗ y⃗. d ⌜(EQUAL x₁ y₁)⌝ ⟹ … ⟹ d ⌜(EQUAL (F x⃗) (F y⃗))⌝.
        for row in &env.rows {
            let xn: Vec<String> = (1..=row.arity).map(|i| format!("x{i}")).collect();
            let yn: Vec<String> = (1..=row.arity).map(|i| format!("y{i}")).collect();
            let xs: Vec<Term> = xn
                .iter()
                .map(|n| Term::free(n.as_str(), a.clone()))
                .collect();
            let ys: Vec<Term> = yn
                .iter()
                .map(|n| Term::free(n.as_str(), a.clone()))
                .collect();
            let f_xs = tm.app(row.sym.as_bytes(), &xs)?;
            let f_ys = tm.app(row.sym.as_bytes(), &ys)?;
            let mut body = d_apply(&tm.mk_equal(&f_xs, &f_ys)?)?;
            for (x, y) in xs.iter().zip(&ys).rev() {
                body = d_apply(&tm.mk_equal(x, y)?)?.imp(body)?;
            }
            // Quantify ∀x₁ y₁ x₂ y₂ … (outermost x₁).
            for (xname, yname) in xn.iter().zip(&yn).rev() {
                body = body
                    .forall(yname.as_str(), a.clone())?
                    .forall(xname.as_str(), a.clone())?;
            }
            clauses.push(body);
        }

        // Computation clauses (the quote-homomorphism family), one per
        // row: ∀x⃗. d ⌜(EQUAL (F 'x₁ … 'xₙ) '(f_model x⃗))⌝.
        for row in &env.rows {
            let xn: Vec<String> = (1..=row.arity).map(|i| format!("x{i}")).collect();
            let xs: Vec<Term> = xn
                .iter()
                .map(|n| Term::free(n.as_str(), a.clone()))
                .collect();
            let quoted: Vec<Term> = xs.iter().map(|x| tm.quote(x)).collect::<Result<_>>()?;
            let lhs = tm.app(row.sym.as_bytes(), &quoted)?;
            let mut model = row.model.clone();
            for x in &xs {
                model = model.apply(x.clone())?;
            }
            let rhs = tm.quote(&model)?;
            let mut body = d_apply(&tm.mk_equal(&lhs, &rhs)?)?;
            for xname in xn.iter().rev() {
                body = body.forall(xname.as_str(), a.clone())?;
            }
            clauses.push(body);
        }

        // CongImpl clauses (S6 envs, design §7.4), one per table row:
        // ∀x⃗ y⃗. d ⌜(IMPLIES (EQUAL x₁ y₁) (… (EQUAL (F x⃗) (F y⃗))))⌝
        // — congruence usable *under object hypotheses* (no deduction
        // theorem for the rule-form Cong clause).
        if env.s6 {
            for row in &env.rows {
                let xn: Vec<String> = (1..=row.arity).map(|i| format!("x{i}")).collect();
                let yn: Vec<String> = (1..=row.arity).map(|i| format!("y{i}")).collect();
                let xs: Vec<Term> = xn
                    .iter()
                    .map(|n| Term::free(n.as_str(), a.clone()))
                    .collect();
                let ys: Vec<Term> = yn
                    .iter()
                    .map(|n| Term::free(n.as_str(), a.clone()))
                    .collect();
                let mut body = d_apply(&cong_impl_enc(tm, row, &xs, &ys)?)?;
                for (xname, yname) in xn.iter().zip(&yn).rev() {
                    body = body
                        .forall(yname.as_str(), a.clone())?
                        .forall(xname.as_str(), a.clone())?;
                }
                clauses.push(body);
            }
        }

        // Defining-equation clauses, one per user defun:
        // Def(j): d ⌜(EQUAL (f X₁ … Xₙ) body)⌝ (instances flow via INST).
        for u in &env.users {
            clauses.push(d_apply(&u.def_enc)?);
        }

        Ok(clauses)
    })
}

/// `Derivable_ACL2 φ := ∀d. Closed d ⟹ d φ` — the impredicative least
/// predicate over the environment's clause set, at an encoded formula
/// `φ : A`.
pub fn derivable(env: &Acl2Env, phi: &Term) -> Result<Term> {
    crate::metalogic::derivable(&acl2_rule_set(env), phi)
}

// ============================================================================
// Derivation constructors (each ⊢ Derivable_ACL2 ⌜…⌝, hypothesis-free)
// ============================================================================

/// Fire clause `kind` with `args`/`premises` (thin wrapper binding the
/// env's layout to [`ladder::derive_mixed`]).
fn fire(env: &Acl2Env, kind: ClauseKind, args: &[Term], premises: Vec<Premise>) -> Result<Thm> {
    ladder::derive_mixed(
        &acl2_rule_set(env),
        env.clause_index(kind),
        env.n_clauses(),
        args,
        premises,
    )
}

/// `⊢ Derivable_ACL2 ⌜ax⌝` for the named env axiom.
pub fn derive_axiom(env: &Acl2Env, name: &str) -> Result<Thm> {
    let (i, _) = env.axiom(name)?;
    fire(env, ClauseKind::Axiom(i), &[], vec![])
}

/// Modus ponens: from `d_imp : ⊢ Derivable_ACL2 ⌜(IMPLIES p q)⌝` and
/// `d_p : ⊢ Derivable_ACL2 ⌜p⌝`, derive `⊢ Derivable_ACL2 ⌜q⌝`. `p`/`q`
/// are passed explicitly (they instantiate the clause's `∀p q`); the
/// kernel's `imp_elim` re-checks that they match the premises.
pub fn derive_mp(env: &Acl2Env, p: &Term, q: &Term, d_imp: Thm, d_p: Thm) -> Result<Thm> {
    fire(
        env,
        ClauseKind::Mp,
        &[p.clone(), q.clone()],
        vec![Premise::Derivation(d_imp), Premise::Derivation(d_p)],
    )
}

/// Instantiation: from `d_phi : ⊢ Derivable_ACL2 ⌜φ⌝` and a concrete
/// substitution `s : bytes → A` (variable names to term encodings),
/// derive `⊢ Derivable_ACL2 (subst ⌜φ⌝ s)` — the *unreduced* `subst`
/// image (fold it with [`subst_ground`] / [`derive_inst_ground`]).
pub fn derive_inst(env: &Acl2Env, phi: &Term, s: &Term, d_phi: Thm) -> Result<Thm> {
    fire(
        env,
        ClauseKind::Inst,
        &[s.clone(), phi.clone()],
        vec![Premise::Derivation(d_phi)],
    )
}

/// [`derive_inst`] with the `subst` image computed away: for a *ground*
/// `φ` (literal symbols/ints, quotes, table applications) and a finite
/// cond-chain `s` (see [`finite_sigma`]), derive
/// `⊢ Derivable_ACL2 ⌜φ[s]⌝` directly.
pub fn derive_inst_ground(env: &Acl2Env, phi: &Term, s: &Term, d_phi: Thm) -> Result<Thm> {
    let raw = derive_inst(env, phi, s, d_phi)?;
    let fold = subst_ground(&env.tm, phi, s)?; // ⊢ subst ⌜φ⌝ s = ⌜φ[s]⌝
    raw.rewrite(&fold)
}

/// Congruence for table row `k`: from per-argument equality derivations
/// `d_eqs[i] : ⊢ Derivable_ACL2 ⌜(EQUAL xᵢ yᵢ)⌝` at the argument pairs
/// `pairs = [(x₁,y₁), …]`, derive
/// `⊢ Derivable_ACL2 ⌜(EQUAL (F x⃗) (F y⃗))⌝`.
pub fn derive_cong(
    env: &Acl2Env,
    k: usize,
    pairs: &[(Term, Term)],
    d_eqs: Vec<Thm>,
) -> Result<Thm> {
    let row = env
        .rows
        .get(k)
        .ok_or_else(|| Error::ConnectiveRule(format!("acl2 derive_cong: bad table row {k}")))?;
    if pairs.len() != row.arity || d_eqs.len() != row.arity {
        return Err(Error::ConnectiveRule(format!(
            "acl2 derive_cong: row `{}` wants {} argument pairs/premises",
            row.sym, row.arity
        )));
    }
    let args: Vec<Term> = pairs
        .iter()
        .flat_map(|(x, y)| [x.clone(), y.clone()])
        .collect();
    fire(
        env,
        ClauseKind::Cong(k),
        &args,
        d_eqs.into_iter().map(Premise::Derivation).collect(),
    )
}

/// Computation for table row `k` at concrete carrier values `args`:
/// `⊢ Derivable_ACL2 ⌜(EQUAL (F 'x₁ … 'xₙ) '(f_model x⃗))⌝` — the model
/// image *unevaluated* (fold it with a model computation law, e.g.
/// [`derive_plus_lit`]).
pub fn derive_comp(env: &Acl2Env, k: usize, args: &[Term]) -> Result<Thm> {
    let row = env
        .rows
        .get(k)
        .ok_or_else(|| Error::ConnectiveRule(format!("acl2 derive_comp: bad table row {k}")))?;
    if args.len() != row.arity {
        return Err(Error::ConnectiveRule(format!(
            "acl2 derive_comp: row `{}` wants {} arguments",
            row.sym, row.arity
        )));
    }
    fire(env, ClauseKind::Comp(k), args, vec![])
}

/// [`derive_comp`] with the model image folded by `model_eq`
/// (`⊢ f_model x⃗ = v`): lands `⊢ Derivable_ACL2 ⌜(EQUAL (F 'x⃗) 'v)⌝`.
pub fn derive_comp_folded(env: &Acl2Env, k: usize, args: &[Term], model_eq: &Thm) -> Result<Thm> {
    derive_comp(env, k, args)?.rewrite(model_eq)
}

/// Defining equation for user row `j`:
/// `⊢ Derivable_ACL2 ⌜(EQUAL (f X₁ … Xₙ) body)⌝` — the `Def(j)` clause,
/// over the formal names as object variables (instances flow through
/// INST, foldable by [`subst_ground`]).
pub fn derive_def(env: &Acl2Env, j: usize) -> Result<Thm> {
    if j >= env.users.len() {
        return Err(Error::ConnectiveRule(format!(
            "acl2 derive_def: bad user row {j}"
        )));
    }
    fire(env, ClauseKind::Def(j), &[], vec![])
}

/// Implication-form congruence for table row `k` (S6 envs): fire the
/// `CongImpl(k)` clause at the argument pairs, landing the hyp-free
/// `⊢ Derivable_ACL2 ⌜(IMPLIES (EQUAL x₁ y₁) (… (EQUAL (F x⃗) (F y⃗))))⌝`
/// (its antecedents are then discharged *inside* the object logic by
/// MP — this is what the [`super::hilbert`] deduction compiler leans on).
pub fn derive_cong_impl(env: &Acl2Env, k: usize, pairs: &[(Term, Term)]) -> Result<Thm> {
    if !env.s6 {
        return Err(Error::ConnectiveRule(
            "acl2 derive_cong_impl: not an S6 env (no CongImpl clauses)".into(),
        ));
    }
    let row = env.rows.get(k).ok_or_else(|| {
        Error::ConnectiveRule(format!("acl2 derive_cong_impl: bad table row {k}"))
    })?;
    if pairs.len() != row.arity {
        return Err(Error::ConnectiveRule(format!(
            "acl2 derive_cong_impl: row `{}` wants {} argument pairs",
            row.sym, row.arity
        )));
    }
    let args: Vec<Term> = pairs
        .iter()
        .flat_map(|(x, y)| [x.clone(), y.clone()])
        .collect();
    fire(env, ClauseKind::CongImpl(k), &args, vec![])
}

/// **Structural induction** (S6 envs, design §8): from
///
/// - `d_base : ⊢ D ⌜(IMPLIES (EQUAL (CONSP v) 'NIL) φ)⌝` and
/// - `d_step : ⊢ D ⌜(IMPLIES (CONSP v) (IMPLIES φ[v ↦ (CAR v)]
///   (IMPLIES φ[v ↦ (CDR v)] φ)))⌝` (the *folded* substitution
///   instances, as [`subst_ground`] computes them),
///
/// derive `⊢ Derivable_ACL2 ⌜φ⌝`. The IND clause states its step
/// antecedents with **unreduced** `subst φ (s_upd …)` subterms; this
/// constructor folds them internally (rewriting the *sym* of the
/// [`subst_ground`] fold into `d_step` — the `derive_comp_folded`
/// safety argument: a wrong fold fails the kernel's `imp_elim`, it
/// never mis-derives). `φ` must be a ground encoding over literal
/// object variables (so the folds compute); `v` names the induction
/// variable. If `v` does not occur in `φ` the fold is the identity and
/// the internal rewrite degenerates — callers should not do that (the
/// clause instance would anyway be no stronger than its own premise).
pub fn derive_ind(env: &Acl2Env, phi: &Term, v: &[u8], d_base: Thm, d_step: Thm) -> Result<Thm> {
    if !env.s6 {
        return Err(Error::ConnectiveRule(
            "acl2 derive_ind: not an S6 env (no IND clause)".into(),
        ));
    }
    let tm = &*env.tm;
    let v_lit = mk_blob(covalence_types::Bytes::from(v.to_vec()));
    let car_enc = tm.app(b"CAR", &[tm.sym(v)?])?;
    let cdr_enc = tm.app(b"CDR", &[tm.sym(v)?])?;
    // At a literal name these are exactly the clause's s_upd instances.
    let s_car = finite_sigma(tm, &[(v, car_enc)])?;
    let s_cdr = finite_sigma(tm, &[(v, cdr_enc)])?;
    let fold_car = subst_ground(tm, phi, &s_car)?; // ⊢ subst ⌜φ⌝ s_car = ⌜φ[v↦(CAR v)]⌝
    let fold_cdr = subst_ground(tm, phi, &s_cdr)?;
    let step_unreduced = d_step
        .rewrite(&fold_car.sym()?)?
        .rewrite(&fold_cdr.sym()?)?;
    fire(
        env,
        ClauseKind::Ind,
        &[phi.clone(), v_lit],
        vec![
            Premise::Derivation(d_base),
            Premise::Derivation(step_unreduced),
        ],
    )
}

/// Ground `+` fact: `⊢ Derivable_ACL2 ⌜(EQUAL (BINARY-+ 'i 'j) 'k)⌝`
/// with `k = i + j` folded by S1's literal law (`Prims::plus_lit`) — the
/// computation-clause instance the S3 gate transports.
pub fn derive_plus_lit(env: &Acl2Env, i: i128, j: i128) -> Result<Thm> {
    let tm = &*env.tm;
    let k = env.row("BINARY-+")?;
    let args = [tm.th.aint_at(&mk_int(i))?, tm.th.aint_at(&mk_int(j))?];
    derive_comp_folded(env, k, &args, &tm.pr.plus_lit(i, j)?)
}

// ============================================================================
// Ground substitution computation (the INST-folding engine)
// ============================================================================

/// `λn:bytes. cond (n = ⌜k₁⌝) v₁ (cond … (asym n))` — a finite
/// substitution as a nested cond-chain over variable names with the
/// identity default (the S2 `t_subst_ground` shape, packaged for
/// [`derive_inst_ground`] callers).
pub fn finite_sigma(tm: &Terms, binds: &[(&[u8], Term)]) -> Result<Term> {
    let n = Term::free("__n", Type::bytes());
    let mut body = tm.th.asym_at(&n)?;
    for (name, v) in binds.iter().rev() {
        let name_lit = mk_blob(covalence_types::Bytes::from(name.to_vec()));
        body = cond(tm.th.ty.clone())
            .apply(n.clone().equals(name_lit)?)?
            .apply(v.clone())?
            .apply(body)?;
    }
    Ok(Term::abs(Type::bytes(), subst::close(&body, "__n")))
}

/// The head symbol's bytes, if `t = asym ⌜lit⌝`.
pub(crate) fn sym_lit_of(tm: &Terms, t: &Term) -> Option<Vec<u8>> {
    let (f, arg) = t.as_app()?;
    if *f != tm.th.asym {
        return None;
    }
    Some(as_blob(arg)?.to_vec())
}

/// `⊢ subst ⌜φ⌝ s = ⌜φ[s]⌝` for the ground fragment (literal-symbol
/// variables, `aint` literals, `anil`, quotes, applications with
/// literal-symbol heads) and a literal cond-chain `s` (whose guards
/// `reduce` decides). Chains the S2 computation laws; the RHS is the
/// fully substituted encoding.
pub fn subst_ground(tm: &Terms, phi: &Term, s: &Term) -> Result<Thm> {
    let bad = || {
        Error::ConnectiveRule(format!(
            "acl2 subst_ground: not a ground pseudo-term: {phi}"
        ))
    };
    // anil.
    if *phi == tm.th.nil {
        return tm.subst_nil()?.all_elim(s.clone());
    }
    // asym ⌜v⌝ — look the name up through the cond-chain.
    if let Some(_name) = sym_lit_of(tm, phi) {
        let (_, lit) = phi.as_app().ok_or_else(bad)?;
        return tm
            .subst_var()?
            .all_elim(lit.clone())?
            .all_elim(s.clone())?
            .rhs_conv(|u| u.reduce())?
            .rhs_conv(collapse_conds);
    }
    // aint ⌜i⌝ (and any aint-headed term).
    if let Some((f, i)) = phi.as_app()
        && *f == tm.th.aint
    {
        return tm.subst_int()?.all_elim(i.clone())?.all_elim(s.clone());
    }
    // acons h t.
    let (ch, t) = phi.as_app().ok_or_else(bad)?;
    let (c, h) = ch.as_app().ok_or_else(bad)?;
    if *c != tm.th.cons {
        return Err(bad());
    }
    // Quoted form: opaque.
    if *h == tm.qsym {
        return tm.subst_quote()?.all_elim(t.clone())?.all_elim(s.clone());
    }
    // Application with a literal symbol head ≠ QUOTE.
    let name = sym_lit_of(tm, h).ok_or_else(bad)?;
    let ne = tm.th.sym_ne(&name, b"QUOTE")?;
    let tail = lsubst_ground(tm, t, s)?;
    tm.subst_app()?
        .all_elim(h.clone())?
        .all_elim(t.clone())?
        .all_elim(s.clone())?
        .imp_elim(ne)?
        .rhs_conv(|u| u.rw_all(&tail))
}

/// `⊢ lsubst ⌜t⌝ s = ⌜t[s]⌝` for a ground nil-terminated argument list.
pub fn lsubst_ground(tm: &Terms, t: &Term, s: &Term) -> Result<Thm> {
    if *t == tm.th.nil {
        return tm.lsubst_nil()?.all_elim(s.clone());
    }
    let bad = || {
        Error::ConnectiveRule(format!(
            "acl2 lsubst_ground: not a ground argument list: {t}"
        ))
    };
    let (ch, tail) = t.as_app().ok_or_else(bad)?;
    let (c, h) = ch.as_app().ok_or_else(bad)?;
    if *c != tm.th.cons {
        return Err(bad());
    }
    let head_eq = subst_ground(tm, h, s)?;
    let tail_eq = lsubst_ground(tm, tail, s)?;
    tm.lsubst_cons()?
        .all_elim(h.clone())?
        .all_elim(tail.clone())?
        .all_elim(s.clone())?
        .rhs_conv(|u| u.rw_all(&head_eq))?
        .rhs_conv(|u| u.rw_all(&tail_eq))
}

// ============================================================================
// Ground evaluation computation (the soundness/transport engine)
// ============================================================================

/// Split `acons h t` into `(h, t)`.
pub(crate) fn uncons(tm: &Terms, t: &Term) -> Option<(Term, Term)> {
    let (ch, tail) = t.as_app()?;
    let (c, h) = ch.as_app()?;
    if *c != tm.th.cons {
        return None;
    }
    Some((h.clone(), tail.clone()))
}

/// `⊢ eval φ σ = ⟦φ⟧σ` for the pseudo-term fragment (symbols, `aint`
/// literals, `anil`, quotes, `IF`, table applications), at an arbitrary
/// `σ` (free or a concrete λ). The image is **symbolic**: variables stay
/// `σ ⌜v⌝`, model applications stay unfolded (fold them separately, e.g.
/// by `Prims::plus_lit`), and free-`A`-variable subterms stay `eval x σ`
/// (the fallback is `refl` — this is what lets the MP/congruence clause
/// discharges evaluate schematic formulas).
pub fn eval_open(tm: &Terms, phi: &Term, sg: &Term) -> Result<Thm> {
    // anil.
    if *phi == tm.th.nil {
        return tm.eval_nil()?.all_elim(sg.clone());
    }
    // asym v — a variable (literal *or* free/schematic name, design
    // §7.1): look up through σ. The `eval_var` law is ∀-quantified over
    // the name, so any bytes-typed argument eliminates it.
    if let Some((f, name)) = phi.as_app()
        && *f == tm.th.asym
    {
        return tm.eval_var()?.all_elim(name.clone())?.all_elim(sg.clone());
    }
    // aint i — integers self-evaluate.
    if let Some((f, i)) = phi.as_app()
        && *f == tm.th.aint
    {
        return tm.eval_int()?.all_elim(i.clone())?.all_elim(sg.clone());
    }
    let fallback =
        || -> Result<Thm> { Thm::refl(tm.eval.clone().apply(phi.clone())?.apply(sg.clone())?) };
    // acons h t — quote / IF / table application.
    let Some((h, t)) = uncons(tm, phi) else {
        return fallback();
    };
    if h == tm.qsym {
        // (QUOTE x) evaluates to its raw payload.
        let (x, tail) = uncons(tm, &t).ok_or_else(|| {
            Error::ConnectiveRule(format!("acl2 eval_open: malformed quote payload: {phi}"))
        })?;
        if tail != tm.th.nil {
            return Err(Error::ConnectiveRule(format!(
                "acl2 eval_open: malformed quote payload: {phi}"
            )));
        }
        return tm.eval_quote()?.all_elim(x)?.all_elim(sg.clone());
    }
    let Some(name) = sym_lit_of(tm, &h) else {
        return fallback();
    };
    let (law, arity) = if name == b"IF" {
        (tm.eval_app_if()?, 3)
    } else {
        // The env's row table (primitives ++ user defuns) — NOT the bare
        // primitive table: S4 user functions dispatch here too.
        let Some(k) = tm.rows().iter().position(|r| r.sym.as_bytes() == name) else {
            return fallback(); // unknown head: no law, stays symbolic
        };
        (tm.eval_app(k)?, tm.rows()[k].arity)
    };
    let law = law.all_elim(t.clone())?.all_elim(sg.clone())?;
    let ls = evlis_open(tm, &t, sg)?; // ⊢ evlis t σ = L
    let mut acc = law.rhs_conv(|u| u.rw_all(&ls))?;
    // Project `car (cdr^i L)` down to the i-th evaluated argument.
    let mut lst = ls.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
    for i in 0..arity {
        let (w, rest) = uncons(tm, &lst).ok_or_else(|| {
            Error::ConnectiveRule(format!(
                "acl2 eval_open: argument list of {phi} shorter than arity {arity}"
            ))
        })?;
        let car_eq = tm.th.cs.proj_scons(false, &w, &rest)?; // car (acons w r) = w
        acc = acc.rhs_conv(|u| u.rw_all(&car_eq))?;
        if i + 1 < arity {
            let cdr_eq = tm.th.cs.proj_scons(true, &w, &rest)?; // cdr (acons w r) = r
            acc = acc.rhs_conv(|u| u.rw_all(&cdr_eq))?;
        }
        lst = rest;
    }
    Ok(acc)
}

/// `⊢ evlis t σ = acons ⟦a₁⟧σ (… anil)` for a nil-terminated argument
/// list, elements evaluated by [`eval_open`].
pub fn evlis_open(tm: &Terms, t: &Term, sg: &Term) -> Result<Thm> {
    if *t == tm.th.nil {
        return tm.evlis_nil()?.all_elim(sg.clone());
    }
    let (h, rest) = uncons(tm, t).ok_or_else(|| {
        Error::ConnectiveRule(format!("acl2 evlis_open: not a nil-terminated list: {t}"))
    })?;
    let law = tm
        .evlis_cons()?
        .all_elim(h.clone())?
        .all_elim(rest.clone())?
        .all_elim(sg.clone())?;
    let he = eval_open(tm, &h, sg)?;
    let te = evlis_open(tm, &rest, sg)?;
    let mut acc = law;
    // Skip identity rewrites (the free-variable fallback).
    let (hl, hr) = he.concl().as_eq().ok_or(Error::NotAnEquation)?;
    if hl != hr {
        acc = acc.rhs_conv(|u| u.rw_all(&he))?;
    }
    let (tl, tr) = te.concl().as_eq().ok_or(Error::NotAnEquation)?;
    if tl != tr {
        acc = acc.rhs_conv(|u| u.rw_all(&te))?;
    }
    Ok(acc)
}

// ============================================================================
// Soundness (§6.4): pred := λφ. ∀σ. ¬(eval φ σ = anil), by rule induction
// ============================================================================

/// The soundness predicate `λφ:A. ∀σ:(bytes→A). ¬(eval φ σ = anil)` —
/// the valuation ∀ is **internal** (the INST discharge must vary σ).
pub fn sound_pred(tm: &Terms) -> Result<Term> {
    let phi = Term::free("__sp", tm.th.ty.clone());
    let sg = Term::free("sg", tm.val_ty.clone());
    let body = tm
        .eval
        .clone()
        .apply(phi.clone())?
        .apply(sg.clone())?
        .equals(tm.th.nil.clone())?
        .not()?
        .forall("sg", tm.val_ty.clone())?;
    Ok(Term::abs(tm.th.ty.clone(), subst::close(&body, "__sp")))
}

/// From `Γ ⊢ v = w` and `Δ ⊢ ¬(w = anil)`, conclude `Γ∪Δ ⊢ ¬(v = anil)`.
fn ne_from_eq(tm: &Terms, eq: Thm, ne_w: Thm) -> Result<Thm> {
    let (v, _) = eq.concl().as_eq().ok_or(Error::NotAnEquation)?;
    let hyp = v.clone().equals(tm.th.nil.clone())?;
    let w_nil = eq.clone().sym()?.trans(Thm::assume(hyp.clone())?)?; // {v=anil} ⊢ w = anil
    ne_w.not_elim(w_nil)?.imp_intro(&hyp)?.not_intro()
}

/// From `Γ ⊢ v = w` and `Δ ⊢ ¬(v = anil)`, conclude `Γ∪Δ ⊢ ¬(w = anil)`.
fn ne_transport(tm: &Terms, eq: &Thm, ne_v: Thm) -> Result<Thm> {
    let (_, w) = eq.concl().as_eq().ok_or(Error::NotAnEquation)?;
    let hyp = w.clone().equals(tm.th.nil.clone())?;
    let v_nil = eq.clone().trans(Thm::assume(hyp.clone())?)?; // {w=anil} ⊢ v = anil
    ne_v.not_elim(v_nil)?.imp_intro(&hyp)?.not_intro()
}

/// **Fire an evaluated `IMPLIES` shape** (design §7.1, the factored
/// `discharge_mp` core): from
/// `whole_ne : Γ ⊢ ¬(aif e_p (aif e_q t anil) t = anil)` and
/// `guard : Δ ⊢ ¬(e_p = anil)`, conclude `Γ∪Δ ⊢ ¬(e_q = anil)` —
/// assume `e_q = anil`, collapse both `aif`s (`if_nil` inside, `if_t`
/// with the guard outside) to `anil`, contradict `whole_ne`. The IND
/// discharge iterates this three deep.
fn fire_implies(tm: &Terms, whole_ne: Thm, e_p: &Term, e_q: &Term, guard: Thm) -> Result<Thm> {
    let pr = tm.pr;
    let anil = tm.th.nil.clone();
    let t = pr.t.clone();
    let g = e_q.clone().equals(anil.clone())?;
    // {e_q = anil} ⊢ aif e_q t anil = anil.
    let d1 = Thm::assume(g.clone())?
        .cong_arg(pr.aif.clone())?
        .cong_fn(t.clone())?
        .cong_fn(anil.clone())?
        .trans(pr.if_nil()?.all_elim(t.clone())?.all_elim(anil.clone())?)?;
    // … ⊢ aif e_p (aif e_q t anil) t = anil (the guard fires the outer aif).
    let d2 = d1
        .cong_arg(pr.aif.clone().apply(e_p.clone())?)?
        .cong_fn(t.clone())?
        .trans(
            pr.if_t()?
                .all_elim(e_p.clone())?
                .all_elim(anil)?
                .all_elim(t)?
                .imp_elim(guard)?,
        )?;
    whole_ne.not_elim(d2)?.imp_intro(&g)?.not_intro()
}

/// The evaluated `IMPLIES` shape is truth-preserving: from
/// `Γ ⊢ ¬(e_p = anil) ⟹ ¬(e_q = anil)` conclude
/// `Γ ⊢ ¬(aif e_p (aif e_q t anil) t = anil)` — one boolean split on
/// `e_p = anil` through S1's `if_nil`/`if_t` + `t_ne_nil`.
fn implies_holds(tm: &Terms, e_p: &Term, e_q: &Term, imp: Thm) -> Result<Thm> {
    let pr = tm.pr;
    let t = pr.t.clone();
    let anil = tm.th.nil.clone();
    let aif = pr.aif.clone();
    let inner = aif
        .clone()
        .apply(e_q.clone())?
        .apply(t.clone())?
        .apply(anil.clone())?; // aif e_q t anil
    let g = e_p.clone().equals(anil.clone())?;
    // e_p = anil: the whole form collapses to the else-branch `t`.
    let case_nil = {
        let chain = Thm::assume(g.clone())?
            .cong_arg(aif.clone())?
            .cong_fn(inner.clone())?
            .cong_fn(t.clone())? // aif e_p inner t = aif anil inner t
            .trans(pr.if_nil()?.all_elim(inner.clone())?.all_elim(t.clone())?)?; // = t
        ne_from_eq(tm, chain, pr.t_ne_nil()?)?.imp_intro(&g)?
    };
    // ¬(e_p = anil): fire `imp`, both `aif`s take their true branch.
    let ng = g.clone().not()?;
    let case_t = {
        let ngth = Thm::assume(ng.clone())?;
        let hq = imp.imp_elim(ngth.clone())?; // Γ,{ng} ⊢ ¬(e_q = anil)
        let chain = pr
            .if_t()?
            .all_elim(e_p.clone())?
            .all_elim(inner)?
            .all_elim(t.clone())?
            .imp_elim(ngth)? // aif e_p inner t = inner
            .trans(
                pr.if_t()?
                    .all_elim(e_q.clone())?
                    .all_elim(t.clone())?
                    .all_elim(anil)?
                    .imp_elim(hq)?,
            )?; // = t
        ne_from_eq(tm, chain, pr.t_ne_nil()?)?.imp_intro(&ng)?
    };
    Thm::lem(g)?.or_elim(case_nil, case_t)
}

/// `⊢ f a₁ … aₙ = f b₁ … bₙ` from per-argument equations `⊢ aᵢ = bᵢ`
/// (argument-wise congruence, no full MK_COMB needed).
fn cong_args(f: &Term, avs: &[Term], bvs: &[Term], eqs: &[Thm]) -> Result<Thm> {
    let mut acc: Option<Thm> = None;
    for i in 0..eqs.len() {
        let mut partial = f.clone();
        for b in bvs.iter().take(i) {
            partial = partial.apply(b.clone())?;
        }
        let mut step = eqs[i].clone().cong_arg(partial)?;
        for a in avs.iter().skip(i + 1) {
            step = step.cong_fn(a.clone())?;
        }
        acc = Some(match acc {
            None => step,
            Some(prev) => prev.trans(step)?,
        });
    }
    acc.ok_or_else(|| Error::ConnectiveRule("acl2 cong_args: no arguments".into()))
}

/// The free object variables of an encoded pseudo-term, in
/// first-occurrence order (deduplicated): literal-symbol atoms in
/// non-head, non-`QUOTE`-payload positions. This is the ∀-elimination
/// order the [`Discharge::ModelEq`]/[`Discharge::ModelHolds`] theorems
/// must be quantified in.
pub fn object_vars(tm: &Terms, enc: &Term) -> Result<Vec<Vec<u8>>> {
    fn go(tm: &Terms, t: &Term, acc: &mut Vec<Vec<u8>>) -> Result<()> {
        if *t == tm.th.nil {
            return Ok(());
        }
        if let Some(name) = sym_lit_of(tm, t) {
            if !acc.contains(&name) {
                acc.push(name);
            }
            return Ok(());
        }
        if let Some((f, _)) = t.as_app()
            && *f == tm.th.aint
        {
            return Ok(());
        }
        let Some((h, tail)) = uncons(tm, t) else {
            return Err(Error::ConnectiveRule(format!(
                "acl2 object_vars: not an encoded pseudo-term: {t}"
            )));
        };
        if h == tm.qsym {
            return Ok(()); // quote payloads are opaque constants
        }
        // Application: skip the head symbol, walk the argument list.
        let mut cur = tail;
        while cur != tm.th.nil {
            let Some((a, rest)) = uncons(tm, &cur) else {
                return Err(Error::ConnectiveRule(format!(
                    "acl2 object_vars: improper argument list in {t}"
                )));
            };
            go(tm, &a, acc)?;
            cur = rest;
        }
        Ok(())
    }
    let mut acc = Vec::new();
    go(tm, enc, &mut acc)?;
    Ok(acc)
}

/// The σ-images `σ ⌜V⌝` of an axiom's object variables (the terms its
/// `ModelEq`/`ModelHolds` theorem is `all_elim`'d at).
fn var_images(tm: &Terms, enc: &Term, sg: &Term) -> Result<Vec<Term>> {
    object_vars(tm, enc)?
        .into_iter()
        .map(|n| sg.clone().apply(mk_blob(covalence_types::Bytes::from(n))))
        .collect()
}

/// Discharge one **axiom clause** at `d := pred`: prove
/// `⊢ ∀σ. ¬(eval ⌜ax⌝ σ = anil)` per the row's [`Discharge`] and
/// β-expand to `⊢ pred ⌜ax⌝`. Every arm fails safe: a wrong or
/// unprovable supplied theorem/hook makes a kernel rule error — no
/// theorem is ever minted (this is the API that filled the old
/// "S4+ axiom-discharge gap" SKELETONS entry).
fn discharge_axiom(env: &Acl2Env, pred: &Term, row: &AxiomRow) -> Result<Thm> {
    let tm = &*env.tm;
    match &row.discharge {
        Discharge::Schema => discharge_schema(env, pred, &row.name, &row.enc),
        Discharge::ModelEq(model_eq) => {
            let pr = tm.pr;
            let sg = Term::free("sg", tm.val_ty.clone());
            let chain = eval_open(tm, &row.enc, &sg)?; // ⊢ eval ⌜ax⌝ σ = aequal L R
            let mut inst = model_eq.clone();
            for img in var_images(tm, &row.enc, &sg)? {
                inst = inst.all_elim(img)?;
            }
            // `inst` must now be `⊢ L = R` at exactly the eval images —
            // the trans/not_elim steps below reject any mismatch.
            let r_term = inst.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
            let v_eq_t = inst
                .cong_arg(pr.equal.clone())?
                .cong_fn(r_term.clone())? // aequal L R = aequal R R
                .trans(pr.equal_refl()?.all_elim(r_term)?)?; // = t
            let ne_v = ne_from_eq(tm, v_eq_t, pr.t_ne_nil()?)?;
            let ne = ne_from_eq(tm, chain, ne_v)?;
            ladder::expand_to_pred(ne.all_intro("sg", tm.val_ty.clone())?, &row.enc, pred)
        }
        Discharge::ModelHolds(model_ne) => {
            let sg = Term::free("sg", tm.val_ty.clone());
            let chain = eval_open(tm, &row.enc, &sg)?; // ⊢ eval ⌜ax⌝ σ = V
            let mut inst = model_ne.clone();
            for img in var_images(tm, &row.enc, &sg)? {
                inst = inst.all_elim(img)?;
            }
            // `inst` must now be `⊢ ¬(V = anil)` at the eval image.
            let ne = ne_from_eq(tm, chain, inst)?;
            ladder::expand_to_pred(ne.all_intro("sg", tm.val_ty.clone())?, &row.enc, pred)
        }
        Discharge::Hook(f) => {
            // The hook supplies `⊢ ∀σ. ¬(eval ⌜ax⌝ σ = anil)` outright
            // (for this env's eval); only the β-plumbing happens here.
            ladder::expand_to_pred(f(env, &row.enc)?, &row.enc, pred)
        }
    }
}

/// The built-in [`Discharge::Schema`] arms — the five S3 ground schemas,
/// discharged exactly as at S3.
fn discharge_schema(env: &Acl2Env, pred: &Term, name: &str, enc: &Term) -> Result<Thm> {
    let tm = &*env.tm;
    let pr = tm.pr;
    let anil = tm.th.nil.clone();
    let sg = Term::free("sg", tm.val_ty.clone());
    let var = |n: &[u8]| -> Result<Term> {
        sg.clone()
            .apply(mk_blob(covalence_types::Bytes::from(n.to_vec())))
    };
    let (vx, vy, vz) = (var(b"X")?, var(b"Y")?, var(b"Z")?);
    let aeq = |a: &Term, b: &Term| -> Result<Term> {
        pr.equal.clone().apply(a.clone())?.apply(b.clone())
    };
    // ⊢ ¬(aequal a b = anil) from `⊢ a = b`-shaped reasoning: chain to
    // `aequal b b = t` then `t_ne_nil`.
    let eq_holds = |a: &Term, b: &Term, ng: &Term| -> Result<Thm> {
        pr.equal_holds()?
            .all_elim(a.clone())?
            .all_elim(b.clone())?
            .imp_elim(Thm::assume(ng.clone())?)
    };
    let ne_of_refl = |v: &Term| -> Result<Thm> {
        ne_from_eq(tm, pr.equal_refl()?.all_elim(v.clone())?, pr.t_ne_nil()?)
    };

    let chain = eval_open(tm, enc, &sg)?; // ⊢ eval ⌜ax⌝ σ = V
    let ne_v = match name {
        "equal-refl" => ne_of_refl(&vx)?,
        "equal-symm" => {
            let e_p = aeq(&vx, &vy)?;
            let e_q = aeq(&vy, &vx)?;
            let ng = e_p.clone().equals(anil.clone())?.not()?;
            let eq_xy = eq_holds(&vx, &vy, &ng)?; // {ng} ⊢ vx = vy
            let eq_q = eq_xy
                .cong_arg(pr.equal.clone().apply(vy.clone())?)? // aequal vy vx = aequal vy vy
                .trans(pr.equal_refl()?.all_elim(vy.clone())?)?; // = t
            let imp = ne_from_eq(tm, eq_q, pr.t_ne_nil()?)?.imp_intro(&ng)?;
            implies_holds(tm, &e_p, &e_q, imp)?
        }
        "equal-trans" => {
            let e_p = aeq(&vx, &vy)?;
            let e_yz = aeq(&vy, &vz)?;
            let e_xz = aeq(&vx, &vz)?;
            let t = pr.t.clone();
            let e_q = pr
                .aif
                .clone()
                .apply(e_yz.clone())?
                .apply(
                    pr.aif
                        .clone()
                        .apply(e_xz.clone())?
                        .apply(t.clone())?
                        .apply(anil.clone())?,
                )?
                .apply(t)?;
            let ng1 = e_p.clone().equals(anil.clone())?.not()?;
            let ng2 = e_yz.clone().equals(anil.clone())?.not()?;
            let eq_xy = eq_holds(&vx, &vy, &ng1)?; // {ng1} ⊢ vx = vy
            let eq_yz = eq_holds(&vy, &vz, &ng2)?; // {ng2} ⊢ vy = vz
            let eq_q = eq_xy
                .trans(eq_yz)? // {ng1,ng2} ⊢ vx = vz
                .cong_arg(pr.equal.clone())?
                .cong_fn(vz.clone())? // aequal vx vz = aequal vz vz
                .trans(pr.equal_refl()?.all_elim(vz.clone())?)?; // = t
            let inner = ne_from_eq(tm, eq_q, pr.t_ne_nil()?)?.imp_intro(&ng2)?;
            let outer = implies_holds(tm, &e_yz, &e_xz, inner)?.imp_intro(&ng1)?;
            implies_holds(tm, &e_p, &e_q, outer)?
        }
        "if-true" => {
            let e_p = vx.clone();
            let if_xyz = pr
                .aif
                .clone()
                .apply(vx.clone())?
                .apply(vy.clone())?
                .apply(vz.clone())?;
            let e_q = aeq(&if_xyz, &vy)?;
            let ng = e_p.clone().equals(anil.clone())?.not()?;
            let if_eq = pr
                .if_t()?
                .all_elim(vx.clone())?
                .all_elim(vy.clone())?
                .all_elim(vz.clone())?
                .imp_elim(Thm::assume(ng.clone())?)?; // {ng} ⊢ aif vx vy vz = vy
            let eq_q = if_eq
                .cong_arg(pr.equal.clone())?
                .cong_fn(vy.clone())? // aequal (aif …) vy = aequal vy vy
                .trans(pr.equal_refl()?.all_elim(vy.clone())?)?; // = t
            let imp = ne_from_eq(tm, eq_q, pr.t_ne_nil()?)?.imp_intro(&ng)?;
            implies_holds(tm, &e_p, &e_q, imp)?
        }
        "if-false" => {
            let e_p = aeq(&vx, &anil)?;
            let if_xyz = pr
                .aif
                .clone()
                .apply(vx.clone())?
                .apply(vy.clone())?
                .apply(vz.clone())?;
            let e_q = aeq(&if_xyz, &vz)?;
            let ng = e_p.clone().equals(anil.clone())?.not()?;
            let eq_x = eq_holds(&vx, &anil, &ng)?; // {ng} ⊢ vx = anil
            let if_eq = eq_x
                .cong_arg(pr.aif.clone())?
                .cong_fn(vy.clone())?
                .cong_fn(vz.clone())? // aif vx vy vz = aif anil vy vz
                .trans(pr.if_nil()?.all_elim(vy.clone())?.all_elim(vz.clone())?)?; // = vz
            let eq_q = if_eq
                .cong_arg(pr.equal.clone())?
                .cong_fn(vz.clone())?
                .trans(pr.equal_refl()?.all_elim(vz.clone())?)?; // = t
            let imp = ne_from_eq(tm, eq_q, pr.t_ne_nil()?)?.imp_intro(&ng)?;
            implies_holds(tm, &e_p, &e_q, imp)?
        }
        // prop-k: (IMPLIES X (IMPLIES Y X)) — assume ¬(vx = anil),
        // vacuously discharge the Y antecedent, nest `implies_holds`.
        "prop-k" => {
            let ng_x = vx.clone().equals(anil.clone())?.not()?;
            let ng_y = vy.clone().equals(anil.clone())?.not()?;
            let inner = Thm::assume(ng_x.clone())?.imp_intro(&ng_y)?; // ng_y ⟹ ng_x (K)
            let inner_q = {
                let t = pr.t.clone();
                pr.aif
                    .clone()
                    .apply(vy.clone())?
                    .apply(
                        pr.aif
                            .clone()
                            .apply(vx.clone())?
                            .apply(t.clone())?
                            .apply(anil.clone())?,
                    )?
                    .apply(t)?
            };
            let mid = implies_holds(tm, &vy, &vx, inner)?.imp_intro(&ng_x)?;
            implies_holds(tm, &vx, &inner_q, mid)?
        }
        // prop-s: (IMPLIES (IMPLIES X (IMPLIES Y Z))
        //                  (IMPLIES (IMPLIES X Y) (IMPLIES X Z))) —
        // two `fire_implies` under the assumed antecedents, then nest
        // `implies_holds` back up.
        "prop-s" => {
            let t = pr.t.clone();
            let ifml = |p: &Term, q: &Term| -> Result<Term> {
                pr.aif
                    .clone()
                    .apply(p.clone())?
                    .apply(
                        pr.aif
                            .clone()
                            .apply(q.clone())?
                            .apply(t.clone())?
                            .apply(anil.clone())?,
                    )?
                    .apply(t.clone())
            };
            let yz = ifml(&vy, &vz)?; // E[(IMPLIES Y Z)]
            let a_t = ifml(&vx, &yz)?; // E[(IMPLIES X (IMPLIES Y Z))]
            let b_t = ifml(&vx, &vy)?; // E[(IMPLIES X Y)]
            let c_t = ifml(&vx, &vz)?; // E[(IMPLIES X Z)]
            let ng = |e: &Term| -> Result<Term> { e.clone().equals(anil.clone())?.not() };
            let (ng_a, ng_b, ng_x) = (ng(&a_t)?, ng(&b_t)?, ng(&vx)?);
            let ne_y = fire_implies(
                tm,
                Thm::assume(ng_b.clone())?,
                &vx,
                &vy,
                Thm::assume(ng_x.clone())?,
            )?;
            let ne_yz = fire_implies(
                tm,
                Thm::assume(ng_a.clone())?,
                &vx,
                &yz,
                Thm::assume(ng_x.clone())?,
            )?;
            let ne_z = fire_implies(tm, ne_yz, &vy, &vz, ne_y)?; // {ng_a, ng_b, ng_x} ⊢ ¬(vz = anil)
            let step1 = implies_holds(tm, &vx, &vz, ne_z.imp_intro(&ng_x)?)?; // ¬(C = anil)
            let step2 = implies_holds(tm, &b_t, &c_t, step1.imp_intro(&ng_b)?)?;
            let bc_t = ifml(&b_t, &c_t)?; // E[(IMPLIES (IMPLIES X Y) (IMPLIES X Z))]
            implies_holds(tm, &a_t, &bc_t, step2.imp_intro(&ng_a)?)?
        }
        other => {
            return Err(Error::ConnectiveRule(format!(
                "acl2 soundness: no discharge for axiom schema `{other}` \
                 (the five S3 ground schemas + S6's prop-k/prop-s are known)"
            )));
        }
    };
    let ne = ne_from_eq(tm, chain, ne_v)?; // ⊢ ¬(eval ⌜ax⌝ σ = anil)
    ladder::expand_to_pred(ne.all_intro("sg", tm.val_ty.clone())?, enc, pred)
}

/// Discharge the **MP clause** at `d := pred`:
/// `⊢ ∀p q. pred ⌜(IMPLIES p q)⌝ ⟹ pred p ⟹ pred q` — unfold the
/// `IMPLIES` macro shape through `eval_app_if`, then `if_nil`/`if_t`.
fn discharge_mp(env: &Acl2Env, pred: &Term) -> Result<Thm> {
    let tm = &*env.tm;
    let a = tm.th.ty.clone();
    let p = Term::free("p", a.clone());
    let q = Term::free("q", a.clone());
    let imp_enc = tm.mk_implies(&p, &q)?;

    let d_imp_t = pred.clone().apply(imp_enc.clone())?;
    let d_p_t = pred.clone().apply(p.clone())?;
    let (br_imp, _) = ladder::br(pred, imp_enc.clone())?;
    let (br_p, _) = ladder::br(pred, p.clone())?;
    let h_imp = br_imp.eq_mp(Thm::assume(d_imp_t.clone())?)?; // {d imp} ⊢ ∀σ. ¬(eval imp σ = anil)
    let h_p = br_p.eq_mp(Thm::assume(d_p_t.clone())?)?; // {d p} ⊢ ∀σ. ¬(eval p σ = anil)

    let sg = Term::free("sg", tm.val_ty.clone());
    let hi = h_imp.all_elim(sg.clone())?;
    let hp = h_p.all_elim(sg.clone())?; // ¬(eval p σ = anil)
    let chain = eval_open(tm, &imp_enc, &sg)?; // eval imp σ = aif Ep (aif Eq t anil) t
    let hi2 = ne_transport(tm, &chain, hi)?; // ¬(aif Ep (aif Eq t anil) t = anil)

    let ep = tm.eval.clone().apply(p.clone())?.apply(sg.clone())?;
    let eq_ = tm.eval.clone().apply(q.clone())?.apply(sg.clone())?;
    let nf_q = fire_implies(tm, hi2, &ep, &eq_, hp)? // ¬(eval q σ = anil)
        .all_intro("sg", tm.val_ty.clone())?;
    ladder::expand_to_pred(nf_q, &q, pred)?
        .imp_intro(&d_p_t)?
        .imp_intro(&d_imp_t)?
        .all_intro("q", a.clone())?
        .all_intro("p", a)
}

/// Discharge the **INST clause** at `d := pred`:
/// `⊢ ∀s f. pred f ⟹ pred (subst f s)` — **this is where S2's
/// `subst_sema` fires**: the internalized ∀σ absorbs the composed
/// valuation `λv. eval (s v) σ`.
fn discharge_inst(env: &Acl2Env, pred: &Term) -> Result<Thm> {
    let tm = &*env.tm;
    let a = tm.th.ty.clone();
    let s = Term::free("s", tm.val_ty.clone());
    let f = Term::free("f", a.clone());
    let sub = tm.subst.clone().apply(f.clone())?.apply(s.clone())?;

    let d_f_t = pred.clone().apply(f.clone())?;
    let (br_f, _) = ladder::br(pred, f.clone())?;
    let h_f = br_f.eq_mp(Thm::assume(d_f_t.clone())?)?; // {d f} ⊢ ∀σ. ¬(eval f σ = anil)

    let sg = Term::free("sg", tm.val_ty.clone());
    let sema = beta_reduce(tm.subst_sema()?.all_elim(f.clone())?)?
        .all_elim(s.clone())?
        .all_elim(sg.clone())?;
    let (c1, _) = sema.conjuncts()?; // ⊢ eval (subst f s) σ = eval f σ′
    // Read the composed valuation σ′ = λv. eval (s v) σ off the RHS.
    let sp = c1
        .concl()
        .as_eq()
        .ok_or(Error::NotAnEquation)?
        .1
        .as_app()
        .ok_or(Error::NotAnEquation)?
        .1
        .clone();
    let hf_sp = h_f.all_elim(sp)?; // {d f} ⊢ ¬(eval f σ′ = anil)
    let nf = ne_from_eq(tm, c1, hf_sp)? // ¬(eval (subst f s) σ = anil)
        .all_intro("sg", tm.val_ty.clone())?;
    ladder::expand_to_pred(nf, &sub, pred)?
        .imp_intro(&d_f_t)?
        .all_intro("f", a)?
        .all_intro("s", tm.val_ty.clone())
}

/// `λn:bytes. cond (n = v) val (σ n)` — the single-point *semantic*
/// valuation update of the IND soundness discharge (design §9).
fn upd_val(tm: &Terms, v: &Term, val: &Term, sg: &Term) -> Result<Term> {
    let n = Term::free("__n", Type::bytes());
    let body = cond(tm.th.ty.clone())
        .apply(n.clone().equals(v.clone())?)?
        .apply(val.clone())?
        .apply(sg.clone().apply(n)?)?;
    Ok(Term::abs(Type::bytes(), subst::close(&body, "__n")))
}

/// Discharge the **IND clause** at `d := pred` (design §9 — the crown
/// proof of S6): carrier induction at the motive
/// `M := λa. ∀σ. ¬(eval f (upd a σ) = anil)` (free `f`, `v` parameters),
/// with the IH transport routed through **`subst_sema`** — the clause's
/// `subst f (s_upd v ⌜(CAR v)⌝)` antecedent evaluates at `σ′ := upd (acons h t) σ`
/// to `eval f σc` with `σc = λn. eval (s_upd … n) σ′`, and a pointwise
/// `lem`-split + `cat::fun_ext` identifies `σc = upd h σ` so the motive
/// IH fires. Leaf cases fire the base premise (`consp_atom`/`consp_nil`
/// compute the guard to `anil`); the close identifies `upd (σ v) σ = σ`.
fn discharge_ind(env: &Acl2Env, pred: &Term) -> Result<Thm> {
    let tm = &*env.tm;
    let pr = tm.pr;
    let a = tm.th.ty.clone();
    let vt = tm.val_ty.clone();
    let anil = tm.th.nil.clone();
    let tconst = pr.t.clone();

    let f = Term::free("f", a.clone());
    let v = Term::free("v", Type::bytes());
    let (_consp_v, base_enc, step_enc) = ind_encs(tm, &f, &v)?;

    // The premise hypotheses (pred-applied), opened to ∀σ denotations.
    let pb_t = pred.clone().apply(base_enc.clone())?;
    let ps_t = pred.clone().apply(step_enc.clone())?;
    let (br_b, _) = ladder::br(pred, base_enc.clone())?;
    let (br_s, _) = ladder::br(pred, step_enc.clone())?;
    let hb = br_b.eq_mp(Thm::assume(pb_t.clone())?)?; // {pb} ⊢ ∀σ. ¬(eval ⌜base⌝ σ = anil)
    let hs = br_s.eq_mp(Thm::assume(ps_t.clone())?)?; // {ps} ⊢ ∀σ. ¬(eval ⌜step⌝ σ = anil)

    let sg = Term::free("sg", vt.clone());
    let sg_at = |x: &Term| -> Result<Term> { sg.clone().apply(x.clone()) };
    let eqt_v = Thm::refl(v.clone())?.eqt_intro()?; // ⊢ (v = v) = T

    // M := λa'. ∀σ. ¬(eval f (upd a' σ) = anil)  (f, v free params —
    // the aappend-motive precedent).
    let motive = {
        let mv = Term::free("__im", a.clone());
        let body = tm
            .eval
            .clone()
            .apply(f.clone())?
            .apply(upd_val(tm, &v, &mv, &sg)?)?
            .equals(anil.clone())?
            .not()?
            .forall("sg", vt.clone())?;
        Term::abs(a.clone(), subst::close(&body, "__im"))
    };

    // Fire the (single) `σ′ v` redex in a chain's RHS down to `val`:
    // β-normalise, decide the `v = v` guard by reflexivity, collapse.
    let fire_upd = |chain: Thm, val: &Term| -> Result<Thm> {
        let ct = cond_true(&a, val, &sg_at(&v)?)?;
        chain
            .rhs_conv(|u| Ok(beta_nf(u.clone())))?
            .rhs_conv(|u| u.rw_all(&eqt_v))?
            .rhs_conv(|u| u.rw_all(&ct))
    };

    // ---- leaf cases (atom / nil): the base premise fires -------------
    let leaf_case = |val: &Term, consp_leaf: Thm| -> Result<Thm> {
        let spr = upd_val(tm, &v, val, &sg)?; // σ′ := upd val σ
        let hb_at = hb.clone().all_elim(spr.clone())?;
        let chain = fire_upd(eval_open(tm, &base_enc, &spr)?, val)?
            .rhs_conv(|u| u.rw_all(&consp_leaf))? // aconsp val → anil
            .rhs_conv(|u| u.rw_all(&pr.equal_refl()?.all_elim(anil.clone())?))?; // aequal anil anil → t
        let whole = ne_transport(tm, &chain, hb_at)?;
        let e_f = tm.eval.clone().apply(f.clone())?.apply(spr)?;
        let ne_f = fire_implies(tm, whole, &tconst, &e_f, pr.t_ne_nil()?)?;
        beta_expand(&motive, val.clone(), ne_f.all_intro("sg", vt.clone())?)
    };
    let case_atom = {
        let b = Term::free("b", acl2_payload());
        let atom_b = tm.th.atom.clone().apply(b.clone())?;
        leaf_case(&atom_b, pr.consp_atom()?.all_elim(b)?)?
    };
    let case_nil = leaf_case(&anil.clone(), pr.consp_nil()?)?;

    // ---- cons case: both IHs transport through subst_sema -------------
    let sema_all = tm.subst_sema()?;
    let case_cons = {
        let h = Term::free("h", a.clone());
        let t_var = Term::free("t", a.clone());
        let acons_ht = tm.th.cons.clone().apply(h.clone())?.apply(t_var.clone())?;
        let spr = upd_val(tm, &v, &acons_ht, &sg)?; // σ′ := upd (acons h t) σ
        let ph = motive.clone().apply(h.clone())?;
        let pt = motive.clone().apply(t_var.clone())?;

        // From the β-applied motive IH `ihyp` at `val` (`h` or `t`) and
        // the clause substitution `s_e := s_upd v ⌜e⌝` (`e` = (CAR v) /
        // (CDR v), projection law `proj_eq : car|cdr (acons h t) = val`),
        // conclude `¬(eval (subst f s_e) σ′ = anil)`.
        let ih_transport = |ihyp: &Term, val: &Term, e_enc: &Term, proj_eq: Thm| -> Result<Thm> {
            let s_e = sigma_upd(tm, &v, e_enc)?;
            let sema = beta_reduce(sema_all.clone().all_elim(f.clone())?)?
                .all_elim(s_e.clone())?
                .all_elim(spr.clone())?;
            let (c1, _) = sema.conjuncts()?; // ⊢ eval (subst f s_e) σ′ = eval f σc
            let sc = c1
                .concl()
                .as_eq()
                .ok_or(Error::NotAnEquation)?
                .1
                .as_app()
                .ok_or(Error::NotAnEquation)?
                .1
                .clone(); // σc = λn. eval (s_e n) σ′
            let updv = upd_val(tm, &v, val, &sg)?;
            // Pointwise ⊢ σc n = updv n at a fresh free n, by lem on n = v.
            let n = Term::free("__pn", Type::bytes());
            let bl = Thm::beta_conv(sc.clone().apply(n.clone())?)?; // σc n = eval (s_e n) σ′
            let rb = Thm::beta_conv(updv.clone().apply(n.clone())?)?; // updv n = cond (n=v) val (σ n)
            let inner = Thm::beta_conv(s_e.clone().apply(n.clone())?)?; // s_e n = cond (n=v) ⌜e⌝ (asym n)
            let asym_n = tm.th.asym_at(&n)?;
            let g = n.clone().equals(v.clone())?;
            let case_t = {
                let ge = Thm::assume(g.clone())?.eqt_intro()?;
                let inner2 = inner
                    .clone()
                    .rhs_conv(|u| u.rw_all(&ge))?
                    .rhs_conv(|u| u.rw_all(&cond_true(&a, e_enc, &asym_n)?))?; // {g} ⊢ s_e n = ⌜e⌝
                let e1 = inner2.cong_arg(tm.eval.clone())?.cong_fn(spr.clone())?;
                let e2 = fire_upd(eval_open(tm, e_enc, &spr)?, &acons_ht)?
                    .rhs_conv(|u| u.rw_all(&proj_eq))?; // eval ⌜e⌝ σ′ = val
                let lhs_chain = e1.trans(e2)?; // {g} ⊢ eval (s_e n) σ′ = val
                let rb2 = rb
                    .clone()
                    .rhs_conv(|u| u.rw_all(&ge))?
                    .rhs_conv(|u| u.rw_all(&cond_true(&a, val, &sg_at(&n)?)?))?; // {g} ⊢ updv n = val
                bl.clone()
                    .trans(lhs_chain)?
                    .trans(rb2.sym()?)?
                    .imp_intro(&g)?
            };
            let case_f = {
                let ng = g.clone().not()?;
                let gf = eqf_intro(Thm::assume(ng.clone())?)?;
                let inner2 = inner
                    .rhs_conv(|u| u.rw_all(&gf))?
                    .rhs_conv(|u| u.rw_all(&cond_false(&a, e_enc, &asym_n)?))?; // {¬g} ⊢ s_e n = asym n
                let e1 = inner2.cong_arg(tm.eval.clone())?.cong_fn(spr.clone())?;
                let e2 = tm
                    .eval_var()?
                    .all_elim(n.clone())?
                    .all_elim(spr.clone())?
                    .rhs_conv(|u| Ok(beta_nf(u.clone())))?
                    .rhs_conv(|u| u.rw_all(&gf))?
                    .rhs_conv(|u| u.rw_all(&cond_false(&a, &acons_ht, &sg_at(&n)?)?))?; // eval (asym n) σ′ = σ n
                let lhs_chain = e1.trans(e2)?; // {¬g} ⊢ eval (s_e n) σ′ = σ n
                let rb2 = rb
                    .rhs_conv(|u| u.rw_all(&gf))?
                    .rhs_conv(|u| u.rw_all(&cond_false(&a, val, &sg_at(&n)?)?))?; // {¬g} ⊢ updv n = σ n
                bl.trans(lhs_chain)?.trans(rb2.sym()?)?.imp_intro(&ng)?
            };
            let pw = Thm::lem(g)?.or_elim(case_t, case_f)?; // ⊢ σc n = updv n
            let veq = fun_ext(pw, "__pn", &Type::bytes())?; // ⊢ σc = updv
            let step_eq = veq.cong_arg(tm.eval.clone().apply(f.clone())?)?; // eval f σc = eval f updv
            let ih_inst = beta_reduce(Thm::assume(ihyp.clone())?)?.all_elim(sg.clone())?; // {ihyp} ⊢ ¬(eval f updv = anil)
            let ne_upd = ne_from_eq(tm, step_eq, ih_inst)?; // ¬(eval f σc = anil)
            ne_from_eq(tm, c1, ne_upd) // ¬(eval (subst f s_e) σ′ = anil)
        };

        let asym_v = tm.th.asym_at(&v)?;
        let car_v = tm.app(b"CAR", &[asym_v.clone()])?;
        let cdr_v = tm.app(b"CDR", &[asym_v])?;
        let ne_car = ih_transport(&ph, &h, &car_v, tm.th.cs.proj_scons(false, &h, &t_var)?)?;
        let ne_cdr = ih_transport(&pt, &t_var, &cdr_v, tm.th.cs.proj_scons(true, &h, &t_var)?)?;

        // The step premise at σ′, its image fired three levels deep.
        let hs_at = hs.clone().all_elim(spr.clone())?;
        let consp_ht = pr
            .consp_cons()?
            .all_elim(h.clone())?
            .all_elim(t_var.clone())?;
        let chain = fire_upd(eval_open(tm, &step_enc, &spr)?, &acons_ht)?
            .rhs_conv(|u| u.rw_all(&consp_ht))?; // aconsp (acons h t) → t
        let whole = ne_transport(tm, &chain, hs_at)?;
        let sub_at = |e_enc: &Term| -> Result<Term> {
            tm.eval
                .clone()
                .apply(
                    tm.subst
                        .clone()
                        .apply(f.clone())?
                        .apply(sigma_upd(tm, &v, e_enc)?)?,
                )?
                .apply(spr.clone())
        };
        let e_car = sub_at(&car_v)?;
        let e_cdr = sub_at(&cdr_v)?;
        let e_f = tm.eval.clone().apply(f.clone())?.apply(spr.clone())?;
        let lvl = |p: &Term, q: &Term| -> Result<Term> {
            pr.aif
                .clone()
                .apply(p.clone())?
                .apply(
                    pr.aif
                        .clone()
                        .apply(q.clone())?
                        .apply(tconst.clone())?
                        .apply(anil.clone())?,
                )?
                .apply(tconst.clone())
        };
        let s2 = lvl(&e_cdr, &e_f)?; // E[(IMPLIES cdr-IH φ)]
        let s1 = lvl(&e_car, &s2)?; // E[(IMPLIES car-IH …)]
        let f1 = fire_implies(tm, whole, &tconst, &s1, pr.t_ne_nil()?)?;
        let f2 = fire_implies(tm, f1, &e_car, &s2, ne_car)?;
        let f3 = fire_implies(tm, f2, &e_cdr, &e_f, ne_cdr)?; // ¬(eval f σ′ = anil)
        beta_expand(&motive, acons_ht, f3.all_intro("sg", vt.clone())?)?
            .imp_intro(&pt)?
            .imp_intro(&ph)?
    };

    // ---- induct + close ------------------------------------------------
    let by = tm
        .th
        .induct(&motive, vec![case_atom, case_nil, case_cons])?; // {pb, ps} ⊢ ∀a. M a
    let sg_v = sg_at(&v)?;
    let m_inst = beta_reduce(by.all_elim(sg_v.clone())?)?.all_elim(sg.clone())?; // ¬(eval f (upd (σ v) σ) = anil)
    let updv = upd_val(tm, &v, &sg_v, &sg)?;
    // Pointwise ⊢ upd (σ v) σ n = σ n, hence upd (σ v) σ = σ.
    let n = Term::free("__pn", Type::bytes());
    let rbn = Thm::beta_conv(updv.clone().apply(n.clone())?)?;
    let g = n.clone().equals(v.clone())?;
    let case_t = {
        let ge = Thm::assume(g.clone())?.eqt_intro()?;
        let chain = rbn
            .clone()
            .rhs_conv(|u| u.rw_all(&ge))?
            .rhs_conv(|u| u.rw_all(&cond_true(&a, &sg_v, &sg_at(&n)?)?))?; // {g} ⊢ updv n = σ v
        let n_eq_v = Thm::assume(g.clone())?.cong_arg(sg.clone())?; // {g} ⊢ σ n = σ v
        chain.trans(n_eq_v.sym()?)?.imp_intro(&g)?
    };
    let case_f = {
        let ng = g.clone().not()?;
        let gf = eqf_intro(Thm::assume(ng.clone())?)?;
        rbn.rhs_conv(|u| u.rw_all(&gf))?
            .rhs_conv(|u| u.rw_all(&cond_false(&a, &sg_v, &sg_at(&n)?)?))?
            .imp_intro(&ng)?
    };
    let pw = Thm::lem(g)?.or_elim(case_t, case_f)?; // ⊢ updv n = σ n
    let veq = fun_ext(pw, "__pn", &Type::bytes())?; // ⊢ updv = σ
    let eqf_eval = veq.cong_arg(tm.eval.clone().apply(f.clone())?)?; // eval f updv = eval f σ
    let ne_final = ne_transport(tm, &eqf_eval, m_inst)?; // {pb, ps} ⊢ ¬(eval f σ = anil)
    ladder::expand_to_pred(ne_final.all_intro("sg", vt)?, &f, pred)?
        .imp_intro(&ps_t)?
        .imp_intro(&pb_t)?
        .all_intro("v", Type::bytes())?
        .all_intro("f", a)
}

/// Discharge the **congruence clause** for table row `k` at `d := pred`:
/// per-argument `equal_holds` turns the premises into HOL equations,
/// argument-wise congruence + `equal_refl` close the conclusion.
fn discharge_cong(env: &Acl2Env, pred: &Term, k: usize) -> Result<Thm> {
    let tm = &*env.tm;
    let pr = tm.pr;
    let a = tm.th.ty.clone();
    let row = &env.rows[k];
    let xn: Vec<String> = (1..=row.arity).map(|i| format!("x{i}")).collect();
    let yn: Vec<String> = (1..=row.arity).map(|i| format!("y{i}")).collect();
    let xs: Vec<Term> = xn
        .iter()
        .map(|n| Term::free(n.as_str(), a.clone()))
        .collect();
    let ys: Vec<Term> = yn
        .iter()
        .map(|n| Term::free(n.as_str(), a.clone()))
        .collect();
    let f_xs = tm.app(row.sym.as_bytes(), &xs)?;
    let f_ys = tm.app(row.sym.as_bytes(), &ys)?;
    let concl_enc = tm.mk_equal(&f_xs, &f_ys)?;

    let sg = Term::free("sg", tm.val_ty.clone());
    let ev_at = |x: &Term| -> Result<Term> { tm.eval.clone().apply(x.clone())?.apply(sg.clone()) };
    let mut hyp_terms = Vec::with_capacity(row.arity);
    let mut arg_eqs = Vec::with_capacity(row.arity);
    for (x, y) in xs.iter().zip(&ys) {
        let enc_i = tm.mk_equal(x, y)?;
        let d_t = pred.clone().apply(enc_i.clone())?;
        let (br_i, _) = ladder::br(pred, enc_i.clone())?;
        let h_i = br_i
            .eq_mp(Thm::assume(d_t.clone())?)?
            .all_elim(sg.clone())?; // ¬(eval ⌜(EQUAL xᵢ yᵢ)⌝ σ = anil)
        let chain_i = eval_open(tm, &enc_i, &sg)?; // = aequal (eval xᵢ σ) (eval yᵢ σ)
        let ne_i = ne_transport(tm, &chain_i, h_i)?;
        let eq_i = pr
            .equal_holds()?
            .all_elim(ev_at(x)?)?
            .all_elim(ev_at(y)?)?
            .imp_elim(ne_i)?; // {d ⌜(EQUAL xᵢ yᵢ)⌝} ⊢ eval xᵢ σ = eval yᵢ σ
        hyp_terms.push(d_t);
        arg_eqs.push(eq_i);
    }
    let exs: Vec<Term> = xs.iter().map(ev_at).collect::<Result<_>>()?;
    let eys: Vec<Term> = ys.iter().map(ev_at).collect::<Result<_>>()?;
    let lr = cong_args(&row.model, &exs, &eys, &arg_eqs)?; // ⊢ L = R
    let mut r_term = row.model.clone();
    for e in &eys {
        r_term = r_term.apply(e.clone())?;
    }
    let v_eq_t = lr
        .cong_arg(pr.equal.clone())?
        .cong_fn(r_term.clone())? // aequal L R = aequal R R
        .trans(pr.equal_refl()?.all_elim(r_term)?)?; // = t
    let ne_v = ne_from_eq(tm, v_eq_t, pr.t_ne_nil()?)?;
    let chain_c = eval_open(tm, &concl_enc, &sg)?; // eval ⌜concl⌝ σ = aequal L R
    let nf = ne_from_eq(tm, chain_c, ne_v)?.all_intro("sg", tm.val_ty.clone())?;
    let mut th = ladder::expand_to_pred(nf, &concl_enc, pred)?;
    for d_t in hyp_terms.iter().rev() {
        th = th.imp_intro(d_t)?;
    }
    for (xname, yname) in xn.iter().zip(&yn).rev() {
        th = th
            .all_intro(yname.as_str(), a.clone())?
            .all_intro(xname.as_str(), a.clone())?;
    }
    Ok(th)
}

/// Discharge the **CongImpl clause** for table row `k` at `d := pred`
/// (design §7.4): the object-level curried implication is proved by
/// nesting [`implies_holds`] around the [`discharge_cong`] core —
/// per-argument `equal_holds` under the assumed `¬(E[(EQUAL xᵢ yᵢ)] = anil)`
/// guards, argument-wise congruence, `equal_refl` + `t_ne_nil`.
fn discharge_cong_impl(env: &Acl2Env, pred: &Term, k: usize) -> Result<Thm> {
    let tm = &*env.tm;
    let pr = tm.pr;
    let a = tm.th.ty.clone();
    let anil = tm.th.nil.clone();
    let t = pr.t.clone();
    let row = &env.rows[k];
    let xn: Vec<String> = (1..=row.arity).map(|i| format!("x{i}")).collect();
    let yn: Vec<String> = (1..=row.arity).map(|i| format!("y{i}")).collect();
    let xs: Vec<Term> = xn
        .iter()
        .map(|n| Term::free(n.as_str(), a.clone()))
        .collect();
    let ys: Vec<Term> = yn
        .iter()
        .map(|n| Term::free(n.as_str(), a.clone()))
        .collect();
    let enc = cong_impl_enc(tm, row, &xs, &ys)?;

    let sg = Term::free("sg", tm.val_ty.clone());
    let ev_at = |x: &Term| -> Result<Term> { tm.eval.clone().apply(x.clone())?.apply(sg.clone()) };
    // The per-level antecedent images e_i = aequal (eval xᵢ σ) (eval yᵢ σ)
    // and their `= anil` negation guards.
    let mut e_terms = Vec::with_capacity(row.arity);
    let mut ng_terms = Vec::with_capacity(row.arity);
    let mut arg_eqs = Vec::with_capacity(row.arity);
    for (x, y) in xs.iter().zip(&ys) {
        let e_i = pr.equal.clone().apply(ev_at(x)?)?.apply(ev_at(y)?)?;
        let ng_i = e_i.clone().equals(anil.clone())?.not()?;
        let eq_i = pr
            .equal_holds()?
            .all_elim(ev_at(x)?)?
            .all_elim(ev_at(y)?)?
            .imp_elim(Thm::assume(ng_i.clone())?)?; // {ng_i} ⊢ eval xᵢ σ = eval yᵢ σ
        e_terms.push(e_i);
        ng_terms.push(ng_i);
        arg_eqs.push(eq_i);
    }
    let exs: Vec<Term> = xs.iter().map(ev_at).collect::<Result<_>>()?;
    let eys: Vec<Term> = ys.iter().map(ev_at).collect::<Result<_>>()?;
    let lr = cong_args(&row.model, &exs, &eys, &arg_eqs)?; // {ng⃗} ⊢ L = R
    let mut r_term = row.model.clone();
    for e in &eys {
        r_term = r_term.apply(e.clone())?;
    }
    let mut l_term = row.model.clone();
    for e in &exs {
        l_term = l_term.apply(e.clone())?;
    }
    let v_eq_t = lr
        .cong_arg(pr.equal.clone())?
        .cong_fn(r_term.clone())? // aequal L R = aequal R R
        .trans(pr.equal_refl()?.all_elim(r_term.clone())?)?; // = t
    let mut th = ne_from_eq(tm, v_eq_t, pr.t_ne_nil()?)?; // {ng⃗} ⊢ ¬(aequal L R = anil)
    // Nest the implication levels back up, innermost first.
    let mut cur = pr.equal.clone().apply(l_term)?.apply(r_term)?; // aequal L R
    for i in (0..row.arity).rev() {
        th = implies_holds(tm, &e_terms[i], &cur, th.imp_intro(&ng_terms[i])?)?;
        cur = pr
            .aif
            .clone()
            .apply(e_terms[i].clone())?
            .apply(
                pr.aif
                    .clone()
                    .apply(cur)?
                    .apply(t.clone())?
                    .apply(anil.clone())?,
            )?
            .apply(t.clone())?;
    }
    let chain = eval_open(tm, &enc, &sg)?; // ⊢ eval ⌜enc⌝ σ = <the nested image>
    let nf = ne_from_eq(tm, chain, th)?.all_intro("sg", tm.val_ty.clone())?;
    let mut out = ladder::expand_to_pred(nf, &enc, pred)?;
    for (xname, yname) in xn.iter().zip(&yn).rev() {
        out = out
            .all_intro(yname.as_str(), a.clone())?
            .all_intro(xname.as_str(), a.clone())?;
    }
    Ok(out)
}

/// Discharge the **computation clause** for table row `k` at `d := pred`:
/// both sides of the quote-homomorphism evaluate to the *same* model
/// application, so `equal_refl` + `t_ne_nil` close it.
fn discharge_comp(env: &Acl2Env, pred: &Term, k: usize) -> Result<Thm> {
    let tm = &*env.tm;
    let pr = tm.pr;
    let a = tm.th.ty.clone();
    let row = &env.rows[k];
    let xn: Vec<String> = (1..=row.arity).map(|i| format!("x{i}")).collect();
    let xs: Vec<Term> = xn
        .iter()
        .map(|n| Term::free(n.as_str(), a.clone()))
        .collect();
    let quoted: Vec<Term> = xs.iter().map(|x| tm.quote(x)).collect::<Result<_>>()?;
    let lhs = tm.app(row.sym.as_bytes(), &quoted)?;
    let mut model = row.model.clone();
    for x in &xs {
        model = model.apply(x.clone())?;
    }
    let rhs = tm.quote(&model)?;
    let enc = tm.mk_equal(&lhs, &rhs)?;

    let sg = Term::free("sg", tm.val_ty.clone());
    let chain = eval_open(tm, &enc, &sg)?; // = aequal (f_model x⃗) (f_model x⃗)
    let ne_v = ne_from_eq(tm, pr.equal_refl()?.all_elim(model)?, pr.t_ne_nil()?)?;
    let nf = ne_from_eq(tm, chain, ne_v)?.all_intro("sg", tm.val_ty.clone())?;
    let mut th = ladder::expand_to_pred(nf, &enc, pred)?;
    for xname in xn.iter().rev() {
        th = th.all_intro(xname.as_str(), a.clone())?;
    }
    Ok(th)
}

/// Discharge the **defining-equation clause** for user row `j` at
/// `d := pred` (S4+S6 design §5.1) — uniform, no per-row proof: the
/// [`eval_open`] image of `⌜(EQUAL (f X⃗) body)⌝` at a free σ is
/// `aequal (f_model σX⃗) B` with `B` the compositional model image of
/// the body (`defun::model_image` — the §3.1 single source of truth),
/// and the row's **proved** `def_eq_model` eliminated at the σ-images is
/// exactly `⊢ f_model σX⃗ = B`. Any drift between the two chains is a
/// kernel error here, never an unsound theorem.
fn discharge_def(env: &Acl2Env, pred: &Term, j: usize) -> Result<Thm> {
    let tm = &*env.tm;
    let pr = tm.pr;
    let u = &env.users[j];
    let sg = Term::free("sg", tm.val_ty.clone());
    let chain = eval_open(tm, &u.def_enc, &sg)?; // ⊢ eval ⌜enc⌝ σ = aequal (f σX⃗) B
    let mut inst = u.def_eq_model.clone();
    for f in &u.formals {
        let img = sg
            .clone()
            .apply(mk_blob(covalence_types::Bytes::from(f.as_bytes().to_vec())))?;
        inst = inst.all_elim(img)?;
    }
    // inst: ⊢ f_model σX⃗ = B (syntactic agreement with chain's RHS).
    let b_term = inst.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
    let v_eq_t = inst
        .cong_arg(pr.equal.clone())?
        .cong_fn(b_term.clone())? // aequal (f σX⃗) B = aequal B B
        .trans(pr.equal_refl()?.all_elim(b_term)?)?; // = t
    let ne_v = ne_from_eq(tm, v_eq_t, pr.t_ne_nil()?)?;
    let ne = ne_from_eq(tm, chain, ne_v)?; // ⊢ ¬(eval ⌜enc⌝ σ = anil)
    ladder::expand_to_pred(ne.all_intro("sg", tm.val_ty.clone())?, &u.def_enc, pred)
}

/// Discharge every clause of [`acl2_rule_set`] at `d := pred`, in clause
/// order (the invariant that makes `rule_induction`'s `imp_elim` check).
fn discharge_closed(env: &Acl2Env, pred: &Term) -> Result<Vec<Thm>> {
    let mut proofs = Vec::with_capacity(env.n_clauses());
    for row in &env.axioms {
        proofs.push(discharge_axiom(env, pred, row)?);
    }
    proofs.push(discharge_mp(env, pred)?);
    proofs.push(discharge_inst(env, pred)?);
    if env.s6 {
        proofs.push(discharge_ind(env, pred)?);
    }
    for k in 0..env.rows.len() {
        proofs.push(discharge_cong(env, pred, k)?);
    }
    for k in 0..env.rows.len() {
        proofs.push(discharge_comp(env, pred, k)?);
    }
    if env.s6 {
        for k in 0..env.rows.len() {
            proofs.push(discharge_cong_impl(env, pred, k)?);
        }
    }
    for j in 0..env.users.len() {
        proofs.push(discharge_def(env, pred, j)?);
    }
    Ok(proofs)
}

/// **THE SOUNDNESS METATHEOREM** (design §6.4):
///
/// ```text
/// ⊢ ∀A:A. Derivable_ACL2 A ⟹ (∀σ. ¬(eval A σ = anil))
/// ```
///
/// by [`crate::metalogic::rule_induction`] at
/// `pred := λφ. ∀σ. ¬(eval φ σ = anil)`, every clause of the env's rule
/// set discharged ([`discharge_closed`]). Hypothesis-free; every step is
/// an existing kernel rule — a wrong clause proof *fails*, it never
/// fabricates an induction.
pub fn soundness(env: &Acl2Env) -> Result<Thm> {
    let tm = &*env.tm;
    let a = tm.th.ty.clone();
    let pred = sound_pred(tm)?;
    let proofs = discharge_closed(env, &pred)?;
    let av = Term::free("A", a.clone());
    let deriv_a = derivable(env, &av)?;
    let raw = crate::metalogic::rule_induction(&pred, proofs, &deriv_a, "A", a.clone())?;
    // Clean the β-redex `pred A` in the consequent to its ∀σ-form.
    let assumed = Thm::assume(deriv_a.clone())?;
    let pred_a = raw.all_elim(av.clone())?.imp_elim(assumed)?; // {Der A} ⊢ (λφ. …) A
    let beta = Thm::beta_conv(pred.apply(av)?)?;
    beta.eq_mp(pred_a)?.imp_intro(&deriv_a)?.all_intro("A", a)
}

// ============================================================================
// Transport (§6.5): derivation ↦ projected fact ↦ base-HOL model equation
// ============================================================================

/// One-step projection with an already-proved [`soundness`] theorem:
/// from `der : ⊢ Derivable_ACL2 ⌜φ⌝` conclude
/// `⊢ ∀σ. ¬(eval ⌜φ⌝ σ = anil)`. Just `all_elim` + `imp_elim` — the
/// kernel re-checks that `der` really is the derivation of `φ`.
pub fn project_with(soundness: &Thm, phi: &Term, der: Thm) -> Result<Thm> {
    soundness.clone().all_elim(phi.clone())?.imp_elim(der)
}

/// [`project_with`] proving [`soundness`] afresh (the metatheorem is
/// env-scoped and not cached; callers projecting many derivations should
/// prove it once and use [`project_with`]).
pub fn project_acl2(env: &Acl2Env, phi: &Term, der: Thm) -> Result<Thm> {
    project_with(&soundness(env)?, phi, der)
}

/// **Transport a projected ground equation into base HOL** (§6.5): from
/// `projected : ⊢ ∀σ. ¬(eval ⌜(EQUAL l r)⌝ σ = anil)` conclude the model
/// equation `⊢ ⟦l⟧ = ⟦r⟧` — instantiate `σ := λv. anil`, compute `eval`
/// by the S2 laws ([`eval_open`]), then S1's `equal_holds`. Errors (and
/// mints nothing) if the formula is not a computable `EQUAL` form.
pub fn transport_equal(env: &Acl2Env, projected: &Thm) -> Result<Thm> {
    let tm = &*env.tm;
    let bad = || {
        Error::ConnectiveRule(format!(
            "acl2 transport_equal: not a projected ground equation: {projected}"
        ))
    };
    // σ₀ := λv:bytes. anil.
    let s0 = Term::abs(Type::bytes(), tm.th.nil.clone());
    let inst = projected.clone().all_elim(s0.clone())?; // ⊢ ¬(eval ⌜φ⌝ σ₀ = anil)
    // Read ⌜φ⌝ off the instantiated conclusion.
    let phi = {
        let (_, p) = inst.concl().as_app().ok_or_else(bad)?;
        let (lhs, _) = p.as_eq().ok_or_else(bad)?;
        let (ef, s) = lhs.as_app().ok_or_else(bad)?;
        if *s != s0 {
            return Err(bad());
        }
        let (e, phi) = ef.as_app().ok_or_else(bad)?;
        if *e != tm.eval {
            return Err(bad());
        }
        phi.clone()
    };
    let chain = eval_open(tm, &phi, &s0)?; // ⊢ eval ⌜φ⌝ σ₀ = aequal ⟦l⟧ ⟦r⟧
    let v = chain.concl().as_eq().ok_or_else(bad)?.1.clone();
    let (evl, vr) = v.as_app().ok_or_else(bad)?;
    let (eqc, vl) = evl.as_app().ok_or_else(bad)?;
    if *eqc != tm.pr.equal {
        return Err(bad()); // not an EQUAL form (e.g. an IF-shaped axiom)
    }
    let ne = ne_transport(tm, &chain, inst)?; // ⊢ ¬(aequal ⟦l⟧ ⟦r⟧ = anil)
    tm.pr
        .equal_holds()?
        .all_elim(vl.clone())?
        .all_elim(vr.clone())?
        .imp_elim(ne) // ⊢ ⟦l⟧ = ⟦r⟧
}

/// **Open-`EQUAL` transport** (design §10): from a projected formula
/// with free object variables,
/// `projected : ⊢ ∀σ. ¬(eval ⌜(EQUAL lhs rhs)⌝ σ = anil)`, conclude the
/// **∀-quantified base-HOL model equation** `⊢ ∀x⃗:A. ⟦lhs⟧(x⃗) = ⟦rhs⟧(x⃗)`
/// — instantiate `σ* := λn. cond (n = ⌜V₁⌝) x₁ (… anil)` at fresh HOL
/// frees named per `binds`, compute `eval` by the S2 laws, β-fire the
/// `σ* ⌜Vᵢ⌝` redexes and decide the literal guards, land through
/// `equal_holds`, and `all_intro` in `binds` order.
///
/// **Coverage check (honesty-critical, §10.2):** every free object
/// variable of `⌜φ⌝` ([`object_vars`]) must appear in `binds`, and the
/// bound names must be distinct — otherwise an uncovered variable would
/// be *silently specialized to `anil`* by the default arm. Errors — and
/// mints nothing — on coverage failure or a non-`EQUAL` conclusion
/// (`IMPLIES`-form open transport stays deferred; SKELETONS).
pub fn transport_equal_open(
    env: &Acl2Env,
    projected: &Thm,
    binds: &[(&[u8], &str)],
) -> Result<Thm> {
    let tm = &*env.tm;
    let bad = || {
        Error::ConnectiveRule(format!(
            "acl2 transport_equal_open: not a projected open equation: {projected}"
        ))
    };
    // Read ⌜φ⌝ off a probe instantiation (the kernel re-checks the real
    // instantiation below; the probe is only for parsing).
    let phi = {
        let probe = Term::free("__probe", tm.val_ty.clone());
        let inst = projected.clone().all_elim(probe.clone())?;
        let (_, p) = inst.concl().as_app().ok_or_else(bad)?;
        let (lhs, _) = p.as_eq().ok_or_else(bad)?;
        let (ef, s) = lhs.as_app().ok_or_else(bad)?;
        if *s != probe {
            return Err(bad());
        }
        let (e, phi) = ef.as_app().ok_or_else(bad)?;
        if *e != tm.eval {
            return Err(bad());
        }
        phi.clone()
    };
    // Coverage: every object variable of φ is bound, names distinct.
    let vars = object_vars(tm, &phi)?;
    for (i, (name, _)) in binds.iter().enumerate() {
        if binds[..i].iter().any(|(m, _)| m == name) {
            return Err(Error::ConnectiveRule(format!(
                "acl2 transport_equal_open: duplicate bind for object variable `{}`",
                String::from_utf8_lossy(name)
            )));
        }
    }
    for var in &vars {
        if !binds.iter().any(|(name, _)| *name == var.as_slice()) {
            return Err(Error::ConnectiveRule(format!(
                "acl2 transport_equal_open: object variable `{}` is not covered by \
                 the binds (it would be silently specialized to anil)",
                String::from_utf8_lossy(var)
            )));
        }
    }
    // σ* := λn. cond (n = ⌜V₁⌝) x₁ (… anil) at fresh HOL frees.
    let a = tm.th.ty.clone();
    let s_star = {
        let n = Term::free("__n", Type::bytes());
        let mut body = tm.th.nil.clone();
        for (name, hol) in binds.iter().rev() {
            let lit = mk_blob(covalence_types::Bytes::from(name.to_vec()));
            body = cond(a.clone())
                .apply(n.clone().equals(lit)?)?
                .apply(Term::free(*hol, a.clone()))?
                .apply(body)?;
        }
        Term::abs(Type::bytes(), subst::close(&body, "__n"))
    };
    let inst = projected.clone().all_elim(s_star.clone())?; // ⊢ ¬(eval ⌜φ⌝ σ* = anil)
    // β-fire the σ* ⌜Vᵢ⌝ redexes and decide the literal guards — one
    // *leading*-position reduction per bind, rewritten into the chain
    // (the redexes sit in argument positions, where `collapse_conds`
    // cannot reach directly).
    let mut chain = eval_open(tm, &phi, &s_star)?; // ⊢ eval ⌜φ⌝ σ* = <image>
    for (name, _) in binds {
        let lit = mk_blob(covalence_types::Bytes::from(name.to_vec()));
        let red = Thm::beta_conv(s_star.clone().apply(lit)?)?
            .rhs_conv(|u| u.reduce())?
            .rhs_conv(collapse_conds)?; // ⊢ σ* ⌜Vᵢ⌝ = xᵢ
        chain = chain.rhs_conv(|u| u.rw_all(&red))?;
    } // ⊢ eval ⌜φ⌝ σ* = aequal L(x⃗) R(x⃗)
    let img = chain.concl().as_eq().ok_or_else(bad)?.1.clone();
    let (evl, vr) = img.as_app().ok_or_else(bad)?;
    let (eqc, vl) = evl.as_app().ok_or_else(bad)?;
    if *eqc != tm.pr.equal {
        return Err(bad()); // not an EQUAL form
    }
    let ne = ne_transport(tm, &chain, inst)?;
    let mut out = tm
        .pr
        .equal_holds()?
        .all_elim(vl.clone())?
        .all_elim(vr.clone())?
        .imp_elim(ne)?; // ⊢ L(x⃗) = R(x⃗)
    for (_, hol) in binds.iter().rev() {
        out = out.all_intro(hol, a.clone())?;
    }
    Ok(out)
}

/// The **required statement** of a [`Discharge::ModelEq`] theorem for an
/// `EQUAL`-form axiom `enc = ⌜(EQUAL lhs rhs)⌝` (design §5.2): the
/// object variables ∀-quantified in first-occurrence [`object_vars`]
/// order, body exactly the model images of the two sides. Callers prove
/// *this* term (binder names are irrelevant — conclusions are
/// locally nameless).
pub fn model_eq_target(env: &Acl2Env, enc: &Term) -> Result<Term> {
    let tm = &*env.tm;
    let bad = || {
        Error::ConnectiveRule(format!(
            "acl2 model_eq_target: not an (EQUAL lhs rhs) encoding: {enc}"
        ))
    };
    let (h, tail) = uncons(tm, enc).ok_or_else(bad)?;
    if sym_lit_of(tm, &h).as_deref() != Some(b"EQUAL") {
        return Err(bad());
    }
    let (l, rest) = uncons(tm, &tail).ok_or_else(bad)?;
    let (r, rest) = uncons(tm, &rest).ok_or_else(bad)?;
    if rest != tm.th.nil {
        return Err(bad());
    }
    let (formals, names) = target_formals(env, enc)?;
    let body = super::defun::model_image_of(env, &formals, &l)?
        .equals(super::defun::model_image_of(env, &formals, &r)?)?;
    close_target(body, &names, &env.tm)
}

/// The **required statement** of a [`Discharge::ModelHolds`] theorem for
/// a holds-form axiom: `∀v⃗. ¬(⟦enc⟧(v⃗) = anil)` (same ∀ discipline as
/// [`model_eq_target`]).
pub fn model_holds_target(env: &Acl2Env, enc: &Term) -> Result<Term> {
    let (formals, names) = target_formals(env, enc)?;
    let body = super::defun::model_image_of(env, &formals, enc)?
        .equals(env.tm.th.nil.clone())?
        .not()?;
    close_target(body, &names, &env.tm)
}

/// The object variables of `enc` as HOL frees (name = the variable's
/// UTF-8 name), in first-occurrence order.
fn target_formals(env: &Acl2Env, enc: &Term) -> Result<(Vec<(SmolStr, Term)>, Vec<String>)> {
    let tm = &*env.tm;
    let a = tm.th.ty.clone();
    let mut formals = Vec::new();
    let mut names = Vec::new();
    for var in object_vars(tm, enc)? {
        let name = String::from_utf8_lossy(&var).into_owned();
        formals.push((SmolStr::new(&name), Term::free(name.as_str(), a.clone())));
        names.push(name);
    }
    Ok((formals, names))
}

/// ∀-close a target body over the collected variable names (innermost
/// last, so the *first* object variable is the outermost ∀).
fn close_target(body: Term, names: &[String], tm: &Terms) -> Result<Term> {
    let mut out = body;
    for name in names.iter().rev() {
        out = out.forall(name.as_str(), tm.th.ty.clone())?;
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_core::Type;

    fn env() -> Acl2Env {
        ground_env().unwrap()
    }

    fn aint(i: i128) -> Term {
        let e = env();
        e.tm.th.aint_at(&mk_int(i)).unwrap()
    }

    /// Assert a closed theorem with an exact conclusion.
    fn check(thm: &Thm, expected: &Term) {
        assert!(thm.hyps().is_empty(), "must be closed: {thm}");
        assert_eq!(thm.concl(), expected);
    }

    /// **S3 gate (layout):** the clause set builds — 29 clauses
    /// (5 axioms + MP + INST + 11 congruence + 11 computation), every
    /// clause `bool`-typed, `Derivable_ACL2 φ` a closed `bool`
    /// proposition, and the index map consistent.
    #[test]
    fn t_clause_set_builds() {
        let e = env();
        let rs = acl2_rule_set(&e);
        assert_eq!(e.n_clauses(), 29);
        assert_eq!(rs.n_clauses().unwrap(), e.n_clauses());

        let d = rs.d_var();
        let d_apply = |f: &Term| d.clone().apply(f.clone());
        let clauses = (rs.clauses)(&d_apply).unwrap();
        assert_eq!(clauses.len(), e.n_clauses());
        for c in &clauses {
            assert_eq!(c.type_of().unwrap(), Type::bool());
        }

        // Index map: axioms first, then MP/INST, then the two families.
        assert_eq!(e.clause_index(ClauseKind::Axiom(0)), 0);
        assert_eq!(e.clause_index(ClauseKind::Mp), 5);
        assert_eq!(e.clause_index(ClauseKind::Inst), 6);
        assert_eq!(e.clause_index(ClauseKind::Cong(0)), 7);
        assert_eq!(e.clause_index(ClauseKind::Comp(0)), 18);
        assert_eq!(e.clause_index(ClauseKind::Comp(10)), 28);

        // Derivable_ACL2 at a closed formula is a closed bool proposition.
        let phi = e.tm.mk_equal(&aint(1), &aint(1)).unwrap();
        let der = derivable(&e, &phi).unwrap();
        assert_eq!(der.type_of().unwrap(), Type::bool());
    }

    /// Every ground axiom is derivable, with the exact
    /// `Derivable_ACL2 ⌜ax⌝` statement.
    #[test]
    fn t_axioms_derive() {
        let e = env();
        for row in e.axioms.clone() {
            let der = derive_axiom(&e, &row.name).unwrap();
            check(&der, &derivable(&e, &row.enc).unwrap());
        }
    }

    /// **S3 gate (computation):**
    /// `⊢ Derivable_ACL2 ⌜(EQUAL (BINARY-+ '2 '2) '4)⌝` by firing the
    /// `+` computation clause and folding the model image by S1's
    /// literal law.
    #[test]
    fn t_comp_two_plus_two() {
        let e = env();
        let tm = &*e.tm;

        // The raw clause instance: model image unevaluated.
        let k = e.row("BINARY-+").unwrap();
        let raw = derive_comp(&e, k, &[aint(2), aint(2)]).unwrap();
        let plus_model = tm
            .pr
            .plus
            .clone()
            .apply(aint(2))
            .unwrap()
            .apply(aint(2))
            .unwrap();
        let raw_phi = tm
            .mk_equal(
                &tm.mk_plus(&tm.quote(&aint(2)).unwrap(), &tm.quote(&aint(2)).unwrap())
                    .unwrap(),
                &tm.quote(&plus_model).unwrap(),
            )
            .unwrap();
        check(&raw, &derivable(&e, &raw_phi).unwrap());

        // Folded: ⊢ Derivable_ACL2 ⌜(EQUAL (BINARY-+ '2 '2) '4)⌝.
        let der = derive_plus_lit(&e, 2, 2).unwrap();
        let phi = tm
            .mk_equal(
                &tm.mk_plus(&tm.quote(&aint(2)).unwrap(), &tm.quote(&aint(2)).unwrap())
                    .unwrap(),
                &tm.quote(&aint(4)).unwrap(),
            )
            .unwrap();
        check(&der, &derivable(&e, &phi).unwrap());
    }

    /// An INST instance through S2's `subst`: instantiate `equal-refl`
    /// at `X ↦ '7`, landing `⊢ Derivable_ACL2 ⌜(EQUAL '7 '7)⌝`.
    #[test]
    fn t_inst_instance() {
        let e = env();
        let tm = &*e.tm;
        let (_, ax) = e.axiom("equal-refl").unwrap();
        let ax = ax.clone();
        let d_ax = derive_axiom(&e, "equal-refl").unwrap();

        let q7 = tm.quote(&aint(7)).unwrap();
        let s = finite_sigma(tm, &[(b"X", q7.clone())]).unwrap();

        // Raw INST: the unreduced subst image.
        let raw = derive_inst(&e, &ax, &s, d_ax.clone()).unwrap();
        let sub = tm
            .subst
            .clone()
            .apply(ax.clone())
            .unwrap()
            .apply(s.clone())
            .unwrap();
        check(&raw, &derivable(&e, &sub).unwrap());

        // Folded: ⊢ Derivable_ACL2 ⌜(EQUAL '7 '7)⌝.
        let der = derive_inst_ground(&e, &ax, &s, d_ax).unwrap();
        let phi = tm.mk_equal(&q7, &q7).unwrap();
        check(&der, &derivable(&e, &phi).unwrap());
    }

    /// A congruence instance: from `⊢ D ⌜(EQUAL '7 '7)⌝` twice, derive
    /// `⊢ D ⌜(EQUAL (BINARY-+ '7 '7) (BINARY-+ '7 '7))⌝`.
    #[test]
    fn t_cong_instance() {
        let e = env();
        let tm = &*e.tm;
        let (_, ax) = e.axiom("equal-refl").unwrap();
        let ax = ax.clone();
        let d_ax = derive_axiom(&e, "equal-refl").unwrap();
        let q7 = tm.quote(&aint(7)).unwrap();
        let s = finite_sigma(tm, &[(b"X", q7.clone())]).unwrap();
        let d_eq = derive_inst_ground(&e, &ax, &s, d_ax).unwrap(); // ⊢ D ⌜(EQUAL '7 '7)⌝

        let k = e.row("BINARY-+").unwrap();
        let der = derive_cong(
            &e,
            k,
            &[(q7.clone(), q7.clone()), (q7.clone(), q7.clone())],
            vec![d_eq.clone(), d_eq],
        )
        .unwrap();
        let plus77 = tm.mk_plus(&q7, &q7).unwrap();
        let phi = tm.mk_equal(&plus77, &plus77).unwrap();
        check(&der, &derivable(&e, &phi).unwrap());
    }

    /// **S3 gate (MP chain, INST through S2's subst):** derive
    /// `⊢ Derivable_ACL2 ⌜(EQUAL '4 (BINARY-+ '2 '2))⌝` by
    /// axiom(equal-symm) → INST{X ↦ (BINARY-+ '2 '2), Y ↦ '4} →
    /// MP against the computation-clause fact from
    /// [`t_comp_two_plus_two`]'s pipeline.
    #[test]
    fn t_mp_chain() {
        let e = env();
        let tm = &*e.tm;

        // p := (EQUAL (BINARY-+ '2 '2) '4), q := (EQUAL '4 (BINARY-+ '2 '2)).
        let q2 = tm.quote(&aint(2)).unwrap();
        let q4 = tm.quote(&aint(4)).unwrap();
        let plus22 = tm.mk_plus(&q2, &q2).unwrap();
        let p = tm.mk_equal(&plus22, &q4).unwrap();
        let q = tm.mk_equal(&q4, &plus22).unwrap();

        // ⊢ D ⌜(IMPLIES p q)⌝ — equal-symm instantiated at
        // {X ↦ (BINARY-+ '2 '2), Y ↦ '4}.
        let (_, symm) = e.axiom("equal-symm").unwrap();
        let symm = symm.clone();
        let d_symm = derive_axiom(&e, "equal-symm").unwrap();
        let s = finite_sigma(tm, &[(b"X", plus22.clone()), (b"Y", q4.clone())]).unwrap();
        let d_imp = derive_inst_ground(&e, &symm, &s, d_symm).unwrap();
        check(
            &d_imp,
            &derivable(&e, &tm.mk_implies(&p, &q).unwrap()).unwrap(),
        );

        // ⊢ D ⌜p⌝ — the computation clause.
        let d_p = derive_plus_lit(&e, 2, 2).unwrap();
        check(&d_p, &derivable(&e, &p).unwrap());

        // MP: ⊢ D ⌜q⌝ = ⊢ Derivable_ACL2 ⌜(EQUAL '4 (BINARY-+ '2 '2))⌝.
        let d_q = derive_mp(&e, &p, &q, d_imp, d_p).unwrap();
        check(&d_q, &derivable(&e, &q).unwrap());
    }

    /// The soundness metatheorem for the ground env, proved once and
    /// shared by the transport tests (it is deterministic — the same
    /// clause discharges every time — but not cheap).
    fn snd() -> Thm {
        use std::sync::LazyLock;
        static SND: LazyLock<std::result::Result<Thm, String>> =
            LazyLock::new(|| soundness(&ground_env().unwrap()).map_err(|e| e.to_string()));
        SND.as_ref().unwrap().clone()
    }

    /// **S3 gate (soundness):** the metatheorem is closed, with the
    /// exact designed statement
    /// `⊢ ∀A. Derivable_ACL2 A ⟹ (∀σ. ¬(eval A σ = anil))`.
    #[test]
    fn t_soundness_closed_exact() {
        let e = env();
        let tm = &*e.tm;
        let s = snd();

        let a = tm.th.ty.clone();
        let av = Term::free("A", a.clone());
        let sg = Term::free("sg", tm.val_ty.clone());
        let body = tm
            .eval
            .clone()
            .apply(av.clone())
            .unwrap()
            .apply(sg)
            .unwrap()
            .equals(tm.th.nil.clone())
            .unwrap()
            .not()
            .unwrap()
            .forall("sg", tm.val_ty.clone())
            .unwrap();
        let expected = derivable(&e, &av)
            .unwrap()
            .imp(body)
            .unwrap()
            .forall("A", a)
            .unwrap();
        check(&s, &expected);
    }

    /// **THE S3 GATE (design §6.5): `(defthm four (equal (+ 2 2) 4))`
    /// transported into base HOL.** The derivation (computation clause,
    /// model image folded), its projection through soundness, and the
    /// final closed model equation `⊢ aplus (aint 2) (aint 2) = aint 4`
    /// — produced by the derivation pipeline, with no direct-arithmetic
    /// shortcut; every intermediate is asserted exactly.
    #[test]
    fn t_defthm_four_transports() {
        let e = env();
        let tm = &*e.tm;
        let q2 = tm.quote(&aint(2)).unwrap();
        let q4 = tm.quote(&aint(4)).unwrap();
        let plus22 = tm.mk_plus(&q2, &q2).unwrap();
        let phi = tm.mk_equal(&plus22, &q4).unwrap();

        // 1. The derivation: ⊢ Derivable_ACL2 ⌜(EQUAL (BINARY-+ '2 '2) '4)⌝.
        let der = derive_plus_lit(&e, 2, 2).unwrap();
        check(&der, &derivable(&e, &phi).unwrap());

        // 2. Projection through the soundness metatheorem:
        //    ⊢ ∀σ. ¬(eval ⌜φ⌝ σ = anil).
        let projected = project_with(&snd(), &phi, der).unwrap();
        let sg = Term::free("sg", tm.val_ty.clone());
        let expected_proj = tm
            .eval
            .clone()
            .apply(phi.clone())
            .unwrap()
            .apply(sg)
            .unwrap()
            .equals(tm.th.nil.clone())
            .unwrap()
            .not()
            .unwrap()
            .forall("sg", tm.val_ty.clone())
            .unwrap();
        check(&projected, &expected_proj);

        // 3. Transport: the closed base-HOL model equation
        //    ⊢ aplus (aint 2) (aint 2) = aint 4.
        let final_thm = transport_equal(&e, &projected).unwrap();
        let expected = tm
            .pr
            .plus
            .clone()
            .apply(aint(2))
            .unwrap()
            .apply(aint(2))
            .unwrap()
            .equals(aint(4))
            .unwrap();
        check(&final_thm, &expected);
    }

    /// The INST/MP path transports too: `t_mp_chain`'s derivation of
    /// `⌜(EQUAL '4 (BINARY-+ '2 '2))⌝` lands
    /// `⊢ aint 4 = aplus (aint 2) (aint 2)` in base HOL.
    #[test]
    fn t_transport_mp_chain() {
        let e = env();
        let tm = &*e.tm;
        let q2 = tm.quote(&aint(2)).unwrap();
        let q4 = tm.quote(&aint(4)).unwrap();
        let plus22 = tm.mk_plus(&q2, &q2).unwrap();
        let p = tm.mk_equal(&plus22, &q4).unwrap();
        let q = tm.mk_equal(&q4, &plus22).unwrap();

        let (_, symm) = e.axiom("equal-symm").unwrap();
        let symm = symm.clone();
        let d_symm = derive_axiom(&e, "equal-symm").unwrap();
        let s = finite_sigma(tm, &[(b"X", plus22.clone()), (b"Y", q4.clone())]).unwrap();
        let d_imp = derive_inst_ground(&e, &symm, &s, d_symm).unwrap();
        let d_p = derive_plus_lit(&e, 2, 2).unwrap();
        let d_q = derive_mp(&e, &p, &q, d_imp, d_p).unwrap();

        let projected = project_with(&snd(), &q, d_q).unwrap();
        let final_thm = transport_equal(&e, &projected).unwrap();
        let expected = aint(4)
            .equals(
                tm.pr
                    .plus
                    .clone()
                    .apply(aint(2))
                    .unwrap()
                    .apply(aint(2))
                    .unwrap(),
            )
            .unwrap();
        check(&final_thm, &expected);
    }

    /// **Negative controls:** the transport path *errors* — mints no
    /// theorem — on (a) projecting a formula that does not match the
    /// derivation (the kernel's `imp_elim` rejects it) and (b)
    /// transporting a projected non-equational formula (`if-true` is an
    /// `IF` shape, not a computable `EQUAL` form).
    #[test]
    fn t_transport_negative_controls() {
        let e = env();
        let tm = &*e.tm;
        let q2 = tm.quote(&aint(2)).unwrap();
        let q4 = tm.quote(&aint(4)).unwrap();

        // (a) φ_false := (EQUAL '2 '4) is not what `der` derives.
        let der = derive_plus_lit(&e, 2, 2).unwrap();
        let phi_false = tm.mk_equal(&q2, &q4).unwrap();
        assert!(project_with(&snd(), &phi_false, der).is_err());

        // (b) a projected axiom that is not an EQUAL form.
        let (_, if_true) = e.axiom("if-true").unwrap();
        let if_true = if_true.clone();
        let d_ax = derive_axiom(&e, "if-true").unwrap();
        let projected = project_with(&snd(), &if_true, d_ax).unwrap();
        assert!(transport_equal(&e, &projected).is_err());
    }

    /// The ground substitution engine on a nested form: substituting
    /// inside an application, under a quote (opaque), and at an
    /// unbound variable (identity default).
    #[test]
    fn t_subst_ground_engine() {
        let e = env();
        let tm = &*e.tm;
        let x = tm.sym(b"X").unwrap();
        let w = tm.sym(b"W").unwrap();
        let q1 = tm.quote(&aint(1)).unwrap();
        let q7 = tm.quote(&aint(7)).unwrap();
        let s = finite_sigma(tm, &[(b"X", q7.clone())]).unwrap();

        // (EQUAL (BINARY-+ X '1) W)[X ↦ '7] = (EQUAL (BINARY-+ '7 '1) W).
        let phi = tm.mk_equal(&tm.mk_plus(&x, &q1).unwrap(), &w).unwrap();
        let expected = tm.mk_equal(&tm.mk_plus(&q7, &q1).unwrap(), &w).unwrap();
        let eq = subst_ground(tm, &phi, &s).unwrap();
        check(
            &eq,
            &tm.subst
                .clone()
                .apply(phi)
                .unwrap()
                .apply(s.clone())
                .unwrap()
                .equals(expected)
                .unwrap(),
        );
    }

    /// **S6 gate (layout):** the s6 env's clause set builds at the
    /// design-§2.1 formula (`na + 2 + s6 + (2+s6)·nr + nu`), the index
    /// map is consistent, and the ground env keeps the committed
    /// 29-clause layout (regression).
    #[test]
    fn t_s6_env_layout() {
        // Ground regression (s6 = 0).
        let e0 = env();
        assert!(!e0.s6);
        assert_eq!(e0.n_clauses(), 29);
        assert_eq!(e0.clause_index(ClauseKind::Cong(0)), 7);
        assert_eq!(e0.clause_index(ClauseKind::Comp(10)), 28);

        // s6 env: 10 axioms + MP + INST + IND + 11 Cong + 11 Comp +
        // 11 CongImpl = 46 clauses.
        let e6 = s6_env().unwrap();
        assert!(e6.s6);
        assert_eq!(e6.axioms.len(), 10);
        assert_eq!(e6.n_clauses(), 46);
        assert_eq!(e6.clause_index(ClauseKind::Mp), 10);
        assert_eq!(e6.clause_index(ClauseKind::Inst), 11);
        assert_eq!(e6.clause_index(ClauseKind::Ind), 12);
        assert_eq!(e6.clause_index(ClauseKind::Cong(0)), 13);
        assert_eq!(e6.clause_index(ClauseKind::Comp(0)), 24);
        assert_eq!(e6.clause_index(ClauseKind::CongImpl(0)), 35);
        assert_eq!(e6.clause_index(ClauseKind::Def(0)), 46); // (hypothetical next)
        let rs = acl2_rule_set(&e6);
        assert_eq!(rs.n_clauses().unwrap(), 46);
        let d = rs.d_var();
        let d_apply = |f: &Term| d.clone().apply(f.clone());
        for c in (rs.clauses)(&d_apply).unwrap() {
            assert_eq!(c.type_of().unwrap(), Type::bool());
        }
    }

    /// **S6 gate (Hilbert axioms):** `prop-k`/`prop-s` derivable with
    /// their exact encodings.
    #[test]
    fn t_prop_axioms_derive() {
        let e6 = s6_env().unwrap();
        let tm = &*e6.tm;
        let x = tm.sym(b"X").unwrap();
        let y = tm.sym(b"Y").unwrap();
        let z = tm.sym(b"Z").unwrap();

        let dk = derive_axiom(&e6, "prop-k").unwrap();
        let k_enc = tm.mk_implies(&x, &tm.mk_implies(&y, &x).unwrap()).unwrap();
        check(&dk, &derivable(&e6, &k_enc).unwrap());

        let ds = derive_axiom(&e6, "prop-s").unwrap();
        let s_enc = tm
            .mk_implies(
                &tm.mk_implies(&x, &tm.mk_implies(&y, &z).unwrap()).unwrap(),
                &tm.mk_implies(
                    &tm.mk_implies(&x, &y).unwrap(),
                    &tm.mk_implies(&x, &z).unwrap(),
                )
                .unwrap(),
            )
            .unwrap();
        check(&ds, &derivable(&e6, &s_enc).unwrap());
    }

    /// **S6 gate (structural pack):** `car-cons`/`cdr-cons`/`consp-cons`
    /// derivable with exact encodings, and their supplied
    /// `ModelEq`/`ModelHolds` theorems state exactly the
    /// [`model_eq_target`]/[`model_holds_target`] contracts.
    #[test]
    fn t_structural_pack() {
        let e6 = s6_env().unwrap();
        let tm = &*e6.tm;
        let x = tm.sym(b"X").unwrap();
        let y = tm.sym(b"Y").unwrap();
        let cons_xy = tm.app(b"CONS", &[x.clone(), y.clone()]).unwrap();

        for (name, enc) in [
            (
                "car-cons",
                tm.mk_equal(&tm.app(b"CAR", &[cons_xy.clone()]).unwrap(), &x)
                    .unwrap(),
            ),
            (
                "cdr-cons",
                tm.mk_equal(&tm.app(b"CDR", &[cons_xy.clone()]).unwrap(), &y)
                    .unwrap(),
            ),
            ("consp-cons", tm.app(b"CONSP", &[cons_xy.clone()]).unwrap()),
        ] {
            let d = derive_axiom(&e6, name).unwrap();
            check(&d, &derivable(&e6, &enc).unwrap());
            // The installed discharge theorem states the target contract.
            let (i, _) = e6.axiom(name).unwrap();
            match &e6.axioms[i].discharge {
                Discharge::ModelEq(t) => {
                    check(t, &model_eq_target(&e6, &enc).unwrap());
                }
                Discharge::ModelHolds(t) => {
                    check(t, &model_holds_target(&e6, &enc).unwrap());
                }
                _ => panic!("structural pack row {name} has a schema discharge"),
            }
        }
    }

    /// **S6 gate (CongImpl):** one implication-form congruence firing —
    /// hyp-free control with the exact curried encoding; non-S6 envs
    /// reject the constructor.
    #[test]
    fn t_cong_impl_instance() {
        let e6 = s6_env().unwrap();
        let tm = &*e6.tm;
        let q7 = tm.quote(&aint(7)).unwrap();
        let q8 = tm.quote(&aint(8)).unwrap();
        let k = e6.row("BINARY-+").unwrap();
        let d = derive_cong_impl(
            &e6,
            k,
            &[(q7.clone(), q8.clone()), (q8.clone(), q7.clone())],
        )
        .unwrap();
        let enc = tm
            .mk_implies(
                &tm.mk_equal(&q7, &q8).unwrap(),
                &tm.mk_implies(
                    &tm.mk_equal(&q8, &q7).unwrap(),
                    &tm.mk_equal(
                        &tm.mk_plus(&q7, &q8).unwrap(),
                        &tm.mk_plus(&q8, &q7).unwrap(),
                    )
                    .unwrap(),
                )
                .unwrap(),
            )
            .unwrap();
        check(&d, &derivable(&e6, &enc).unwrap());

        // The ground env has no CongImpl clauses.
        let e0 = env();
        assert!(derive_cong_impl(&e0, k, &[(q7.clone(), q7.clone()), (q7.clone(), q7)]).is_err());
        // And no IND clause.
        let phi = tm
            .mk_equal(&tm.sym(b"X").unwrap(), &tm.sym(b"X").unwrap())
            .unwrap();
        let dummy = derive_axiom(&e0, "equal-refl").unwrap();
        assert!(derive_ind(&e0, &phi, b"X", dummy.clone(), dummy).is_err());
    }

    /// **The per-row discharge hooks** (the API that filled the old
    /// "S4+ axiom-discharge gap"): `ModelEq`, `ModelHolds` and `Hook`
    /// axiom discharges each produce the closed applied-predicate
    /// theorem `⊢ pred ⌜ax⌝` that `soundness`'s rule induction consumes;
    /// wrong supplied theorems / failing hooks error — nothing minted.
    #[test]
    fn t_discharge_arms() {
        let e = env();
        let tm = &*e.tm;
        let pr = tm.pr;
        let pred = sound_pred(tm).unwrap();
        let x = tm.sym(b"X").unwrap();
        let y = tm.sym(b"Y").unwrap();
        let cons_xy = tm.app(b"CONS", &[x.clone(), y.clone()]).unwrap();

        // ModelEq: car-cons — (EQUAL (CAR (CONS X Y)) X) from the S1
        // theorem ⊢ ∀h t. car (acons h t) = h (∀-order = [X, Y] ✓).
        let enc_cc = tm
            .mk_equal(&tm.app(b"CAR", &[cons_xy.clone()]).unwrap(), &x)
            .unwrap();
        assert_eq!(
            object_vars(tm, &enc_cc).unwrap(),
            vec![b"X".to_vec(), b"Y".to_vec()]
        );
        let row = AxiomRow {
            name: SmolStr::new("car-cons"),
            enc: enc_cc.clone(),
            discharge: Discharge::ModelEq(pr.car_cons().unwrap()),
        };
        let th = discharge_axiom(&e, &pred, &row).unwrap();
        check(&th, &pred.clone().apply(enc_cc.clone()).unwrap());

        // A WRONG ModelEq theorem (cdr_cons for the car-cons formula)
        // fails safe.
        let wrong = AxiomRow {
            name: SmolStr::new("car-cons"),
            enc: enc_cc,
            discharge: Discharge::ModelEq(pr.cdr_cons().unwrap()),
        };
        assert!(discharge_axiom(&e, &pred, &wrong).is_err());

        // ModelHolds: consp-cons — (CONSP (CONS X Y)) from
        // ⊢ ∀h t. ¬(aconsp (acons h t) = anil) (consp_cons + t_ne_nil).
        let enc_pc = tm.app(b"CONSP", &[cons_xy]).unwrap();
        let holds = {
            let a = tm.th.ty.clone();
            let (h, t) = (Term::free("h", a.clone()), Term::free("t", a.clone()));
            let eq = pr
                .consp_cons()
                .unwrap()
                .all_elim(h)
                .unwrap()
                .all_elim(t)
                .unwrap(); // aconsp (acons h t) = t
            ne_from_eq(tm, eq, pr.t_ne_nil().unwrap())
                .unwrap()
                .all_intro("t", a.clone())
                .unwrap()
                .all_intro("h", a)
                .unwrap()
        };
        let row = AxiomRow {
            name: SmolStr::new("consp-cons"),
            enc: enc_pc.clone(),
            discharge: Discharge::ModelHolds(holds),
        };
        let th = discharge_axiom(&e, &pred, &row).unwrap();
        check(&th, &pred.clone().apply(enc_pc).unwrap());

        // Hook: build ⊢ ∀σ. ¬(eval ⌜(EQUAL X X)⌝ σ = anil) from scratch.
        let enc_rf = tm.mk_equal(&x, &x).unwrap();
        let row = AxiomRow {
            name: SmolStr::new("refl-hook"),
            enc: enc_rf.clone(),
            discharge: Discharge::Hook(std::sync::Arc::new(|env: &Acl2Env, enc: &Term| {
                let tm = &*env.tm;
                let pr = tm.pr;
                let sg = Term::free("sg", tm.val_ty.clone());
                let chain = eval_open(tm, enc, &sg)?; // = aequal σX σX
                let vx = sg
                    .clone()
                    .apply(mk_blob(covalence_types::Bytes::from(b"X".to_vec())))?;
                let ne_v = ne_from_eq(tm, pr.equal_refl()?.all_elim(vx)?, pr.t_ne_nil()?)?;
                ne_from_eq(tm, chain, ne_v)?.all_intro("sg", tm.val_ty.clone())
            })),
        };
        let th = discharge_axiom(&e, &pred, &row).unwrap();
        check(&th, &pred.clone().apply(enc_rf.clone()).unwrap());

        // A failing hook fails safe.
        let row = AxiomRow {
            name: SmolStr::new("broken-hook"),
            enc: enc_rf,
            discharge: Discharge::Hook(std::sync::Arc::new(|_: &Acl2Env, _: &Term| {
                Err(Error::ConnectiveRule("no proof".into()))
            })),
        };
        assert!(discharge_axiom(&e, &pred, &row).is_err());

        // An unknown Schema name still errors (the S3 behaviour).
        let (_, refl) = e.axiom("equal-refl").unwrap();
        let row = AxiomRow {
            name: SmolStr::new("mystery"),
            enc: refl.clone(),
            discharge: Discharge::Schema,
        };
        assert!(discharge_axiom(&e, &pred, &row).is_err());
    }
}
