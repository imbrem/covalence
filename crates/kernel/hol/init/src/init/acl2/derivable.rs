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

use covalence_core::{Error, Result, Term, Type, subst};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::derived::DerivedRules;
use covalence_hol_eval::{as_blob, mk_blob, mk_int};
use smol_str::SmolStr;

use crate::init::acl2::ladder::{self, Premise};
use crate::init::acl2::prims::PrimRow;
use crate::init::acl2::term::{Terms, terms};
use crate::init::cond::{collapse_conds, cond};
use crate::init::eq::beta_reduce;
use crate::init::ext::{TermExt, ThmExt};
use crate::metalogic::RuleSet;

// ============================================================================
// The environment
// ============================================================================

/// The data defining `Derivable_ACL2`: encoded axioms + the primitive
/// table. Env-scoped from day one (S4's per-defun growth adds axioms
/// without touching the engine).
pub struct Acl2Env {
    /// The S2 deep-term theory (encoders, `subst`, the S1/S0 layers).
    pub tm: &'static Terms,
    /// Closed encoded axiom formulas `(name, ⌜ax⌝)`, over object
    /// variables `asym "X"` etc. — instances flow from the INST clause.
    pub axioms: Vec<(SmolStr, Term)>,
    /// The S1 primitive table (drives the congruence + computation
    /// clause families).
    pub rows: Vec<PrimRow>,
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
    /// The congruence clause for table row `k`.
    Cong(usize),
    /// The computation (quote-homomorphism) clause for table row `k`.
    Comp(usize),
}

impl Acl2Env {
    /// The deterministic clause index of `kind` in the layout
    /// (axioms, MP, INST, congruence family, computation family).
    pub fn clause_index(&self, kind: ClauseKind) -> usize {
        let na = self.axioms.len();
        let nr = self.rows.len();
        match kind {
            ClauseKind::Axiom(i) => i,
            ClauseKind::Mp => na,
            ClauseKind::Inst => na + 1,
            ClauseKind::Cong(k) => na + 2 + k,
            ClauseKind::Comp(k) => na + 2 + nr + k,
        }
    }

    /// Total clause count: `|axioms| + 2 + 2·|table|`.
    pub fn n_clauses(&self) -> usize {
        self.axioms.len() + 2 + 2 * self.rows.len()
    }

    /// Look up an axiom by name: `(index, encoded formula)`.
    pub fn axiom(&self, name: &str) -> Result<(usize, &Term)> {
        self.axioms
            .iter()
            .position(|(n, _)| n == name)
            .map(|i| (i, &self.axioms[i].1))
            .ok_or_else(|| Error::ConnectiveRule(format!("acl2 env: no axiom named `{name}`")))
    }

    /// Look up a primitive-table row by surface symbol.
    pub fn row(&self, sym: &str) -> Result<usize> {
        self.rows
            .iter()
            .position(|r| r.sym == sym)
            .ok_or_else(|| Error::ConnectiveRule(format!("acl2 env: no table row `{sym}`")))
    }
}

/// The ground S3 environment: the five equality/if axiom schemas over
/// the full 11-row primitive table.
pub fn ground_env() -> Result<Acl2Env> {
    let tm = terms()?;
    let x = tm.sym(b"X")?;
    let y = tm.sym(b"Y")?;
    let z = tm.sym(b"Z")?;
    let ax = |name: &str, t: Term| (SmolStr::new(name), t);
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
    Ok(Acl2Env {
        tm,
        axioms,
        rows: tm.pr.table(),
    })
}

// ============================================================================
// The rule set + Derivable_ACL2
// ============================================================================

/// Lay the environment out as a unary [`RuleSet`] over the carrier `A`
/// (clause order per [`Acl2Env::clause_index`]).
pub fn acl2_rule_set(env: &Acl2Env) -> RuleSet<'_> {
    let tm = env.tm;
    let a = tm.th.ty.clone();
    RuleSet::new(a.clone(), move |d_apply| {
        let mut clauses = Vec::with_capacity(env.n_clauses());

        // Axiom clauses: d ⌜ax⌝.
        for (_, ax) in &env.axioms {
            clauses.push(d_apply(ax)?);
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
    let fold = subst_ground(env.tm, phi, s)?; // ⊢ subst ⌜φ⌝ s = ⌜φ[s]⌝
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

/// Ground `+` fact: `⊢ Derivable_ACL2 ⌜(EQUAL (BINARY-+ 'i 'j) 'k)⌝`
/// with `k = i + j` folded by S1's literal law (`Prims::plus_lit`) — the
/// computation-clause instance the S3 gate transports.
pub fn derive_plus_lit(env: &Acl2Env, i: i128, j: i128) -> Result<Thm> {
    let tm = env.tm;
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
fn sym_lit_of(tm: &Terms, t: &Term) -> Option<Vec<u8>> {
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
fn uncons(tm: &Terms, t: &Term) -> Option<(Term, Term)> {
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
    // asym ⌜v⌝ — a variable: look up through σ.
    if sym_lit_of(tm, phi).is_some() {
        let (_, lit) = phi.as_app().expect("sym_lit_of matched an app");
        return tm.eval_var()?.all_elim(lit.clone())?.all_elim(sg.clone());
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
        let Some(k) = tm.pr.table().iter().position(|r| r.sym.as_bytes() == name) else {
            return fallback(); // unknown head: no law, stays symbolic
        };
        (tm.eval_app(k)?, tm.pr.table()[k].arity)
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

/// Discharge one **axiom clause** at `d := pred`: prove
/// `⊢ ∀σ. ¬(eval ⌜ax⌝ σ = anil)` for the named ground schema and
/// β-expand to `⊢ pred ⌜ax⌝`. Only the five S3 ground schemas are known;
/// a new env axiom needs its own discharge (SKELETONS).
fn discharge_axiom(env: &Acl2Env, pred: &Term, name: &str, enc: &Term) -> Result<Thm> {
    let tm = env.tm;
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
        other => {
            return Err(Error::ConnectiveRule(format!(
                "acl2 soundness: no discharge for axiom schema `{other}` \
                 (only the five S3 ground schemas are known)"
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
    let tm = env.tm;
    let pr = tm.pr;
    let a = tm.th.ty.clone();
    let anil = tm.th.nil.clone();
    let t = pr.t.clone();
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
    // Assume eval q σ = anil; the whole IMPLIES form then computes to anil.
    let g = eq_.clone().equals(anil.clone())?;
    let d1 = Thm::assume(g.clone())?
        .cong_arg(pr.aif.clone())?
        .cong_fn(t.clone())?
        .cong_fn(anil.clone())? // aif Eq t anil = aif anil t anil
        .trans(pr.if_nil()?.all_elim(t.clone())?.all_elim(anil.clone())?)?; // = anil
    let d2 = d1
        .cong_arg(pr.aif.clone().apply(ep.clone())?)?
        .cong_fn(t.clone())? // aif Ep (aif Eq t anil) t = aif Ep anil t
        .trans(
            pr.if_t()?
                .all_elim(ep)?
                .all_elim(anil.clone())?
                .all_elim(t)?
                .imp_elim(hp)?,
        )?; // = anil
    let f = hi2.not_elim(d2)?; // {g, d imp, d p} ⊢ F
    let nf_q = f
        .imp_intro(&g)?
        .not_intro()? // ¬(eval q σ = anil)
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
    let tm = env.tm;
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

/// Discharge the **congruence clause** for table row `k` at `d := pred`:
/// per-argument `equal_holds` turns the premises into HOL equations,
/// argument-wise congruence + `equal_refl` close the conclusion.
fn discharge_cong(env: &Acl2Env, pred: &Term, k: usize) -> Result<Thm> {
    let tm = env.tm;
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

/// Discharge the **computation clause** for table row `k` at `d := pred`:
/// both sides of the quote-homomorphism evaluate to the *same* model
/// application, so `equal_refl` + `t_ne_nil` close it.
fn discharge_comp(env: &Acl2Env, pred: &Term, k: usize) -> Result<Thm> {
    let tm = env.tm;
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

/// Discharge every clause of [`acl2_rule_set`] at `d := pred`, in clause
/// order (the invariant that makes `rule_induction`'s `imp_elim` check).
fn discharge_closed(env: &Acl2Env, pred: &Term) -> Result<Vec<Thm>> {
    let mut proofs = Vec::with_capacity(env.n_clauses());
    for (name, enc) in &env.axioms {
        proofs.push(discharge_axiom(env, pred, name, enc)?);
    }
    proofs.push(discharge_mp(env, pred)?);
    proofs.push(discharge_inst(env, pred)?);
    for k in 0..env.rows.len() {
        proofs.push(discharge_cong(env, pred, k)?);
    }
    for k in 0..env.rows.len() {
        proofs.push(discharge_comp(env, pred, k)?);
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
    let tm = env.tm;
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
    let tm = env.tm;
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
        for (name, ax) in e.axioms.clone() {
            let der = derive_axiom(&e, &name).unwrap();
            check(&der, &derivable(&e, &ax).unwrap());
        }
    }

    /// **S3 gate (computation):**
    /// `⊢ Derivable_ACL2 ⌜(EQUAL (BINARY-+ '2 '2) '4)⌝` by firing the
    /// `+` computation clause and folding the model image by S1's
    /// literal law.
    #[test]
    fn t_comp_two_plus_two() {
        let e = env();
        let tm = e.tm;

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
        let tm = e.tm;
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
        let tm = e.tm;
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
        let tm = e.tm;

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
        let tm = e.tm;
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
        let tm = e.tm;
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
        let tm = e.tm;
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
        let tm = e.tm;
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
        let tm = e.tm;
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
}
