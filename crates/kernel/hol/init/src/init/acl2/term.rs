//! **S2 — metacircular pseudo-terms + valuation semantics.**
//!
//! ACL2 pseudo-terms **are carrier values** ([`super::carrier`]) — no
//! second datatype: variables are symbols (`asym s`), constants arrive
//! quoted (`(QUOTE v)` = `acons ⌜QUOTE⌝ (acons v anil)`), and
//! applications are conses `(f a₁ … aₙ)` with `f` a primitive-table
//! symbol ([`super::prims::PrimRow`]). The S2/S3 **fragment**: `lambda`
//! is deferred to S4, and unknown heads evaluate to `anil` — honest
//! fragment boundaries (this directory's `SKELETONS.md`).
//!
//! The evaluator is **one pair-valued paramorphic recursor** (term-eval ×
//! list-eval, needed because a cons is a term *or* an argument list and
//! shape can't distinguish them), at `β := (bytes → A) → prod A A`:
//!
//! ```text
//! ev : A → (bytes → A) → A × A                                ("acl2.ev")
//!   aatom l   ↦ λσ. pair (coprod_case (λi. aint i) (λs. σ s) l) anil
//!   anil      ↦ λσ. pair anil anil
//!   acons h t ↦ λσ. pair (dispatch h) (acons (fst (eh σ)) (snd (et σ)))
//!     with images eh = ev h, et = ev t, vs := snd (et σ), and dispatch h =
//!       cond (h = ⌜QUOTE⌝) (car t)                      -- raw t: paramorphism
//!       (cond (h = ⌜IF⌝) (aif (car vs) (car (cdr vs)) (car (cdr (cdr vs))))
//!       (… one cond per primitive-table row …  anil))   -- unknown head: nil
//!
//! eval := λφ σ. fst (ev φ σ)      evlis := λφ σ. snd (ev φ σ)
//! ```
//!
//! **Substitution** has the same pair-valued paramorphic shape
//! (`"acl2.subst-ev"`, projections `subst`/`lsubst`), with `σs : bytes → A`
//! mapping variable names to *term encodings*; quoted forms are opaque and
//! application heads stay raw.
//!
//! The key S2 lemma is **semantic substitution** ([`Terms::subst_sema`]):
//!
//! ```text
//! ⊢ ∀φ. ∀σs σ.  eval  (subst  φ σs) σ = eval  φ (λv. eval (σs v) σ)
//!             ∧ evlis (lsubst φ σs) σ = evlis φ (λv. eval (σs v) σ)
//! ```
//!
//! by carrier induction at the conjunctive motive — the discharge of
//! S3's INST rule. Everything here is a derived theorem over existing
//! kernel rules; nothing is trusted, no axiom is postulated.

use std::sync::{Arc, LazyLock};

use covalence_core::{Error, Result, Term, Type, subst};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::derived::DerivedRules;

use crate::init::acl2::carrier::{Acl2, acl2_payload};
use crate::init::acl2::prims::{PrimRow, Prims, eqf_intro, prims};
use crate::init::cond::{collapse_conds, cond};
use crate::init::coprod::{cases as coprod_cases, coprod_case, inl, inr};
use crate::init::eq::{beta_expand, beta_reduce};
use crate::init::ext::{TermExt, ThmExt};
use crate::init::inductive::carved::apply_def;
use crate::init::logic::exists_elim;
use crate::init::prod::{fst, fst_pair, pair, prod, snd, snd_pair};

/// A pair-valued paramorphic definition (`ev` / `subst-ev`): the recursor
/// constant, its defining equation, the exact step terms (law derivation
/// re-runs `prec_eq` against them), and the two projection constants with
/// their defining equations.
struct ParaDef {
    con: Term,
    def_eq: Thm,
    steps: [Term; 3],
    /// `fst`-projection constant (`eval` / `subst`) + its definition.
    fst_con: Term,
    fst_eq: Thm,
    /// `snd`-projection constant (`evlis` / `lsubst`) + its definition.
    snd_con: Term,
    snd_eq: Thm,
}

/// The S2 deep-term theory over the ACL2 carrier. Built exactly once
/// ([`terms`]).
pub struct Terms {
    /// The S1 primitive theory.
    pub pr: &'static Prims,
    /// The S0 carrier theory.
    pub th: &'static Acl2,
    /// The valuation type `bytes → A` (both `σ` and `σs`).
    pub val_ty: Type,
    /// `ev : A → (bytes → A) → prod A A` — the pair-valued evaluator.
    pub ev: Term,
    /// `eval : A → (bytes → A) → A` — term evaluation (`fst ∘ ev`).
    pub eval: Term,
    /// `evlis : A → (bytes → A) → A` — argument-list evaluation.
    pub evlis: Term,
    /// `sev : A → (bytes → A) → prod A A` — the pair-valued substituter.
    pub sev: Term,
    /// `subst : A → (bytes → A) → A` — term substitution.
    pub subst: Term,
    /// `lsubst : A → (bytes → A) → A` — argument-list substitution.
    pub lsubst: Term,
    /// `asym ⌜"QUOTE"⌝` / `asym ⌜"IF"⌝` — the special-form heads.
    pub qsym: Term,
    /// See [`Terms::qsym`].
    pub ifsym: Term,
    /// The S1 primitive table driving the dispatch spine.
    rows: Vec<PrimRow>,
    /// `λi:int. aint i` — the shared int arm of the atom steps.
    ci: Term,
    /// `prod A A`'s recursor result type `(bytes → A) → prod A A`.
    beta_ty: Type,
    ev_pd: ParaDef,
    sev_pd: ParaDef,
}

static TERMS: LazyLock<std::result::Result<Arc<Terms>, String>> =
    LazyLock::new(|| Terms::build().map(Arc::new).map_err(|e| e.to_string()));

/// The process-global S2 deep-term theory (the *primitive-table* build —
/// S4 envs with user rows carry their own [`Terms::build_with`] value).
pub fn terms() -> Result<&'static Terms> {
    TERMS
        .as_ref()
        .map(|arc| &**arc)
        .map_err(|e| Error::ConnectiveRule(format!("acl2 terms build failed: {e}")))
}

/// The process-global theory as a shareable handle (what `ground_env`
/// stores — allocation-free, clones the static `Arc`).
pub fn arc_terms() -> Result<Arc<Terms>> {
    TERMS
        .as_ref()
        .cloned()
        .map_err(|e| Error::ConnectiveRule(format!("acl2 terms build failed: {e}")))
}

/// Split a `⊢ C = body` definition into `(C, the equation)`.
fn defined(name: &str, body: Term) -> Result<(Term, Thm)> {
    let eq = Thm::define(name, body)?;
    let c = eq.concl().as_eq().ok_or(Error::NotAnEquation)?.0.clone();
    Ok((c, eq))
}

/// `car (cdr^i vs)` — the `i`-th argument of an evaluated argument list.
fn proj_arg(th: &Acl2, vs: &Term, i: usize) -> Result<Term> {
    let mut cur = vs.clone();
    for _ in 0..i {
        cur = th.cdr.clone().apply(cur)?;
    }
    th.car.clone().apply(cur)
}

/// The `dispatch h` cond-spine of the `ev` cons step (module docs):
/// `QUOTE` (raw `t`), `IF`, one cond per table row (args projected from
/// `vs`), default `anil`.
fn build_dispatch(
    pr: &Prims,
    th: &Acl2,
    rows: &[PrimRow],
    qsym: &Term,
    ifsym: &Term,
    h: &Term,
    t: &Term,
    vs: &Term,
) -> Result<Term> {
    let a = th.ty.clone();
    let mut acc = th.nil.clone();
    for row in rows.iter().rev() {
        let guard = h
            .clone()
            .equals(th.asym_lit(row.sym.as_str().as_bytes())?)?;
        let mut expr = row.model.clone();
        for i in 0..row.arity {
            expr = expr.apply(proj_arg(th, vs, i)?)?;
        }
        acc = cond(a.clone()).apply(guard)?.apply(expr)?.apply(acc)?;
    }
    let if_expr = pr
        .aif
        .clone()
        .apply(proj_arg(th, vs, 0)?)?
        .apply(proj_arg(th, vs, 1)?)?
        .apply(proj_arg(th, vs, 2)?)?;
    acc = cond(a.clone())
        .apply(h.clone().equals(ifsym.clone())?)?
        .apply(if_expr)?
        .apply(acc)?;
    let q_expr = th.car.clone().apply(t.clone())?;
    cond(a)
        .apply(h.clone().equals(qsym.clone())?)?
        .apply(q_expr)?
        .apply(acc)
}

impl Terms {
    fn build() -> Result<Terms> {
        Self::build_with(prims()?.table())
    }

    /// Build the deep-term theory over an **extended row table** (the
    /// prims ++ user-defun rows of an S4 env — S4+S6 design §1). The
    /// evaluator/substituter constants are re-minted per build
    /// (`Thm::define` allocates a fresh `Def` each call, so distinct
    /// envs' `eval`s are distinct constants and their theorems never
    /// mix); the dispatch spine, computation laws and `subst_sema` are
    /// all data-driven from `rows`.
    pub fn build_with(rows: Vec<PrimRow>) -> Result<Terms> {
        let pr = prims()?;
        let th = pr.th;
        let a = th.ty.clone();
        let anil = th.nil.clone();
        let vt = Type::fun(Type::bytes(), a.clone());
        let pt = prod(a.clone(), a.clone());
        let beta_ty = Type::fun(vt.clone(), pt.clone());
        let qsym = th.asym_lit(b"QUOTE")?;
        let ifsym = th.asym_lit(b"IF")?;

        // λi:int. aint i — the int arm shared by both atom steps.
        let ci = {
            let i = Term::free("__ci", Type::int());
            let body = th.aint_at(&i)?;
            Term::abs(Type::int(), subst::close(&body, "__ci"))
        };
        let pair_aa = pair(a.clone(), a.clone());
        let fst_aa = fst(a.clone(), a.clone());
        let snd_aa = snd(a.clone(), a.clone());

        // Shared atom step: λl. λσ. pair (case ci (λv. σ v) l) anil.
        let sa = {
            let l = Term::free("__l", acl2_payload());
            let s0 = Term::free("__s0", vt.clone());
            let arm = {
                let v = Term::free("__av", Type::bytes());
                let body = s0.clone().apply(v)?;
                Term::abs(Type::bytes(), subst::close(&body, "__av"))
            };
            let case_t = coprod_case(Type::int(), Type::bytes(), a.clone())
                .apply(ci.clone())?
                .apply(arm)?
                .apply(l)?;
            let body = pair_aa.clone().apply(case_t)?.apply(anil.clone())?;
            let l_s = Term::abs(vt.clone(), subst::close(&body, "__s0"));
            Term::abs(acl2_payload(), subst::close(&l_s, "__l"))
        };
        // Shared nil step: λσ. pair anil anil.
        let sn = Term::abs(
            vt.clone(),
            pair_aa.clone().apply(anil.clone())?.apply(anil.clone())?,
        );

        // Close λh λt λi1 λi2 λσ. body over the standard frees.
        let close_cons_step = |body: Term| -> Term {
            let l_s = Term::abs(vt.clone(), subst::close(&body, "__s0"));
            let l_i2 = Term::abs(beta_ty.clone(), subst::close(&l_s, "__i2"));
            let l_i1 = Term::abs(beta_ty.clone(), subst::close(&l_i2, "__i1"));
            let l_t = Term::abs(a.clone(), subst::close(&l_i1, "__t"));
            Term::abs(a.clone(), subst::close(&l_t, "__h"))
        };
        let h = Term::free("__h", a.clone());
        let t = Term::free("__t", a.clone());
        let i1 = Term::free("__i1", beta_ty.clone());
        let i2 = Term::free("__i2", beta_ty.clone());
        let s0 = Term::free("__s0", vt.clone());
        let vs = snd_aa.clone().apply(i2.clone().apply(s0.clone())?)?;
        let head_img = fst_aa.clone().apply(i1.clone().apply(s0.clone())?)?;
        let img_list = th.cons.clone().apply(head_img)?.apply(vs.clone())?;

        // ev cons step: pair (dispatch h t vs) (acons (fst (i1 σ)) vs).
        let sc_ev = {
            let d = build_dispatch(pr, th, &rows, &qsym, &ifsym, &h, &t, &vs)?;
            close_cons_step(pair_aa.clone().apply(d)?.apply(img_list.clone())?)
        };
        // subst cons step: pair (cond (h = ⌜QUOTE⌝) (acons h t) (acons h vs))
        //                       (acons (fst (i1 σ)) vs).
        let sc_sev = {
            let keep = th.cons.clone().apply(h.clone())?.apply(t.clone())?;
            let repl = th.cons.clone().apply(h.clone())?.apply(vs.clone())?;
            let d = cond(a.clone())
                .apply(h.clone().equals(qsym.clone())?)?
                .apply(keep)?
                .apply(repl)?;
            close_cons_step(pair_aa.clone().apply(d)?.apply(img_list)?)
        };

        // The recursors + their projections.
        let mk_pd =
            |name: &str, fst_name: &str, snd_name: &str, steps: [Term; 3]| -> Result<ParaDef> {
                let (con, def_eq) = defined(name, th.cs.prec(&steps, &beta_ty)?)?;
                let mk_proj = |pname: &str, proj: &Term| -> Result<(Term, Thm)> {
                    let p = Term::free("__p", a.clone());
                    let s = Term::free("__s", vt.clone());
                    let body = proj
                        .clone()
                        .apply(con.clone().apply(p.clone())?.apply(s.clone())?)?;
                    let l_s = Term::abs(vt.clone(), subst::close(&body, "__s"));
                    defined(pname, Term::abs(a.clone(), subst::close(&l_s, "__p")))
                };
                let (fst_con, fst_eq) = mk_proj(fst_name, &fst_aa)?;
                let (snd_con, snd_eq) = mk_proj(snd_name, &snd_aa)?;
                Ok(ParaDef {
                    con,
                    def_eq,
                    steps,
                    fst_con,
                    fst_eq,
                    snd_con,
                    snd_eq,
                })
            };
        let ev_pd = mk_pd(
            "acl2.ev",
            "acl2.eval",
            "acl2.evlis",
            [sa.clone(), sn.clone(), sc_ev],
        )?;
        let sev_pd = mk_pd(
            "acl2.subst-ev",
            "acl2.subst",
            "acl2.lsubst",
            [sa, sn, sc_sev],
        )?;

        Ok(Terms {
            pr,
            th,
            val_ty: vt,
            ev: ev_pd.con.clone(),
            eval: ev_pd.fst_con.clone(),
            evlis: ev_pd.snd_con.clone(),
            sev: sev_pd.con.clone(),
            subst: sev_pd.fst_con.clone(),
            lsubst: sev_pd.snd_con.clone(),
            qsym,
            ifsym,
            rows,
            ci,
            beta_ty,
            ev_pd,
            sev_pd,
        })
    }

    // ------------------------------------------------------------------
    // Small builders / encoders
    // ------------------------------------------------------------------

    fn a(&self) -> Type {
        self.th.ty.clone()
    }

    /// The row table THIS theory was built over (prims ++ user rows for
    /// an S4 env) — the single dispatch source for `eval`/S3 clauses.
    pub fn rows(&self) -> &[PrimRow] {
        &self.rows
    }

    fn acons_t(&self, h: &Term, t: &Term) -> Result<Term> {
        self.th.cons.clone().apply(h.clone())?.apply(t.clone())
    }

    /// `asym ⌜name⌝` — a symbol (= a pseudo-term variable).
    pub fn sym(&self, name: &[u8]) -> Result<Term> {
        self.th.asym_lit(name)
    }

    /// `(QUOTE v)` = `acons ⌜QUOTE⌝ (acons v anil)` — a quoted constant.
    pub fn quote(&self, v: &Term) -> Result<Term> {
        let inner = self.acons_t(v, &self.th.nil)?;
        self.acons_t(&self.qsym, &inner)
    }

    /// `(x₁ … xₙ)` as a nil-terminated cons list.
    pub fn listn(&self, items: &[Term]) -> Result<Term> {
        let mut acc = self.th.nil.clone();
        for x in items.iter().rev() {
            acc = self.acons_t(x, &acc)?;
        }
        Ok(acc)
    }

    /// `(F a₁ … aₙ)` — an application form with symbol head `F`.
    pub fn app(&self, name: &[u8], args: &[Term]) -> Result<Term> {
        let tail = self.listn(args)?;
        self.acons_t(&self.sym(name)?, &tail)
    }

    /// `(EQUAL x y)`.
    pub fn mk_equal(&self, x: &Term, y: &Term) -> Result<Term> {
        self.app(b"EQUAL", &[x.clone(), y.clone()])
    }

    /// `(IF c y z)`.
    pub fn mk_if(&self, c: &Term, y: &Term, z: &Term) -> Result<Term> {
        self.app(b"IF", &[c.clone(), y.clone(), z.clone()])
    }

    /// `(IMPLIES p q)` in its `IF` macro shape:
    /// `(IF p (IF q 'T 'NIL) 'T)`.
    pub fn mk_implies(&self, p: &Term, q: &Term) -> Result<Term> {
        let qt = self.quote(&self.pr.t)?;
        let qnil = self.quote(&self.th.nil)?;
        let inner = self.mk_if(q, &qt, &qnil)?;
        self.mk_if(p, &inner, &qt)
    }

    /// `(BINARY-+ x y)`.
    pub fn mk_plus(&self, x: &Term, y: &Term) -> Result<Term> {
        self.app(b"BINARY-+", &[x.clone(), y.clone()])
    }

    /// `car (cdr^i vs)` — the `i`-th argument projection (also the shape
    /// S3's computation clauses project with).
    pub fn arg_at(&self, vs: &Term, i: usize) -> Result<Term> {
        proj_arg(self.th, vs, i)
    }

    /// `λv:bytes. s v` — the symbol arm of the atom step at valuation `s`
    /// (the exact term β-substitution leaves in the computation laws).
    fn sym_arm(&self, s: &Term) -> Result<Term> {
        let v = Term::free("__av", Type::bytes());
        let body = s.clone().apply(v)?;
        Ok(Term::abs(Type::bytes(), subst::close(&body, "__av")))
    }

    /// `λv:bytes. eval (σs v) σ` — the composed valuation of `subst_sema`.
    fn sigma_comp(&self, ss: &Term, sg: &Term) -> Result<Term> {
        let v = Term::free("__cv", Type::bytes());
        let body = self
            .eval
            .clone()
            .apply(ss.clone().apply(v)?)?
            .apply(sg.clone())?;
        Ok(Term::abs(Type::bytes(), subst::close(&body, "__cv")))
    }

    // ------------------------------------------------------------------
    // Recursor computation plumbing (private)
    // ------------------------------------------------------------------

    /// `⊢ con (aatom b) s = pair (case ci (λv. s v) b) anil`.
    fn pd_atom_at(&self, pd: &ParaDef, b: &Term, s: &Term) -> Result<Thm> {
        let atom_b = self.th.atom.clone().apply(b.clone())?;
        let comp = self
            .th
            .cs
            .prec_eq(&pd.steps, 0, &self.beta_ty)?
            .all_elim(b.clone())?;
        pd.def_eq
            .clone()
            .cong_fn(atom_b)?
            .trans(comp)?
            .cong_fn(s.clone())?
            .rhs_conv(|tm| tm.reduce())
    }

    /// `⊢ con anil s = pair anil anil`.
    fn pd_nil_at(&self, pd: &ParaDef, s: &Term) -> Result<Thm> {
        let comp = self.th.cs.prec_eq(&pd.steps, 1, &self.beta_ty)?;
        pd.def_eq
            .clone()
            .cong_fn(self.th.nil.clone())?
            .trans(comp)?
            .cong_fn(s.clone())?
            .rhs_conv(|tm| tm.reduce())
    }

    /// `⊢ con (acons h t) s = pair <fst step> <snd step>` with the
    /// recursor images folded back to `con` (the lisp.rs:301 trick)
    /// **before** reducing.
    fn pd_cons_at(&self, pd: &ParaDef, h: &Term, t: &Term, s: &Term) -> Result<Thm> {
        let ht = self.acons_t(h, t)?;
        let comp = self
            .th
            .cs
            .prec_eq(&pd.steps, 2, &self.beta_ty)?
            .all_elim(h.clone())?
            .all_elim(t.clone())?;
        pd.def_eq
            .clone()
            .cong_fn(ht)?
            .trans(comp)?
            .rhs_conv(|tm| tm.rw_all(&pd.def_eq.clone().sym()?))?
            .cong_fn(s.clone())?
            .rhs_conv(|tm| tm.reduce())
    }

    /// Project a pair law `⊢ con x s = pair D L` through the defined
    /// `fst`/`snd` constant: `⊢ (fst|snd)_con x s = D|L`.
    fn ctor_val(
        &self,
        pd: &ParaDef,
        first: bool,
        pair_law: &Thm,
        x: &Term,
        s: &Term,
    ) -> Result<Thm> {
        let proj_eq = if first { &pd.fst_eq } else { &pd.snd_eq };
        let e = apply_def(proj_eq, &[x.clone(), s.clone()])? // proj_con x s = proj (con x s)
            .rhs_conv(|tm| tm.rw_all(pair_law))?; // = proj (pair D L)
        let rhs = e.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
        let (_, pair_dl) = rhs.as_app().ok_or(Error::NotAnEquation)?;
        let (pair_d, l) = pair_dl.as_app().ok_or(Error::NotAnEquation)?;
        let (_, d) = pair_d.as_app().ok_or(Error::NotAnEquation)?;
        let clause = if first {
            fst_pair(&self.a(), &self.a(), d, l)?
        } else {
            snd_pair(&self.a(), &self.a(), d, l)?
        };
        e.trans(clause)
    }

    /// `⊢ (fst|snd)_con (aatom b) s = case ci (λv. s v) b | anil`.
    fn atom_val_at(&self, pd: &ParaDef, first: bool, b: &Term, s: &Term) -> Result<Thm> {
        let law = self.pd_atom_at(pd, b, s)?;
        let atom_b = self.th.atom.clone().apply(b.clone())?;
        self.ctor_val(pd, first, &law, &atom_b, s)
    }

    /// `⊢ (fst|snd)_con anil s = anil`.
    fn nil_val_at(&self, pd: &ParaDef, first: bool, s: &Term) -> Result<Thm> {
        let law = self.pd_nil_at(pd, s)?;
        self.ctor_val(pd, first, &law, &self.th.nil.clone(), s)
    }

    /// `⊢ fst_con (aint i) s = aint i` — integers self-evaluate /
    /// self-substitute (the shared `case_inl` route).
    fn int_val_at(&self, pd: &ParaDef, i: &Term, s: &Term) -> Result<Thm> {
        let inl_i = inl(Type::int(), Type::bytes()).apply(i.clone())?;
        let base = self.atom_val_at(pd, true, &inl_i, s)?;
        let start = self
            .th
            .int_unfold(i)? // aint i = aatom (inl i)
            .cong_arg(pd.fst_con.clone())?
            .cong_fn(s.clone())?;
        start
            .trans(base)?
            .trans(crate::init::coprod::case_inl(
                &Type::int(),
                &Type::bytes(),
                &self.a(),
                &self.ci,
                &self.sym_arm(s)?,
                i,
            )?)?
            .rhs_conv(|tm| tm.reduce())
    }

    /// `⊢ fst_con (asym v) s = s v` (further β-reduced when `s` is a λ) —
    /// variables look up through the valuation (the `case_inr` route).
    fn sym_val_at(&self, pd: &ParaDef, v: &Term, s: &Term) -> Result<Thm> {
        let inr_v = inr(Type::int(), Type::bytes()).apply(v.clone())?;
        let base = self.atom_val_at(pd, true, &inr_v, s)?;
        let start = self
            .th
            .sym_unfold(v)? // asym v = aatom (inr v)
            .cong_arg(pd.fst_con.clone())?
            .cong_fn(s.clone())?;
        start
            .trans(base)?
            .trans(crate::init::coprod::case_inr(
                &Type::int(),
                &Type::bytes(),
                &self.a(),
                &self.ci,
                &self.sym_arm(s)?,
                v,
            )?)?
            .rhs_conv(|tm| tm.reduce())
    }

    /// `⊢ evlis x s = snd (ev x s)` (resp. `eval`/`fst`, `lsubst`/`subst`)
    /// — the projection unfold used (symmetrically) as the fold step.
    fn proj_unfold(&self, pd: &ParaDef, first: bool, x: &Term, s: &Term) -> Result<Thm> {
        apply_def(
            if first { &pd.fst_eq } else { &pd.snd_eq },
            &[x.clone(), s.clone()],
        )
    }

    /// `⊢ eval (acons h t) σ = dispatch(h, t, evlis t σ)` — the raw cons
    /// computation law with the tail image folded to `evlis`.
    fn eval_cons_at(&self, h: &Term, t: &Term, s: &Term) -> Result<Thm> {
        let law = self.pd_cons_at(&self.ev_pd, h, t, s)?;
        let ht = self.acons_t(h, t)?;
        self.ctor_val(&self.ev_pd, true, &law, &ht, s)?
            .rhs_conv(|tm| tm.rw_all(&self.proj_unfold(&self.ev_pd, false, t, s)?.sym()?))
    }

    /// `⊢ evlis (acons h t) σ = acons (eval h σ) (evlis t σ)` at fixed terms.
    fn evlis_cons_at(&self, h: &Term, t: &Term, s: &Term) -> Result<Thm> {
        let law = self.pd_cons_at(&self.ev_pd, h, t, s)?;
        let ht = self.acons_t(h, t)?;
        self.ctor_val(&self.ev_pd, false, &law, &ht, s)?
            .rhs_conv(|tm| tm.rw_all(&self.proj_unfold(&self.ev_pd, true, h, s)?.sym()?))?
            .rhs_conv(|tm| tm.rw_all(&self.proj_unfold(&self.ev_pd, false, t, s)?.sym()?))
    }

    /// `⊢ subst (acons h t) σs = cond (h = ⌜QUOTE⌝) (acons h t)
    /// (acons h (lsubst t σs))` at fixed terms.
    fn subst_cons_at(&self, h: &Term, t: &Term, s: &Term) -> Result<Thm> {
        let law = self.pd_cons_at(&self.sev_pd, h, t, s)?;
        let ht = self.acons_t(h, t)?;
        self.ctor_val(&self.sev_pd, true, &law, &ht, s)?
            .rhs_conv(|tm| tm.rw_all(&self.proj_unfold(&self.sev_pd, false, t, s)?.sym()?))
    }

    /// `⊢ lsubst (acons h t) σs = acons (subst h σs) (lsubst t σs)`.
    fn lsubst_cons_at(&self, h: &Term, t: &Term, s: &Term) -> Result<Thm> {
        let law = self.pd_cons_at(&self.sev_pd, h, t, s)?;
        let ht = self.acons_t(h, t)?;
        self.ctor_val(&self.sev_pd, false, &law, &ht, s)?
            .rhs_conv(|tm| tm.rw_all(&self.proj_unfold(&self.sev_pd, true, h, s)?.sym()?))?
            .rhs_conv(|tm| tm.rw_all(&self.proj_unfold(&self.sev_pd, false, t, s)?.sym()?))
    }

    /// Fire the dispatch guards of an equation whose RHS is the dispatch
    /// spine at concrete head `target`: every guard before `target` is
    /// decided `⌜F⌝` by [`Acl2::sym_ne`], `target`'s own guard `⌜T⌝` by
    /// reflexivity, then the literal conds collapse.
    fn fire_dispatch(&self, acc: Thm, target: &str) -> Result<Thm> {
        let mut acc = acc;
        let names: Vec<&str> = ["QUOTE", "IF"]
            .into_iter()
            .chain(self.rows.iter().map(|r| r.sym.as_str()))
            .collect();
        for name in names {
            if name == target {
                let hk = self.th.asym_lit(name.as_bytes())?;
                let ge = Thm::refl(hk)?.eqt_intro()?;
                acc = acc.rhs_conv(|tm| tm.rw_all(&ge))?;
                return acc.rhs_conv(collapse_conds);
            }
            let ge = eqf_intro(self.th.sym_ne(target.as_bytes(), name.as_bytes())?)?;
            acc = acc.rhs_conv(|tm| tm.rw_all(&ge))?;
        }
        Err(Error::ConnectiveRule(format!(
            "acl2 fire_dispatch: `{target}` is not a dispatch head"
        )))
    }

    // ------------------------------------------------------------------
    // Evaluation computation laws (public, all closed)
    // ------------------------------------------------------------------

    /// `⊢ ∀s σ. eval (asym s) σ = σ s` — variables look up through the
    /// valuation.
    pub fn eval_var(&self) -> Result<Thm> {
        let s = Term::free("s", Type::bytes());
        let sg = Term::free("sg", self.val_ty.clone());
        self.sym_val_at(&self.ev_pd, &s, &sg)?
            .all_intro("sg", self.val_ty.clone())?
            .all_intro("s", Type::bytes())
    }

    /// `⊢ ∀i σ. eval (aint i) σ = aint i` — integers self-evaluate.
    pub fn eval_int(&self) -> Result<Thm> {
        let i = Term::free("i", Type::int());
        let sg = Term::free("sg", self.val_ty.clone());
        self.int_val_at(&self.ev_pd, &i, &sg)?
            .all_intro("sg", self.val_ty.clone())?
            .all_intro("i", Type::int())
    }

    /// `⊢ ∀σ. eval anil σ = anil`.
    pub fn eval_nil(&self) -> Result<Thm> {
        let sg = Term::free("sg", self.val_ty.clone());
        self.nil_val_at(&self.ev_pd, true, &sg)?
            .all_intro("sg", self.val_ty.clone())
    }

    /// `⊢ ∀x σ. eval (q x) σ = x` — quoted constants evaluate to their
    /// payload (raw-`t` paramorphism: the payload is **not** evaluated).
    pub fn eval_quote(&self) -> Result<Thm> {
        let x = Term::free("x", self.a());
        let sg = Term::free("sg", self.val_ty.clone());
        let tail = self.acons_t(&x, &self.th.nil)?;
        let acc = self.eval_cons_at(&self.qsym, &tail, &sg)?;
        let acc = self.fire_dispatch(acc, "QUOTE")?; // = car (acons x anil)
        acc.trans(self.th.cs.proj_scons(false, &x, &self.th.nil)?)?
            .all_intro("sg", self.val_ty.clone())?
            .all_intro("x", self.a())
    }

    /// `⊢ ∀σ. evlis anil σ = anil`.
    pub fn evlis_nil(&self) -> Result<Thm> {
        let sg = Term::free("sg", self.val_ty.clone());
        self.nil_val_at(&self.ev_pd, false, &sg)?
            .all_intro("sg", self.val_ty.clone())
    }

    /// `⊢ ∀b σ. evlis (aatom b) σ = anil` — improper tails read as the
    /// empty argument list.
    pub fn evlis_atom(&self) -> Result<Thm> {
        let b = Term::free("b", acl2_payload());
        let sg = Term::free("sg", self.val_ty.clone());
        self.atom_val_at(&self.ev_pd, false, &b, &sg)?
            .all_intro("sg", self.val_ty.clone())?
            .all_intro("b", acl2_payload())
    }

    /// `⊢ ∀h t σ. evlis (acons h t) σ = acons (eval h σ) (evlis t σ)`.
    pub fn evlis_cons(&self) -> Result<Thm> {
        let h = Term::free("h", self.a());
        let t = Term::free("t", self.a());
        let sg = Term::free("sg", self.val_ty.clone());
        self.evlis_cons_at(&h, &t, &sg)?
            .all_intro("sg", self.val_ty.clone())?
            .all_intro("t", self.a())?
            .all_intro("h", self.a())
    }

    /// The primitive-application law for table row `k`:
    /// `⊢ ∀t σ. eval (acons ⌜F⌝ t) σ = f_model (car (evlis t σ)) …`
    /// (arity-many `car (cdr^i (evlis t σ))` arguments).
    pub fn eval_app(&self, k: usize) -> Result<Thm> {
        let row = self
            .rows
            .get(k)
            .ok_or_else(|| Error::ConnectiveRule(format!("acl2 eval_app: bad table row {k}")))?;
        let hk = self.th.asym_lit(row.sym.as_str().as_bytes())?;
        let t = Term::free("t", self.a());
        let sg = Term::free("sg", self.val_ty.clone());
        let acc = self.eval_cons_at(&hk, &t, &sg)?;
        self.fire_dispatch(acc, row.sym.as_str())?
            .all_intro("sg", self.val_ty.clone())?
            .all_intro("t", self.a())
    }

    /// The `IF` special-form law: `⊢ ∀t σ. eval (acons ⌜IF⌝ t) σ =
    /// aif (car vs) (car (cdr vs)) (car (cdr (cdr vs)))` at `vs := evlis t σ`
    /// (strict `aif` — semantically exact, the logic is total).
    pub fn eval_app_if(&self) -> Result<Thm> {
        let t = Term::free("t", self.a());
        let sg = Term::free("sg", self.val_ty.clone());
        let acc = self.eval_cons_at(&self.ifsym, &t, &sg)?;
        self.fire_dispatch(acc, "IF")?
            .all_intro("sg", self.val_ty.clone())?
            .all_intro("t", self.a())
    }

    // ------------------------------------------------------------------
    // Substitution computation laws (public, all closed)
    // ------------------------------------------------------------------

    /// `⊢ ∀s σs. subst (asym s) σs = σs s` — variables are replaced by
    /// their (term-encoding) image.
    pub fn subst_var(&self) -> Result<Thm> {
        let s = Term::free("s", Type::bytes());
        let ss = Term::free("ss", self.val_ty.clone());
        self.sym_val_at(&self.sev_pd, &s, &ss)?
            .all_intro("ss", self.val_ty.clone())?
            .all_intro("s", Type::bytes())
    }

    /// `⊢ ∀i σs. subst (aint i) σs = aint i`.
    pub fn subst_int(&self) -> Result<Thm> {
        let i = Term::free("i", Type::int());
        let ss = Term::free("ss", self.val_ty.clone());
        self.int_val_at(&self.sev_pd, &i, &ss)?
            .all_intro("ss", self.val_ty.clone())?
            .all_intro("i", Type::int())
    }

    /// `⊢ ∀σs. subst anil σs = anil`.
    pub fn subst_nil(&self) -> Result<Thm> {
        let ss = Term::free("ss", self.val_ty.clone());
        self.nil_val_at(&self.sev_pd, true, &ss)?
            .all_intro("ss", self.val_ty.clone())
    }

    /// `⊢ ∀t σs. subst (acons ⌜QUOTE⌝ t) σs = acons ⌜QUOTE⌝ t` — quoted
    /// forms are opaque.
    pub fn subst_quote(&self) -> Result<Thm> {
        let t = Term::free("t", self.a());
        let ss = Term::free("ss", self.val_ty.clone());
        let ge = Thm::refl(self.qsym.clone())?.eqt_intro()?;
        self.subst_cons_at(&self.qsym, &t, &ss)?
            .rhs_conv(|tm| tm.rw_all(&ge))?
            .rhs_conv(collapse_conds)?
            .all_intro("ss", self.val_ty.clone())?
            .all_intro("t", self.a())
    }

    /// `⊢ ∀h t σs. ¬(h = ⌜QUOTE⌝) ⟹ subst (acons h t) σs =
    /// acons h (lsubst t σs)` — application heads stay raw.
    pub fn subst_app(&self) -> Result<Thm> {
        let h = Term::free("h", self.a());
        let t = Term::free("t", self.a());
        let ss = Term::free("ss", self.val_ty.clone());
        let ng = h.clone().equals(self.qsym.clone())?.not()?;
        let gf = eqf_intro(Thm::assume(ng.clone())?)?;
        self.subst_cons_at(&h, &t, &ss)?
            .rhs_conv(|tm| tm.rw_all(&gf))?
            .rhs_conv(collapse_conds)?
            .imp_intro(&ng)?
            .all_intro("ss", self.val_ty.clone())?
            .all_intro("t", self.a())?
            .all_intro("h", self.a())
    }

    /// `⊢ ∀σs. lsubst anil σs = anil`.
    pub fn lsubst_nil(&self) -> Result<Thm> {
        let ss = Term::free("ss", self.val_ty.clone());
        self.nil_val_at(&self.sev_pd, false, &ss)?
            .all_intro("ss", self.val_ty.clone())
    }

    /// `⊢ ∀b σs. lsubst (aatom b) σs = anil`.
    pub fn lsubst_atom(&self) -> Result<Thm> {
        let b = Term::free("b", acl2_payload());
        let ss = Term::free("ss", self.val_ty.clone());
        self.atom_val_at(&self.sev_pd, false, &b, &ss)?
            .all_intro("ss", self.val_ty.clone())?
            .all_intro("b", acl2_payload())
    }

    /// `⊢ ∀h t σs. lsubst (acons h t) σs = acons (subst h σs) (lsubst t σs)`.
    pub fn lsubst_cons(&self) -> Result<Thm> {
        let h = Term::free("h", self.a());
        let t = Term::free("t", self.a());
        let ss = Term::free("ss", self.val_ty.clone());
        self.lsubst_cons_at(&h, &t, &ss)?
            .all_intro("ss", self.val_ty.clone())?
            .all_intro("t", self.a())?
            .all_intro("h", self.a())
    }

    // ------------------------------------------------------------------
    // subst_sema — semantic substitution (the S3 INST discharge)
    // ------------------------------------------------------------------

    /// The conjunctive `subst_sema` body at fixed `φ`, `σs`, `σ`:
    /// `eval (subst φ σs) σ = eval φ σ′ ∧ evlis (lsubst φ σs) σ = evlis φ σ′`
    /// with `σ′ := λv. eval (σs v) σ`.
    fn sema_conj(&self, phi: &Term, ss: &Term, sg: &Term) -> Result<Term> {
        let sp = self.sigma_comp(ss, sg)?;
        let c1 = self
            .eval
            .clone()
            .apply(self.subst.clone().apply(phi.clone())?.apply(ss.clone())?)?
            .apply(sg.clone())?
            .equals(self.eval.clone().apply(phi.clone())?.apply(sp.clone())?)?;
        let c2 = self
            .evlis
            .clone()
            .apply(self.lsubst.clone().apply(phi.clone())?.apply(ss.clone())?)?
            .apply(sg.clone())?
            .equals(self.evlis.clone().apply(phi.clone())?.apply(sp)?)?;
        c1.and(c2)
    }

    /// The induction motive `λφ. ∀σs σ. <sema_conj>`.
    fn sema_motive(&self) -> Result<Term> {
        let phi = Term::free("__phi", self.a());
        let ss = Term::free("__ms", self.val_ty.clone());
        let sg = Term::free("__mg", self.val_ty.clone());
        let q = self
            .sema_conj(&phi, &ss, &sg)?
            .forall("__mg", self.val_ty.clone())?
            .forall("__ms", self.val_ty.clone())?;
        Ok(Term::abs(self.a(), subst::close(&q, "__phi")))
    }

    /// **Semantic substitution** (the key S2 lemma — S3's INST rule
    /// discharge rests on it):
    ///
    /// ```text
    /// ⊢ ∀φ. ∀σs σ.  eval  (subst  φ σs) σ = eval  φ (λv. eval (σs v) σ)
    ///             ∧ evlis (lsubst φ σs) σ = evlis φ (λv. eval (σs v) σ)
    /// ```
    ///
    /// By carrier induction at the conjunctive motive: `coprod` cases in
    /// the atom case; ONE boolean split on `h = ⌜QUOTE⌝` in the cons case
    /// (the `F` branch reduces to the tail IH with no further guard
    /// firing — the raw-`t` argument only occurs in the discharged QUOTE
    /// branch).
    pub fn subst_sema(&self) -> Result<Thm> {
        let vt = self.val_ty.clone();
        let motive = self.sema_motive()?;
        let ss = Term::free("ss", vt.clone());
        let sg = Term::free("sg", vt.clone());
        let sp = self.sigma_comp(&ss, &sg)?;

        // Close ∀σ then ∀σs over a fixed-`σs σ` conjunction proof.
        let quantify = |conj: Thm| -> Result<Thm> {
            conj.all_intro("sg", vt.clone())?
                .all_intro("ss", vt.clone())
        };

        // ---- atom case (free `b`; payload split for the first component)
        let case_atom = {
            let b = Term::free("b", acl2_payload());
            let atom_b = self.th.atom.clone().apply(b.clone())?;

            // Second component — no split needed: both sides are `anil`.
            let second = self
                .atom_val_at(&self.sev_pd, false, &b, &ss)? // lsubst (aatom b) σs = anil
                .cong_arg(self.evlis.clone())?
                .cong_fn(sg.clone())? // evlis (lsubst (aatom b) σs) σ = evlis anil σ
                .trans(self.nil_val_at(&self.ev_pd, false, &sg)?)? // = anil
                .trans(self.atom_val_at(&self.ev_pd, false, &b, &sp)?.sym()?)?;

            // First component by `coprod` cases on the payload.
            let goal1 = self
                .eval
                .clone()
                .apply(
                    self.subst
                        .clone()
                        .apply(atom_b.clone())?
                        .apply(ss.clone())?,
                )?
                .apply(sg.clone())?
                .equals(self.eval.clone().apply(atom_b.clone())?.apply(sp.clone())?)?;
            let disj = coprod_cases(&Type::int(), &Type::bytes(), &b)?;
            let (dl, dr) = {
                let (or_l, r) = disj.concl().as_app().ok_or(Error::NotAnEquation)?;
                let (_, l) = or_l.as_app().ok_or(Error::NotAnEquation)?;
                (l.clone(), r.clone())
            };
            // One branch: under `b = inl w` / `b = inr w`, both sides
            // compute to the same value through the payload laws.
            let branch = |ex: &Term, is_int: bool| -> Result<Thm> {
                let pred = ex.as_app().ok_or(Error::NotAnEquation)?.1.clone();
                let (wname, wty) = if is_int {
                    ("__wi", Type::int())
                } else {
                    ("__ws", Type::bytes())
                };
                let w = Term::free(wname, wty.clone());
                let hyp = Term::app(pred.clone(), w.clone());
                let e = beta_reduce(Thm::assume(hyp.clone())?)?; // {hyp} ⊢ b = in{l,r} w
                let unfold = if is_int {
                    self.th.int_unfold(&w)?
                } else {
                    self.th.sym_unfold(&w)?
                };
                // {hyp} ⊢ aatom b = aint w / asym w.
                let ab_eq = e.cong_arg(self.th.atom.clone())?.trans(unfold.sym()?)?;
                let val_at = |pd: &ParaDef, s: &Term| -> Result<Thm> {
                    if is_int {
                        self.int_val_at(pd, &w, s)
                    } else {
                        self.sym_val_at(pd, &w, s)
                    }
                };
                // subst (aatom b) σs = <value or σs w>.
                let sub_eq = ab_eq
                    .clone()
                    .cong_arg(self.subst.clone())?
                    .cong_fn(ss.clone())?
                    .trans(val_at(&self.sev_pd, &ss)?)?;
                let lhs = sub_eq
                    .cong_arg(self.eval.clone())?
                    .cong_fn(sg.clone())?
                    .trans(if is_int {
                        self.int_val_at(&self.ev_pd, &w, &sg)?
                    } else {
                        // eval (σs w) σ is already the target — refl step.
                        Thm::refl(
                            self.eval
                                .clone()
                                .apply(ss.clone().apply(w.clone())?)?
                                .apply(sg.clone())?,
                        )?
                    })?;
                let rhs = ab_eq
                    .cong_arg(self.eval.clone())?
                    .cong_fn(sp.clone())?
                    .trans(val_at(&self.ev_pd, &sp)?)?;
                let g = lhs.trans(rhs.sym()?)?; // {hyp} ⊢ goal1
                let step = g.imp_intro(&hyp)?.all_intro(wname, wty)?;
                exists_elim(Thm::assume(ex.clone())?, goal1.clone(), step)?.imp_intro(ex)
            };
            let first = disj.or_elim(branch(&dl, true)?, branch(&dr, false)?)?;
            beta_expand(&motive, atom_b, quantify(first.and_intro(second)?)?)?
        };

        // ---- nil case
        let case_nil = {
            let first = self
                .nil_val_at(&self.sev_pd, true, &ss)? // subst anil σs = anil
                .cong_arg(self.eval.clone())?
                .cong_fn(sg.clone())?
                .trans(self.nil_val_at(&self.ev_pd, true, &sg)?)?
                .trans(self.nil_val_at(&self.ev_pd, true, &sp)?.sym()?)?;
            let second = self
                .nil_val_at(&self.sev_pd, false, &ss)?
                .cong_arg(self.evlis.clone())?
                .cong_fn(sg.clone())?
                .trans(self.nil_val_at(&self.ev_pd, false, &sg)?)?
                .trans(self.nil_val_at(&self.ev_pd, false, &sp)?.sym()?)?;
            beta_expand(
                &motive,
                self.th.nil.clone(),
                quantify(first.and_intro(second)?)?,
            )?
        };

        // ---- cons case (free `h`, `t`; IHs; ONE bool split on h = ⌜QUOTE⌝)
        let case_cons = {
            let h = Term::free("h", self.a());
            let t = Term::free("t", self.a());
            let acons_ht = self.acons_t(&h, &t)?;
            let ph = motive.clone().apply(h.clone())?;
            let pt = motive.clone().apply(t.clone())?;
            let open_ih = |p: &Term| -> Result<(Thm, Thm)> {
                beta_reduce(Thm::assume(p.clone())?)?
                    .all_elim(ss.clone())?
                    .all_elim(sg.clone())?
                    .conjuncts()
            };
            let (ih_h1, _) = open_ih(&ph)?; // {ph} ⊢ eval (subst h σs) σ = eval h σ′
            let (_, ih_t2) = open_ih(&pt)?; // {pt} ⊢ evlis (lsubst t σs) σ = evlis t σ′

            // subst h σs / lsubst t σs as terms.
            let x = self.subst.clone().apply(h.clone())?.apply(ss.clone())?;
            let y = self.lsubst.clone().apply(t.clone())?.apply(ss.clone())?;

            // Second component (guard-independent).
            let second = self
                .lsubst_cons_at(&h, &t, &ss)? // lsubst (acons h t) σs = acons X Y
                .cong_arg(self.evlis.clone())?
                .cong_fn(sg.clone())?
                .trans(self.evlis_cons_at(&x, &y, &sg)?)? // = acons (eval X σ) (evlis Y σ)
                .rhs_conv(|tm| tm.rw_all(&ih_h1))?
                .rhs_conv(|tm| tm.rw_all(&ih_t2))? // = acons (eval h σ′) (evlis t σ′)
                .trans(self.evlis_cons_at(&h, &t, &sp)?.sym()?)?;

            // First component: bool split on the QUOTE guard.
            let g = h.clone().equals(self.qsym.clone())?;
            let first_t = {
                let ge = Thm::assume(g.clone())?.eqt_intro()?; // {g} ⊢ g = ⌜T⌝
                let sc = self
                    .subst_cons_at(&h, &t, &ss)?
                    .rhs_conv(|tm| tm.rw_all(&ge))?
                    .rhs_conv(collapse_conds)?; // {g} ⊢ subst (acons h t) σs = acons h t
                let lhs = sc
                    .cong_arg(self.eval.clone())?
                    .cong_fn(sg.clone())?
                    .trans(self.eval_cons_at(&h, &t, &sg)?)?
                    .rhs_conv(|tm| tm.rw_all(&ge))?
                    .rhs_conv(collapse_conds)?; // {g} ⊢ … = car t
                let rhs = self
                    .eval_cons_at(&h, &t, &sp)?
                    .rhs_conv(|tm| tm.rw_all(&ge))?
                    .rhs_conv(collapse_conds)?; // {g} ⊢ eval (acons h t) σ′ = car t
                lhs.trans(rhs.sym()?)?.imp_intro(&g)?
            };
            let first_f = {
                let ng = g.clone().not()?;
                let gf = eqf_intro(Thm::assume(ng.clone())?)?; // {¬g} ⊢ g = ⌜F⌝
                let scf = self
                    .subst_cons_at(&h, &t, &ss)?
                    .rhs_conv(|tm| tm.rw_all(&gf))?
                    .rhs_conv(collapse_conds)?; // {¬g} ⊢ subst (acons h t) σs = acons h Y
                let lhs = scf
                    .cong_arg(self.eval.clone())?
                    .cong_fn(sg.clone())?
                    .trans(self.eval_cons_at(&h, &y, &sg)?)? // = dispatch(h, Y, evlis Y σ)
                    .rhs_conv(|tm| tm.rw_all(&gf))?
                    .rhs_conv(collapse_conds)? // QUOTE branch (the only raw-Y site) discarded
                    .rhs_conv(|tm| tm.rw_all(&ih_t2))?; // {¬g, pt} ⊢ … = S(h, evlis t σ′)
                let rhs = self
                    .eval_cons_at(&h, &t, &sp)?
                    .rhs_conv(|tm| tm.rw_all(&gf))?
                    .rhs_conv(collapse_conds)?; // {¬g} ⊢ eval (acons h t) σ′ = S(h, evlis t σ′)
                lhs.trans(rhs.sym()?)?.imp_intro(&ng)?
            };
            let first = Thm::lem(g)?.or_elim(first_t, first_f)?;

            beta_expand(&motive, acons_ht, quantify(first.and_intro(second)?)?)?
                .imp_intro(&pt)?
                .imp_intro(&ph)?
        };

        self.th
            .induct(&motive, vec![case_atom, case_nil, case_cons])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_hol_eval::mk_int;

    fn x() -> &'static Terms {
        terms().unwrap()
    }

    fn a() -> Type {
        x().th.ty.clone()
    }

    fn vt() -> Type {
        x().val_ty.clone()
    }

    fn ap1(f: &Term, u: &Term) -> Term {
        f.clone().apply(u.clone()).unwrap()
    }

    fn ap2(f: &Term, u: &Term, v: &Term) -> Term {
        f.clone()
            .apply(u.clone())
            .unwrap()
            .apply(v.clone())
            .unwrap()
    }

    fn acons(h: &Term, t: &Term) -> Term {
        ap2(&x().th.cons, h, t)
    }

    fn aint(i: i64) -> Term {
        x().th.aint_at(&mk_int(i)).unwrap()
    }

    /// Assert a closed theorem with an exact conclusion.
    fn check(thm: &Thm, expected: &Term) {
        assert!(thm.hyps().is_empty(), "must be closed: {thm}");
        assert_eq!(thm.concl(), expected);
    }

    /// The theory builds; the constants have the designed types; the
    /// encoders produce the designed carrier values.
    #[test]
    fn t_terms_build() {
        let tm = x();
        let pair_fn = Type::fun(a(), Type::fun(vt(), prod(a(), a())));
        let flat_fn = Type::fun(a(), Type::fun(vt(), a()));
        assert_eq!(tm.ev.type_of().unwrap(), pair_fn);
        assert_eq!(tm.sev.type_of().unwrap(), pair_fn);
        for c in [&tm.eval, &tm.evlis, &tm.subst, &tm.lsubst] {
            assert_eq!(c.type_of().unwrap(), flat_fn);
        }

        // Encoders: (QUOTE v), (CAR v), (EQUAL x y), (IMPLIES p q).
        let v = Term::free("v", a());
        let qv = tm.quote(&v).unwrap();
        assert_eq!(qv, acons(&tm.qsym, &acons(&v, &tm.th.nil)));
        let car_v = tm.app(b"CAR", &[v.clone()]).unwrap();
        assert_eq!(
            car_v,
            acons(&tm.sym(b"CAR").unwrap(), &acons(&v, &tm.th.nil))
        );
        let w = Term::free("w", a());
        assert_eq!(
            tm.mk_equal(&v, &w).unwrap(),
            acons(
                &tm.sym(b"EQUAL").unwrap(),
                &acons(&v, &acons(&w, &tm.th.nil))
            )
        );
        let qt = tm.quote(&tm.pr.t).unwrap();
        let qnil = tm.quote(&tm.th.nil).unwrap();
        assert_eq!(
            tm.mk_implies(&v, &w).unwrap(),
            tm.mk_if(&v, &tm.mk_if(&w, &qt, &qnil).unwrap(), &qt)
                .unwrap()
        );
    }

    /// **S2 gate (variable / constant / quoted-form evaluation):** the
    /// atom-level computation laws, closed with exact statements.
    #[test]
    fn t_eval_atom_laws() {
        let tm = x();
        let s = Term::free("s", Type::bytes());
        let sg = Term::free("sg", vt());

        // ⊢ ∀s σ. eval (asym s) σ = σ s.
        check(
            &tm.eval_var().unwrap(),
            &ap2(&tm.eval, &tm.th.asym_at(&s).unwrap(), &sg)
                .equals(ap1(&sg, &s))
                .unwrap()
                .forall("sg", vt())
                .unwrap()
                .forall("s", Type::bytes())
                .unwrap(),
        );

        // ⊢ ∀i σ. eval (aint i) σ = aint i.
        let i = Term::free("i", Type::int());
        let aint_i = tm.th.aint_at(&i).unwrap();
        check(
            &tm.eval_int().unwrap(),
            &ap2(&tm.eval, &aint_i, &sg)
                .equals(aint_i.clone())
                .unwrap()
                .forall("sg", vt())
                .unwrap()
                .forall("i", Type::int())
                .unwrap(),
        );

        // ⊢ ∀σ. eval anil σ = anil.
        check(
            &tm.eval_nil().unwrap(),
            &ap2(&tm.eval, &tm.th.nil, &sg)
                .equals(tm.th.nil.clone())
                .unwrap()
                .forall("sg", vt())
                .unwrap(),
        );

        // ⊢ ∀x σ. eval (q x) σ = x.
        let v = Term::free("x", a());
        check(
            &tm.eval_quote().unwrap(),
            &ap2(&tm.eval, &tm.quote(&v).unwrap(), &sg)
                .equals(v.clone())
                .unwrap()
                .forall("sg", vt())
                .unwrap()
                .forall("x", a())
                .unwrap(),
        );
    }

    /// The argument-list evaluation laws (`evlis`), closed and exact.
    #[test]
    fn t_evlis_laws() {
        let tm = x();
        let sg = Term::free("sg", vt());
        let nil = tm.th.nil.clone();

        check(
            &tm.evlis_nil().unwrap(),
            &ap2(&tm.evlis, &nil, &sg)
                .equals(nil.clone())
                .unwrap()
                .forall("sg", vt())
                .unwrap(),
        );

        let b = Term::free("b", acl2_payload());
        check(
            &tm.evlis_atom().unwrap(),
            &ap2(&tm.evlis, &ap1(&tm.th.atom, &b), &sg)
                .equals(nil.clone())
                .unwrap()
                .forall("sg", vt())
                .unwrap()
                .forall("b", acl2_payload())
                .unwrap(),
        );

        let (h, t) = (Term::free("h", a()), Term::free("t", a()));
        check(
            &tm.evlis_cons().unwrap(),
            &ap2(&tm.evlis, &acons(&h, &t), &sg)
                .equals(acons(&ap2(&tm.eval, &h, &sg), &ap2(&tm.evlis, &t, &sg)))
                .unwrap()
                .forall("sg", vt())
                .unwrap()
                .forall("t", a())
                .unwrap()
                .forall("h", a())
                .unwrap(),
        );
    }

    /// **S2 gate (application evaluation laws):** one `eval_app` law per
    /// primitive-table row, plus the `IF` special form — all closed, all
    /// with the exact arity-projected statement.
    #[test]
    fn t_eval_app_laws() {
        let tm = x();
        let t = Term::free("t", a());
        let sg = Term::free("sg", vt());
        let vs = ap2(&tm.evlis, &t, &sg);

        for (k, row) in tm.pr.table().iter().enumerate() {
            let mut rhs = row.model.clone();
            for i in 0..row.arity {
                rhs = rhs.apply(tm.arg_at(&vs, i).unwrap()).unwrap();
            }
            let lhs = ap2(
                &tm.eval,
                &acons(&tm.sym(row.sym.as_bytes()).unwrap(), &t),
                &sg,
            );
            check(
                &tm.eval_app(k).unwrap(),
                &lhs.equals(rhs)
                    .unwrap()
                    .forall("sg", vt())
                    .unwrap()
                    .forall("t", a())
                    .unwrap(),
            );
        }

        // IF: strict aif over the three projected arguments.
        let aif_rhs = tm
            .pr
            .aif
            .clone()
            .apply(tm.arg_at(&vs, 0).unwrap())
            .unwrap()
            .apply(tm.arg_at(&vs, 1).unwrap())
            .unwrap()
            .apply(tm.arg_at(&vs, 2).unwrap())
            .unwrap();
        check(
            &tm.eval_app_if().unwrap(),
            &ap2(&tm.eval, &acons(&tm.ifsym, &t), &sg)
                .equals(aif_rhs)
                .unwrap()
                .forall("sg", vt())
                .unwrap()
                .forall("t", a())
                .unwrap(),
        );
    }

    // ------------------------------------------------------------------
    // Ground evaluation (test-local chaining of the public laws)
    // ------------------------------------------------------------------

    /// `⊢ car/cdr (acons h t) = h/t` fired at every spine node — the
    /// projection collapse for ground values.
    fn proj_step(node: &Term) -> Option<Thm> {
        let tm = x();
        let (f, arg) = node.as_app()?;
        let take_cdr = if *f == tm.th.car {
            false
        } else if *f == tm.th.cdr {
            true
        } else {
            return None;
        };
        let (ch, tail) = arg.as_app()?;
        let (c, h) = ch.as_app()?;
        if *c != tm.th.cons {
            return None;
        }
        tm.th.cs.proj_scons(take_cdr, h, tail).ok()
    }

    /// `⊢ evlis t σ = <value list>` for a nil-terminated encoded list.
    fn evlis_g(t: &Term, sg: &Term) -> Thm {
        let tm = x();
        if *t == tm.th.nil {
            return tm.evlis_nil().unwrap().all_elim(sg.clone()).unwrap();
        }
        let (ch, tail) = t.as_app().unwrap();
        let (_, head) = ch.as_app().unwrap();
        let step = tm
            .evlis_cons()
            .unwrap()
            .all_elim(head.clone())
            .unwrap()
            .all_elim(tail.clone())
            .unwrap()
            .all_elim(sg.clone())
            .unwrap();
        let he = eval_g(head, sg);
        let te = evlis_g(tail, sg);
        step.rhs_conv(|u| u.rw_all(&he))
            .unwrap()
            .rhs_conv(|u| u.rw_all(&te))
            .unwrap()
    }

    /// `⊢ eval φ σ = value` for the quoted/primitive ground fragment.
    fn eval_g(phi: &Term, sg: &Term) -> Thm {
        let tm = x();
        let (ch, targ) = phi.as_app().unwrap();
        let (_, head) = ch.as_app().unwrap();
        if *head == tm.qsym {
            let (cv, _) = targ.as_app().unwrap();
            let (_, v) = cv.as_app().unwrap();
            return tm
                .eval_quote()
                .unwrap()
                .all_elim(v.clone())
                .unwrap()
                .all_elim(sg.clone())
                .unwrap();
        }
        let k = tm
            .pr
            .table()
            .iter()
            .position(|r| tm.sym(r.sym.as_bytes()).unwrap() == *head)
            .expect("eval_g: head not in the primitive table");
        let law = tm
            .eval_app(k)
            .unwrap()
            .all_elim(targ.clone())
            .unwrap()
            .all_elim(sg.clone())
            .unwrap();
        let vs_eq = evlis_g(targ, sg);
        law.rhs_conv(|u| u.rw_all(&vs_eq))
            .unwrap()
            .rhs_conv(|u| crate::init::ext::fire_all(u, &proj_step))
            .unwrap()
    }

    /// **S2 gate (ground evaluation):** `⊢ eval ⌜(CAR (CONS '1 '2))⌝ σ =
    /// aint 1` with `σ` a *free* valuation, computed by chaining the
    /// `eval_app` laws + `eval_quote` + the carrier projections.
    #[test]
    fn t_eval_ground() {
        let tm = x();
        let sg = Term::free("sg", vt());
        let inner = tm
            .app(
                b"CONS",
                &[tm.quote(&aint(1)).unwrap(), tm.quote(&aint(2)).unwrap()],
            )
            .unwrap();
        let phi = tm.app(b"CAR", &[inner.clone()]).unwrap();

        // Intermediate: the CONS form evaluates to the pair value.
        let cons_val = eval_g(&inner, &sg);
        check(
            &cons_val,
            &ap2(&tm.eval, &inner, &sg)
                .equals(acons(&aint(1), &aint(2)))
                .unwrap(),
        );

        // The full form: ⊢ eval ⌜(CAR (CONS '1 '2))⌝ σ = aint 1.
        let thm = eval_g(&phi, &sg);
        check(&thm, &ap2(&tm.eval, &phi, &sg).equals(aint(1)).unwrap());
    }

    /// The substitution computation laws, closed and exact.
    #[test]
    fn t_subst_laws() {
        let tm = x();
        let ss = Term::free("ss", vt());
        let nil = tm.th.nil.clone();

        // ⊢ ∀s σs. subst (asym s) σs = σs s.
        let s = Term::free("s", Type::bytes());
        check(
            &tm.subst_var().unwrap(),
            &ap2(&tm.subst, &tm.th.asym_at(&s).unwrap(), &ss)
                .equals(ap1(&ss, &s))
                .unwrap()
                .forall("ss", vt())
                .unwrap()
                .forall("s", Type::bytes())
                .unwrap(),
        );

        // ⊢ ∀i σs. subst (aint i) σs = aint i.
        let i = Term::free("i", Type::int());
        let aint_i = tm.th.aint_at(&i).unwrap();
        check(
            &tm.subst_int().unwrap(),
            &ap2(&tm.subst, &aint_i, &ss)
                .equals(aint_i.clone())
                .unwrap()
                .forall("ss", vt())
                .unwrap()
                .forall("i", Type::int())
                .unwrap(),
        );

        // ⊢ ∀σs. subst anil σs = anil / lsubst anil σs = anil.
        check(
            &tm.subst_nil().unwrap(),
            &ap2(&tm.subst, &nil, &ss)
                .equals(nil.clone())
                .unwrap()
                .forall("ss", vt())
                .unwrap(),
        );
        check(
            &tm.lsubst_nil().unwrap(),
            &ap2(&tm.lsubst, &nil, &ss)
                .equals(nil.clone())
                .unwrap()
                .forall("ss", vt())
                .unwrap(),
        );

        // ⊢ ∀b σs. lsubst (aatom b) σs = anil.
        let b = Term::free("b", acl2_payload());
        check(
            &tm.lsubst_atom().unwrap(),
            &ap2(&tm.lsubst, &ap1(&tm.th.atom, &b), &ss)
                .equals(nil.clone())
                .unwrap()
                .forall("ss", vt())
                .unwrap()
                .forall("b", acl2_payload())
                .unwrap(),
        );

        // ⊢ ∀t σs. subst (acons ⌜QUOTE⌝ t) σs = acons ⌜QUOTE⌝ t.
        let t = Term::free("t", a());
        check(
            &tm.subst_quote().unwrap(),
            &ap2(&tm.subst, &acons(&tm.qsym, &t), &ss)
                .equals(acons(&tm.qsym, &t))
                .unwrap()
                .forall("ss", vt())
                .unwrap()
                .forall("t", a())
                .unwrap(),
        );

        // ⊢ ∀h t σs. ¬(h = ⌜QUOTE⌝) ⟹ subst (acons h t) σs = acons h (lsubst t σs).
        let h = Term::free("h", a());
        check(
            &tm.subst_app().unwrap(),
            &h.clone()
                .equals(tm.qsym.clone())
                .unwrap()
                .not()
                .unwrap()
                .imp(
                    ap2(&tm.subst, &acons(&h, &t), &ss)
                        .equals(acons(&h, &ap2(&tm.lsubst, &t, &ss)))
                        .unwrap(),
                )
                .unwrap()
                .forall("ss", vt())
                .unwrap()
                .forall("t", a())
                .unwrap()
                .forall("h", a())
                .unwrap(),
        );

        // ⊢ ∀h t σs. lsubst (acons h t) σs = acons (subst h σs) (lsubst t σs).
        check(
            &tm.lsubst_cons().unwrap(),
            &ap2(&tm.lsubst, &acons(&h, &t), &ss)
                .equals(acons(&ap2(&tm.subst, &h, &ss), &ap2(&tm.lsubst, &t, &ss)))
                .unwrap()
                .forall("ss", vt())
                .unwrap()
                .forall("t", a())
                .unwrap()
                .forall("h", a())
                .unwrap(),
        );
    }

    /// **S2 gate (ground substitution):** `⊢ subst ⌜(EQUAL X X)⌝ σs =
    /// ⌜(EQUAL (QUOTE v) (QUOTE v))⌝` for a concrete finite `σs` (nested
    /// `cond` on names with identity default `λn. asym n`).
    #[test]
    fn t_subst_ground() {
        let tm = x();
        let v = Term::free("v", a());
        let qv = tm.quote(&v).unwrap();
        let xname = covalence_hol_eval::mk_blob(covalence_types::Bytes::from(b"X".to_vec()));

        // σs := λn. cond (n = ⌜X⌝) (q v) (asym n).
        let ssig = {
            let n = Term::free("__n", Type::bytes());
            let body = cond(a())
                .apply(n.clone().equals(xname.clone()).unwrap())
                .unwrap()
                .apply(qv.clone())
                .unwrap()
                .apply(tm.th.asym_at(&n).unwrap())
                .unwrap();
            Term::abs(Type::bytes(), subst::close(&body, "__n"))
        };

        // subst (asym ⌜X⌝) σs = q v  (variable hit).
        let var_hit = tm
            .subst_var()
            .unwrap()
            .all_elim(xname.clone())
            .unwrap()
            .all_elim(ssig.clone())
            .unwrap()
            .rhs_conv(|u| u.reduce())
            .unwrap()
            .rhs_conv(collapse_conds)
            .unwrap();
        check(
            &var_hit,
            &ap2(&tm.subst, &tm.sym(b"X").unwrap(), &ssig)
                .equals(qv.clone())
                .unwrap(),
        );

        // The whole form.
        let sym_x = tm.sym(b"X").unwrap();
        let args = tm.listn(&[sym_x.clone(), sym_x.clone()]).unwrap();
        let phi = tm.mk_equal(&sym_x, &sym_x).unwrap();
        let ne = tm.th.sym_ne(b"EQUAL", b"QUOTE").unwrap();
        let s1 = tm
            .subst_app()
            .unwrap()
            .all_elim(tm.sym(b"EQUAL").unwrap())
            .unwrap()
            .all_elim(args.clone())
            .unwrap()
            .all_elim(ssig.clone())
            .unwrap()
            .imp_elim(ne)
            .unwrap(); // subst φ σs = acons ⌜EQUAL⌝ (lsubst args σs)

        // lsubst args σs = acons (q v) (acons (q v) anil).
        let rest = acons(&sym_x, &tm.th.nil);
        let inner = tm
            .lsubst_cons()
            .unwrap()
            .all_elim(sym_x.clone())
            .unwrap()
            .all_elim(tm.th.nil.clone())
            .unwrap()
            .all_elim(ssig.clone())
            .unwrap()
            .rhs_conv(|u| u.rw_all(&var_hit))
            .unwrap()
            .rhs_conv(|u| u.rw_all(&tm.lsubst_nil().unwrap().all_elim(ssig.clone()).unwrap()))
            .unwrap(); // lsubst (acons ⌜X⌝ anil) σs = acons (q v) anil
        let outer = tm
            .lsubst_cons()
            .unwrap()
            .all_elim(sym_x.clone())
            .unwrap()
            .all_elim(rest)
            .unwrap()
            .all_elim(ssig.clone())
            .unwrap()
            .rhs_conv(|u| u.rw_all(&var_hit))
            .unwrap()
            .rhs_conv(|u| u.rw_all(&inner))
            .unwrap(); // lsubst args σs = acons (q v) (acons (q v) anil)

        let full = s1.rhs_conv(|u| u.rw_all(&outer)).unwrap();
        check(
            &full,
            &ap2(&tm.subst, &phi, &ssig)
                .equals(tm.mk_equal(&qv, &qv).unwrap())
                .unwrap(),
        );
    }

    /// **S2 gate (the priority deliverable):** semantic substitution —
    /// closed, with the design's exact conjunctive ∀-statement.
    #[test]
    fn t_subst_sema() {
        let tm = x();
        let lemma = tm.subst_sema().unwrap();
        assert!(lemma.hyps().is_empty(), "subst_sema must be closed");

        // Rebuild the exact expected statement independently.
        let phi = Term::free("p0", a());
        let ss = Term::free("s1", vt());
        let sg = Term::free("s2", vt());
        let sp = {
            let n = Term::free("__v0", Type::bytes());
            let body = ap2(&tm.eval, &ap1(&ss, &n), &sg);
            Term::abs(Type::bytes(), subst::close(&body, "__v0"))
        };
        let c1 = ap2(&tm.eval, &ap2(&tm.subst, &phi, &ss), &sg)
            .equals(ap2(&tm.eval, &phi, &sp))
            .unwrap();
        let c2 = ap2(&tm.evlis, &ap2(&tm.lsubst, &phi, &ss), &sg)
            .equals(ap2(&tm.evlis, &phi, &sp))
            .unwrap();
        let conj = c1.and(c2).unwrap();
        let motive = {
            let q = conj
                .clone()
                .forall("s2", vt())
                .unwrap()
                .forall("s1", vt())
                .unwrap();
            Term::abs(a(), subst::close(&q, "p0"))
        };
        // The induction conclusion is the (η-expanded) `∀φ. motive φ`.
        let expected = ap1(&motive, &phi).forall("p0", a()).unwrap();
        assert_eq!(lemma.concl(), &expected);

        // Instantiated, β-reduced form: exactly the designed conjunction.
        let inst = beta_reduce(lemma.all_elim(phi.clone()).unwrap()).unwrap();
        let inst = inst
            .all_elim(ss.clone())
            .unwrap()
            .all_elim(sg.clone())
            .unwrap();
        assert_eq!(inst.concl(), &conj);
        assert!(inst.hyps().is_empty());
    }
}
