//! **S5 — ordinals below ε₀ over the ACL2 model carrier.**
//!
//! Design: `notes/vibes/lisp/acl2-s5-design.md`. ACL2's ordinal notations
//! ARE conses; `o-p` and `o<` are **carrier functions** (`t`/`nil`-valued,
//! usable inside object terms), defined here as total HOL functions over
//! the S0 carrier — no fuel, no `cv_exists`, no new recursion machinery:
//!
//! - the depth-2 `caar` descent of ACL2's `o<`/`o-p` is dissolved by the
//!   S2 **pair-valued paramorphism trick** — the recursion computes the
//!   pair *(value at `x`, value at `car x`)* (`OLT : A → (A→A) × (A→A)`,
//!   `OP : A → A × A`), with the pointwise **folding lemmas**
//!   `olt_snd` / `op_snd` proved by carrier case analysis (no induction);
//! - ACL2's defining equations for `O<` / `O-P` (§1.2 of the design, the
//!   "ordinal axioms as model theorems") are proved by case analysis over
//!   both arguments ([`Ordinals::olt_def`] / [`Ordinals::op_def`]);
//! - a ground normaliser ([`Ordinals::ord_fold`]) computes
//!   `o-p`/`o<`/`natp`/`posp`/`o-first-expt`/… on constructor-literal
//!   values (the o-p/o< analogue of `defun_ground` — do **not** feed
//!   these heads to `defun::fold_ground`);
//! - the **accessibility predicate** `Acc` (impredicative least
//!   predicate) with its three rules; the "below ω" theorem
//!   [`Ordinals::l0_finite_wf`] (`⊢ ∀i:int. 0 ≤ i ⟹ Acc (aint i)`)
//!   through the `nat ↪ int` bridge
//!   ([`crate::init::int::int_nonneg_nat`] etc.) and the
//!   [`nonneg_si_on`] strong-induction driver;
//! - **well-foundedness at full ε₀**: [`Ordinals::wf`]
//!   (`⊢ ∀x. ¬(o-p x = anil) ⟹ Acc x`, all CNF notations — the classic
//!   triple-nested induction: `main_ord` over the first exponent's
//!   accessibility ⊃ coefficient strong induction ⊃ inner accessibility
//!   induction on the rest, then `graded_wf` by nat induction on tower
//!   height) and the extracted induction principle [`Ordinals::wf_induct`].
//!
//! Everything is a derived theorem over existing kernel rules; nothing
//! here is trusted, no axiom is postulated. Open work (IND-ORD, env
//! rows, the S5 axiom pack) is tracked in this directory's `SKELETONS.md`.

use std::sync::LazyLock;

use covalence_core::{Error, Result, Term, Type, subst};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::derived::DerivedRules;
use covalence_hol_eval::{fal_from_lit, mk_int};

use smol_str::SmolStr;

use crate::init::acl2::carrier::{Acl2, acl2_payload};
use crate::init::acl2::derivable::{
    Acl2Env, AxiomRow, Discharge, UserRow, install_user_rows, model_eq_target, model_holds_target,
    model_implies_target,
};
use crate::init::acl2::prims::{Prims, eqf_intro, prims};
use crate::init::acl2::term::Terms;
use crate::init::coprod::{cases as coprod_cases, inl, inr};
use crate::init::eq::{beta_expand, beta_reduce};
use crate::init::ext::{TermExt, ThmExt};
use crate::init::inductive::carved::apply_def;
use crate::init::int;
use crate::init::logic::{exists_elim, exists_intro};
use crate::init::prod::{fst, fst_pair, pair, prod, snd, snd_pair};

/// Split a `⊢ C = body` definition into `(C, the equation)`.
fn defined(name: &str, body: Term) -> Result<(Term, Thm)> {
    let eq = Thm::define(name, body)?;
    let c = eq.concl().as_eq().ok_or(Error::NotAnEquation)?.0.clone();
    Ok((c, eq))
}

fn ap1(f: &Term, x: &Term) -> Result<Term> {
    f.clone().apply(x.clone())
}

fn ap2(f: &Term, x: &Term, y: &Term) -> Result<Term> {
    f.clone().apply(x.clone())?.apply(y.clone())
}

/// A pair-valued paramorphic (or catamorphic) definition over the
/// carrier: the constant, its defining equation, the exact step terms
/// (law derivation re-runs `prec_eq` against them), the pair component
/// types, and the recursor result type `prod l r`.
struct Para {
    con: Term,
    def_eq: Thm,
    steps: [Term; 3],
    /// Left/right pair component types.
    lty: Type,
    rty: Type,
    /// `prod lty rty`.
    beta: Type,
}

/// The S5 ordinal theory over the ACL2 model. Built exactly once
/// ([`ordinals`]).
pub struct Ordinals {
    /// The S1 primitive theory.
    pub pr: &'static Prims,
    /// The S0 carrier theory.
    pub th: &'static Acl2,
    /// `natp : A → A`.
    pub natp: Term,
    natp_eq: Thm,
    /// `posp : A → A`.
    pub posp: Term,
    posp_eq: Thm,
    /// `ofe : A → A` (ACL2 `O-FIRST-EXPT`).
    pub ofe: Term,
    ofe_eq: Thm,
    /// `ofc : A → A` (ACL2 `O-FIRST-COEFF`).
    pub ofc: Term,
    ofc_eq: Thm,
    /// `ors : A → A` (ACL2 `O-RST`).
    pub ors: Term,
    ors_eq: Thm,
    /// `olt : A → A → A` (ACL2 `O<`) — `λx y. fst (OLT x) y`.
    pub olt: Term,
    olt_eq: Thm,
    olt_p: Para,
    /// `op : A → A` (ACL2 `O-P`) — `λx. fst (OP x)`.
    pub op: Term,
    op_eq: Thm,
    op_p: Para,
    /// `ht : A → nat` — the tower height (HOL-level only, the §6.4
    /// grading; never an env row).
    pub ht: Term,
    ht_eq: Thm,
    ht_p: Para,
    /// `below : A → A → bool` — `R y x := ¬(op y = anil) ∧ ¬(olt y x = anil)`.
    pub below: Term,
    below_eq: Thm,
    /// `acc : A → bool` — the impredicative accessibility predicate.
    pub acc: Term,
    acc_eq: Thm,
}

/// The process-global S5 ordinal theory.
pub fn ordinals() -> Result<&'static Ordinals> {
    static ORD: LazyLock<std::result::Result<Ordinals, String>> =
        LazyLock::new(|| Ordinals::build().map_err(|e| e.to_string()));
    ORD.as_ref()
        .map_err(|e| Error::ConnectiveRule(format!("acl2 ordinals build failed: {e}")))
}

impl Ordinals {
    fn build() -> Result<Ordinals> {
        let pr = prims()?;
        let th = pr.th;
        let a = th.ty.clone();
        let anil = th.nil.clone();
        let a0 = th.aint_at(&mk_int(0i64))?;

        let lam = |name: &str, body: &Term| Term::abs(a.clone(), subst::close(body, name));
        let x = Term::free("__x", a.clone());
        let aif3 = |c: &Term, y: &Term, z: &Term| -> Result<Term> {
            pr.aif
                .clone()
                .apply(c.clone())?
                .apply(y.clone())?
                .apply(z.clone())
        };

        // natp := λx. aif (aintp x) (aif (alt x '0) anil t) anil.
        let (natp, natp_eq) = {
            let inner = aif3(&ap2(&pr.lt, &x, &a0)?, &anil, &pr.t)?;
            let body = aif3(&ap1(&pr.intp, &x)?, &inner, &anil)?;
            defined("acl2.ord.natp", lam("__x", &body))?
        };
        // posp := λx. aif (aintp x) (alt '0 x) anil.
        let (posp, posp_eq) = {
            let body = aif3(&ap1(&pr.intp, &x)?, &ap2(&pr.lt, &a0, &x)?, &anil)?;
            defined("acl2.ord.posp", lam("__x", &body))?
        };
        // ofe := λx. aif (aconsp x) (car (car x)) '0.
        let (ofe, ofe_eq) = {
            let caar = ap1(&th.car, &ap1(&th.car, &x)?)?;
            let body = aif3(&ap1(&pr.consp, &x)?, &caar, &a0)?;
            defined("acl2.ord.o-first-expt", lam("__x", &body))?
        };
        // ofc := λx. aif (aconsp x) (cdr (car x)) x.
        let (ofc, ofc_eq) = {
            let cdar = ap1(&th.cdr, &ap1(&th.car, &x)?)?;
            let body = aif3(&ap1(&pr.consp, &x)?, &cdar, &x)?;
            defined("acl2.ord.o-first-coeff", lam("__x", &body))?
        };
        // ors := λx. cdr x.
        let (ors, ors_eq) = defined("acl2.ord.o-rst", lam("__x", &ap1(&th.cdr, &x)?))?;

        // ---- OLT : A → prod (A→A) (A→A), intended (o< x ·, o< (car x) ·).
        let faa = Type::fun(a.clone(), a.clone());
        let olt_beta = prod(faa.clone(), faa.clone());
        let pair_ff = pair(faa.clone(), faa.clone());
        let fst_ff = fst(faa.clone(), faa.clone());
        let snd_ff = snd(faa.clone(), faa.clone());
        // arm(v) := λy. aif (aconsp y) t (alt v y) — the o< value at a
        // non-cons left argument `v`.
        let arm = |v: &Term| -> Result<Term> {
            let y = Term::free("__y", a.clone());
            let body = aif3(&ap1(&pr.consp, &y)?, &pr.t, &ap2(&pr.lt, v, &y)?)?;
            Ok(Term::abs(a.clone(), subst::close(&body, "__y")))
        };
        let arm_nil = arm(&anil)?;
        let olt_steps: [Term; 3] = {
            // atom step: λl. pair (arm (aatom l)) (arm anil).
            let sa = {
                let l = Term::free("__l", acl2_payload());
                let atom_l = ap1(&th.atom, &l)?;
                let body = pair_ff
                    .clone()
                    .apply(arm(&atom_l)?)?
                    .apply(arm_nil.clone())?;
                Term::abs(acl2_payload(), subst::close(&body, "__l"))
            };
            // nil step: pair (arm anil) (arm anil).
            let sn = pair_ff
                .clone()
                .apply(arm_nil.clone())?
                .apply(arm_nil.clone())?;
            // cons step: λh t oh ot. pair D (fst oh).
            let sc = {
                let h = Term::free("__h", a.clone());
                let _t = Term::free("__t", a.clone());
                let oh = Term::free("__oh", olt_beta.clone());
                let ot = Term::free("__ot", olt_beta.clone());
                let y = Term::free("__y", a.clone());
                let car_y = ap1(&th.car, &y)?;
                let caar_y = ap1(&th.car, &car_y)?;
                let cdar_y = ap1(&th.cdr, &car_y)?;
                let coeff_ne = ap2(&pr.lt, &ap1(&th.cdr, &h)?, &cdar_y)?;
                let rest = fst_ff.clone().apply(ot.clone())?.apply(ap1(&th.cdr, &y)?)?;
                let coeff = aif3(
                    &ap2(&pr.equal, &ap1(&th.cdr, &h)?, &cdar_y)?,
                    &rest,
                    &coeff_ne,
                )?;
                let expt_ne = snd_ff.clone().apply(oh.clone())?.apply(caar_y.clone())?;
                let expt = aif3(
                    &ap2(&pr.equal, &ap1(&th.car, &h)?, &caar_y)?,
                    &coeff,
                    &expt_ne,
                )?;
                let d_body = aif3(&ap1(&pr.consp, &y)?, &expt, &anil)?;
                let d = Term::abs(a.clone(), subst::close(&d_body, "__y"));
                let body = pair_ff
                    .clone()
                    .apply(d)?
                    .apply(fst_ff.clone().apply(oh.clone())?)?;
                let l_ot = Term::abs(olt_beta.clone(), subst::close(&body, "__ot"));
                let l_oh = Term::abs(olt_beta.clone(), subst::close(&l_ot, "__oh"));
                let l_t = Term::abs(a.clone(), subst::close(&l_oh, "__t"));
                Term::abs(a.clone(), subst::close(&l_t, "__h"))
            };
            [sa, sn, sc]
        };
        let (olt_rec, olt_rec_eq) =
            defined("acl2.ord.o-lt-rec", th.cs.prec(&olt_steps, &olt_beta)?)?;
        let olt_p = Para {
            con: olt_rec.clone(),
            def_eq: olt_rec_eq,
            steps: olt_steps,
            lty: faa.clone(),
            rty: faa.clone(),
            beta: olt_beta.clone(),
        };
        // olt := λx y. fst (OLT x) y.
        let (olt, olt_eq) = {
            let y = Term::free("__y", a.clone());
            let body = fst_ff.clone().apply(ap1(&olt_rec, &x)?)?.apply(y.clone())?;
            let l_y = Term::abs(a.clone(), subst::close(&body, "__y"));
            defined("acl2.ord.o-lt", lam("__x", &l_y))?
        };

        // ---- OP : A → prod A A, intended (o-p x, o-p (car x)).
        let op_beta = prod(a.clone(), a.clone());
        let pair_aa = pair(a.clone(), a.clone());
        let fst_aa = fst(a.clone(), a.clone());
        let snd_aa = snd(a.clone(), a.clone());
        let natp_nil = ap1(&natp, &anil)?;
        let op_steps: [Term; 3] = {
            let sa = {
                let l = Term::free("__l", acl2_payload());
                let atom_l = ap1(&th.atom, &l)?;
                let body = pair_aa
                    .clone()
                    .apply(ap1(&natp, &atom_l)?)?
                    .apply(natp_nil.clone())?;
                Term::abs(acl2_payload(), subst::close(&body, "__l"))
            };
            let sn = pair_aa
                .clone()
                .apply(natp_nil.clone())?
                .apply(natp_nil.clone())?;
            let sc = {
                let h = Term::free("__h", a.clone());
                let t = Term::free("__t", a.clone());
                let ph = Term::free("__ph", op_beta.clone());
                let pt = Term::free("__pt", op_beta.clone());
                let car_h = ap1(&th.car, &h)?;
                let cdr_h = ap1(&th.cdr, &h)?;
                // aif (fst pt) (olt (ofe t) (car h)) anil.
                let rec_ok = aif3(
                    &fst_aa.clone().apply(pt.clone())?,
                    &ap2(&olt, &ap1(&ofe, &t)?, &car_h)?,
                    &anil,
                )?;
                let posp_ck = aif3(&ap1(&posp, &cdr_h)?, &rec_ok, &anil)?;
                let zero_ck = aif3(&ap2(&pr.equal, &car_h, &a0)?, &anil, &posp_ck)?;
                let expt_ok = aif3(&snd_aa.clone().apply(ph.clone())?, &zero_ck, &anil)?;
                let c = aif3(&ap1(&pr.consp, &h)?, &expt_ok, &anil)?;
                let body = pair_aa
                    .clone()
                    .apply(c)?
                    .apply(fst_aa.clone().apply(ph.clone())?)?;
                let l_pt = Term::abs(op_beta.clone(), subst::close(&body, "__pt"));
                let l_ph = Term::abs(op_beta.clone(), subst::close(&l_pt, "__ph"));
                let l_t = Term::abs(a.clone(), subst::close(&l_ph, "__t"));
                Term::abs(a.clone(), subst::close(&l_t, "__h"))
            };
            [sa, sn, sc]
        };
        let (op_rec, op_rec_eq) = defined("acl2.ord.o-p-rec", th.cs.prec(&op_steps, &op_beta)?)?;
        let op_p = Para {
            con: op_rec.clone(),
            def_eq: op_rec_eq,
            steps: op_steps,
            lty: a.clone(),
            rty: a.clone(),
            beta: op_beta.clone(),
        };
        // op := λx. fst (OP x).
        let (op, op_eq) = defined(
            "acl2.ord.o-p",
            lam("__x", &fst_aa.clone().apply(ap1(&op_rec, &x)?)?),
        )?;

        // ---- HP : A → prod nat nat, intended (ht x, ht (car x)).
        let nt = Type::nat();
        let ht_beta = prod(nt.clone(), nt.clone());
        let pair_nn = pair(nt.clone(), nt.clone());
        let fst_nn = fst(nt.clone(), nt.clone());
        let snd_nn = snd(nt.clone(), nt.clone());
        let zero = crate::init::nat::zero();
        let ht_steps: [Term; 3] = {
            let pair00 = pair_nn.clone().apply(zero.clone())?.apply(zero.clone())?;
            let sa = Term::abs(acl2_payload(), pair00.clone());
            let sn = pair00;
            let sc = {
                let _h = Term::free("__h", a.clone());
                let _t = Term::free("__t", a.clone());
                let ph = Term::free("__ph", ht_beta.clone());
                let _pt = Term::free("__pt", ht_beta.clone());
                let body = pair_nn
                    .clone()
                    .apply(crate::init::nat::succ(snd_nn.clone().apply(ph.clone())?))?
                    .apply(fst_nn.clone().apply(ph.clone())?)?;
                let l_pt = Term::abs(ht_beta.clone(), subst::close(&body, "__pt"));
                let l_ph = Term::abs(ht_beta.clone(), subst::close(&l_pt, "__ph"));
                let l_t = Term::abs(a.clone(), subst::close(&l_ph, "__t"));
                Term::abs(a.clone(), subst::close(&l_t, "__h"))
            };
            [sa, sn, sc]
        };
        let (ht_rec, ht_rec_eq) = defined("acl2.ord.ht-rec", th.cs.prec(&ht_steps, &ht_beta)?)?;
        let ht_p = Para {
            con: ht_rec.clone(),
            def_eq: ht_rec_eq,
            steps: ht_steps,
            lty: nt.clone(),
            rty: nt.clone(),
            beta: ht_beta.clone(),
        };
        let (ht, ht_eq) = defined(
            "acl2.ord.ht",
            lam("__x", &fst_nn.clone().apply(ap1(&ht_rec, &x)?)?),
        )?;

        // ---- R (below) and Acc.
        // below := λy x. ¬(op y = anil) ∧ ¬(olt y x = anil).
        let (below, below_eq) = {
            let y = Term::free("__by", a.clone());
            let xx = Term::free("__bx", a.clone());
            let c1 = ap1(&op, &y)?.equals(anil.clone())?.not()?;
            let c2 = ap2(&olt, &y, &xx)?.equals(anil.clone())?.not()?;
            let body = c1.and(c2)?;
            let l_x = Term::abs(a.clone(), subst::close(&body, "__bx"));
            defined(
                "acl2.ord.below",
                Term::abs(a.clone(), subst::close(&l_x, "__by")),
            )?
        };
        // acc := λx. ∀S. (∀z. (∀y. below y z ⟹ S y) ⟹ S z) ⟹ S x.
        let (acc, acc_eq) = {
            let sb = Type::fun(a.clone(), Type::bool());
            let s = Term::free("__aS", sb.clone());
            let xv = Term::free("__ax", a.clone());
            let zv = Term::free("__az", a.clone());
            let yv = Term::free("__ay", a.clone());
            let prem_y = ap2(&below, &yv, &zv)?
                .imp(s.clone().apply(yv.clone())?)?
                .forall("__ay", a.clone())?;
            let step = prem_y
                .imp(s.clone().apply(zv.clone())?)?
                .forall("__az", a.clone())?;
            let body = step
                .imp(s.clone().apply(xv.clone())?)?
                .forall("__aS", sb.clone())?;
            defined(
                "acl2.ord.acc",
                Term::abs(a.clone(), subst::close(&body, "__ax")),
            )?
        };

        Ok(Ordinals {
            pr,
            th,
            natp,
            natp_eq,
            posp,
            posp_eq,
            ofe,
            ofe_eq,
            ofc,
            ofc_eq,
            ors,
            ors_eq,
            olt,
            olt_eq,
            olt_p,
            op,
            op_eq,
            op_p,
            ht,
            ht_eq,
            ht_p,
            below,
            below_eq,
            acc,
            acc_eq,
        })
    }

    // ------------------------------------------------------------------
    // Small builders
    // ------------------------------------------------------------------

    fn a(&self) -> Type {
        self.th.ty.clone()
    }

    fn avar(&self, n: &str) -> Term {
        Term::free(n, self.a())
    }

    fn anil(&self) -> Term {
        self.th.nil.clone()
    }

    fn a0(&self) -> Result<Term> {
        self.th.aint_at(&mk_int(0i64))
    }

    fn acons_t(&self, h: &Term, t: &Term) -> Result<Term> {
        ap2(&self.th.cons, h, t)
    }

    // ------------------------------------------------------------------
    // `aif` firing + rewrite plumbing
    // ------------------------------------------------------------------

    /// Fire the outermost `aif` of `acc`'s RHS whose guard is literally
    /// `t` or `anil` (via the proved `if_t` / `if_nil`). Errors if the
    /// RHS is not such an `aif`.
    fn fire_if(&self, acc: Thm) -> Result<Thm> {
        let bad = || Error::ConnectiveRule("acl2 ord fire_if: RHS is not a fireable aif".into());
        let rhs = acc.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
        let (cy, z) = rhs.as_app().ok_or_else(bad)?;
        let (cc, y) = cy.as_app().ok_or_else(bad)?;
        let (hd, c) = cc.as_app().ok_or_else(bad)?;
        if *hd != self.pr.aif {
            return Err(bad());
        }
        if *c == self.pr.t {
            let law = self
                .pr
                .if_t()?
                .all_elim(self.pr.t.clone())?
                .all_elim(y.clone())?
                .all_elim(z.clone())?
                .imp_elim(self.pr.t_ne_nil()?)?;
            acc.trans(law)
        } else if *c == self.anil() {
            let law = self.pr.if_nil()?.all_elim(y.clone())?.all_elim(z.clone())?;
            acc.trans(law)
        } else {
            Err(bad())
        }
    }

    /// Fire outermost `aif`s while their guards are literal `t`/`anil`.
    fn fire_ifs(&self, mut acc: Thm) -> Result<Thm> {
        loop {
            match self.fire_if(acc.clone()) {
                Ok(next) => acc = next,
                Err(_) => return Ok(acc),
            }
        }
    }

    /// Rewrite `acc`'s RHS with each equation in turn (all occurrences).
    fn rw_rhs(&self, mut acc: Thm, eqs: &[&Thm]) -> Result<Thm> {
        for eq in eqs {
            acc = acc.rhs_conv(|tm| tm.rw_all(eq))?;
        }
        Ok(acc)
    }

    // ------------------------------------------------------------------
    // Simple-constant laws (at fixed terms)
    // ------------------------------------------------------------------

    /// `⊢ aconsp (acons h t) = t` at fixed terms.
    fn consp_cons_at(&self, h: &Term, t: &Term) -> Result<Thm> {
        self.pr
            .consp_cons()?
            .all_elim(h.clone())?
            .all_elim(t.clone())
    }

    /// `⊢ aconsp (aint i) = anil` at a fixed `int` term.
    fn consp_int_at(&self, i: &Term) -> Result<Thm> {
        let wrapped = inl(Type::int(), Type::bytes()).apply(i.clone())?;
        self.th
            .int_unfold(i)?
            .cong_arg(self.pr.consp.clone())?
            .trans(self.pr.consp_atom()?.all_elim(wrapped)?)
    }

    /// `⊢ aconsp (asym s) = anil` at a fixed `bytes` term.
    fn consp_sym_at(&self, s: &Term) -> Result<Thm> {
        let wrapped = inr(Type::int(), Type::bytes()).apply(s.clone())?;
        self.th
            .sym_unfold(s)?
            .cong_arg(self.pr.consp.clone())?
            .trans(self.pr.consp_atom()?.all_elim(wrapped)?)
    }

    /// `⊢ ofe (acons h t) = car h` at fixed terms.
    pub fn ofe_cons_at(&self, h: &Term, t: &Term) -> Result<Thm> {
        let ht = self.acons_t(h, t)?;
        let acc = apply_def(&self.ofe_eq, &[ht.clone()])?;
        let acc = self.rw_rhs(acc, &[&self.consp_cons_at(h, t)?])?;
        let acc = self.fire_if(acc)?; // = car (car (acons h t))
        self.rw_rhs(acc, &[&self.th.cs.proj_scons(false, h, t)?]) // = car h
    }

    /// `⊢ ofe v = aint 0` for a **non-cons** `v`, given
    /// `cv : ⊢ aconsp v = anil`.
    fn ofe_noncons_at(&self, v: &Term, cv: &Thm) -> Result<Thm> {
        let acc = apply_def(&self.ofe_eq, std::slice::from_ref(v))?;
        self.fire_if(self.rw_rhs(acc, &[cv])?)
    }

    /// `⊢ ofc (acons h t) = cdr h` at fixed terms.
    pub fn ofc_cons_at(&self, h: &Term, t: &Term) -> Result<Thm> {
        let ht = self.acons_t(h, t)?;
        let acc = apply_def(&self.ofc_eq, &[ht.clone()])?;
        let acc = self.rw_rhs(acc, &[&self.consp_cons_at(h, t)?])?;
        let acc = self.fire_if(acc)?; // = cdr (car (acons h t))
        self.rw_rhs(acc, &[&self.th.cs.proj_scons(false, h, t)?]) // = cdr h
    }

    /// `⊢ ors x = cdr x` at a fixed term.
    pub fn ors_at(&self, x: &Term) -> Result<Thm> {
        apply_def(&self.ors_eq, std::slice::from_ref(x))
    }

    /// `⊢ ors (acons h t) = t` at fixed terms.
    pub fn ors_cons_at(&self, h: &Term, t: &Term) -> Result<Thm> {
        let ht = self.acons_t(h, t)?;
        self.ors_at(&ht)?.trans(self.th.cs.proj_scons(true, h, t)?)
    }

    /// `⊢ natp (aint i) = aif (alt (aint i) '0) anil t` at a fixed `int`
    /// term (the integer branch, guard fired).
    fn natp_int_at(&self, i: &Term) -> Result<Thm> {
        let ai = self.th.aint_at(i)?;
        let acc = apply_def(&self.natp_eq, &[ai])?;
        let acc = self.rw_rhs(acc, &[&self.pr.intp_int()?.all_elim(i.clone())?])?;
        self.fire_if(acc)
    }

    /// `⊢ natp v = anil` for a non-integer `v`, given
    /// `iv : ⊢ aintp v = anil`.
    fn natp_nonint_at(&self, v: &Term, iv: &Thm) -> Result<Thm> {
        let acc = apply_def(&self.natp_eq, std::slice::from_ref(v))?;
        self.fire_if(self.rw_rhs(acc, &[iv])?)
    }

    /// `⊢ posp (aint i) = alt '0 (aint i)` at a fixed `int` term.
    fn posp_int_at(&self, i: &Term) -> Result<Thm> {
        let ai = self.th.aint_at(i)?;
        let acc = apply_def(&self.posp_eq, &[ai])?;
        let acc = self.rw_rhs(acc, &[&self.pr.intp_int()?.all_elim(i.clone())?])?;
        self.fire_if(acc)
    }

    // ------------------------------------------------------------------
    // Paramorphism plumbing
    // ------------------------------------------------------------------

    /// `⊢ CON (aatom b) = <atom step at b, reduced>` (a pair value).
    fn para_atom(&self, p: &Para, b: &Term) -> Result<Thm> {
        let atom_b = ap1(&self.th.atom, b)?;
        p.def_eq
            .clone()
            .cong_fn(atom_b)?
            .trans(
                self.th
                    .cs
                    .prec_eq(&p.steps, 0, &p.beta)?
                    .all_elim(b.clone())?,
            )?
            .reduce_rhs()
    }

    /// `⊢ CON anil = <nil step>`.
    fn para_nil(&self, p: &Para) -> Result<Thm> {
        p.def_eq
            .clone()
            .cong_fn(self.anil())?
            .trans(self.th.cs.prec_eq(&p.steps, 1, &p.beta)?)
    }

    /// `⊢ CON (acons h t) = <cons step, images folded back to CON,
    /// reduced>` (a pair value mentioning `CON h` / `CON t`).
    fn para_cons(&self, p: &Para, h: &Term, t: &Term) -> Result<Thm> {
        let ht = self.acons_t(h, t)?;
        p.def_eq
            .clone()
            .cong_fn(ht)?
            .trans(
                self.th
                    .cs
                    .prec_eq(&p.steps, 2, &p.beta)?
                    .all_elim(h.clone())?
                    .all_elim(t.clone())?,
            )?
            .rhs_conv(|tm| tm.rw_all(&p.def_eq.clone().sym()?))?
            .reduce_rhs()
    }

    /// Project a pair law `⊢ CON X = pair D L` through `fst`/`snd`:
    /// `⊢ fst (CON X) = D` (resp. `snd`/`L`).
    fn para_proj(&self, p: &Para, law: &Thm, first: bool) -> Result<Thm> {
        let rhs = law.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
        let (pair_d, l) = rhs.as_app().ok_or(Error::NotAnEquation)?;
        let (_, d) = pair_d.as_app().ok_or(Error::NotAnEquation)?;
        let proj = if first {
            fst(p.lty.clone(), p.rty.clone())
        } else {
            snd(p.lty.clone(), p.rty.clone())
        };
        let clause = if first {
            fst_pair(&p.lty, &p.rty, d, l)?
        } else {
            snd_pair(&p.lty, &p.rty, d, l)?
        };
        law.clone().cong_arg(proj)?.trans(clause)
    }

    // ------------------------------------------------------------------
    // `olt` per-constructor laws (at fixed terms)
    // ------------------------------------------------------------------

    /// `⊢ olt x y = fst (OLT x) y` at fixed terms.
    fn olt_unfold_at(&self, x: &Term, y: &Term) -> Result<Thm> {
        apply_def(&self.olt_eq, &[x.clone(), y.clone()])
    }

    /// `⊢ olt (aatom b) y = aif (aconsp y) t (alt (aatom b) y)`.
    pub fn olt_atom_at(&self, b: &Term, y: &Term) -> Result<Thm> {
        let atom_b = ap1(&self.th.atom, b)?;
        let proj = self.para_proj(&self.olt_p, &self.para_atom(&self.olt_p, b)?, true)?;
        self.olt_unfold_at(&atom_b, y)?
            .rhs_conv(|tm| tm.rw_all(&proj))?
            .reduce_rhs()
    }

    /// `⊢ olt anil y = aif (aconsp y) t (alt anil y)`.
    pub fn olt_nil_at(&self, y: &Term) -> Result<Thm> {
        let proj = self.para_proj(&self.olt_p, &self.para_nil(&self.olt_p)?, true)?;
        self.olt_unfold_at(&self.anil(), y)?
            .rhs_conv(|tm| tm.rw_all(&proj))?
            .reduce_rhs()
    }

    /// `⊢ olt (aint i) y = aif (aconsp y) t (alt (aint i) y)` — the atom
    /// law routed through the payload constructor.
    pub fn olt_int_at(&self, i: &Term, y: &Term) -> Result<Thm> {
        let unfold = self.th.int_unfold(i)?; // aint i = aatom (inl i)
        let wrapped = inl(Type::int(), Type::bytes()).apply(i.clone())?;
        unfold
            .clone()
            .cong_arg(self.olt.clone())?
            .cong_fn(y.clone())?
            .trans(self.olt_atom_at(&wrapped, y)?)?
            .rhs_conv(|tm| tm.rw_all(&unfold.sym()?))
    }

    /// `⊢ olt (asym s) y = aif (aconsp y) t (alt (asym s) y)`.
    pub fn olt_sym_at(&self, s: &Term, y: &Term) -> Result<Thm> {
        let unfold = self.th.sym_unfold(s)?;
        let wrapped = inr(Type::int(), Type::bytes()).apply(s.clone())?;
        unfold
            .clone()
            .cong_arg(self.olt.clone())?
            .cong_fn(y.clone())?
            .trans(self.olt_atom_at(&wrapped, y)?)?
            .rhs_conv(|tm| tm.rw_all(&unfold.sym()?))
    }

    /// `⊢ snd (OLT x) y = olt (car x) y` at fixed terms — THE folding
    /// lemma (by carrier case analysis on `x`; no induction).
    fn olt_snd_at(&self, x: &Term, y: &Term) -> Result<Thm> {
        let goal = snd(self.olt_p.lty.clone(), self.olt_p.rty.clone())
            .apply(ap1(&self.olt_p.con, x)?)?
            .apply(y.clone())?
            .equals(ap2(&self.olt, &ap1(&self.th.car, x)?, y)?)?;
        let snd_ff = snd(self.olt_p.lty.clone(), self.olt_p.rty.clone());
        // Shared leaf logic: from `e : x = LEAF` with `⊢ car LEAF = anil`
        // and the leaf's snd-projection = arm(anil).
        let leaf = |e: &Thm, snd_proj: Thm, car_leaf: Thm| -> Result<Thm> {
            // snd (OLT x) y = snd (OLT LEAF) y = arm(anil) y (β) = aif … .
            let lhs = e
                .clone()
                .cong_arg(self.olt_p.con.clone())?
                .cong_arg(snd_ff.clone())?
                .cong_fn(y.clone())?
                .rhs_conv(|tm| tm.rw_all(&snd_proj))?
                .reduce_rhs()?;
            // olt (car x) y = olt anil y = aif … (the same value).
            let rhs = e
                .clone()
                .cong_arg(self.th.car.clone())?
                .trans(car_leaf)?
                .cong_arg(self.olt.clone())?
                .cong_fn(y.clone())?
                .trans(self.olt_nil_at(y)?)?;
            lhs.trans(rhs.sym()?)
        };
        self.by_cases(
            x,
            &goal,
            "os",
            &|b, e| {
                leaf(
                    e,
                    self.para_proj(&self.olt_p, &self.para_atom(&self.olt_p, b)?, false)?,
                    self.pr.car_atom()?.all_elim(b.clone())?,
                )
            },
            &|e| {
                leaf(
                    e,
                    self.para_proj(&self.olt_p, &self.para_nil(&self.olt_p)?, false)?,
                    self.pr.car_nil()?,
                )
            },
            &|h, t, e| {
                // snd (OLT (acons h t)) = fst (OLT h); applied to y and
                // folded back through olt's definition.
                let lhs = e
                    .clone()
                    .cong_arg(self.olt_p.con.clone())?
                    .cong_arg(snd_ff.clone())?
                    .cong_fn(y.clone())?
                    .rhs_conv(|tm| {
                        tm.rw_all(&self.para_proj(
                            &self.olt_p,
                            &self.para_cons(&self.olt_p, h, t)?,
                            false,
                        )?)
                    })? // = fst (OLT h) y
                    .rhs_conv(|tm| tm.rw_all(&self.olt_unfold_at(h, y)?.sym()?))?; // = olt h y
                let rhs = e
                    .clone()
                    .cong_arg(self.th.car.clone())?
                    .trans(self.th.cs.proj_scons(false, h, t)?)? // car x = h
                    .cong_arg(self.olt.clone())?
                    .cong_fn(y.clone())?; // olt (car x) y = olt h y
                lhs.trans(rhs.sym()?)
            },
        )
    }

    /// `⊢ olt (acons h t) y = aif (aconsp y) (aif (aequal (car h)
    /// (car (car y))) (aif (aequal (cdr h) (cdr (car y))) (olt t (cdr y))
    /// (alt (cdr h) (cdr (car y)))) (olt (car h) (car (car y)))) anil` —
    /// the fully-folded cons law.
    pub fn olt_cons_at(&self, h: &Term, t: &Term, y: &Term) -> Result<Thm> {
        let ht = self.acons_t(h, t)?;
        let proj = self.para_proj(&self.olt_p, &self.para_cons(&self.olt_p, h, t)?, true)?;
        let acc = self
            .olt_unfold_at(&ht, y)?
            .rhs_conv(|tm| tm.rw_all(&proj))?
            .reduce_rhs()?;
        // Fold `fst (OLT t) (cdr y)` → `olt t (cdr y)` and
        // `snd (OLT h) (car (car y))` → `olt (car h) (car (car y))`.
        let cdr_y = ap1(&self.th.cdr, y)?;
        let caar_y = ap1(&self.th.car, &ap1(&self.th.car, y)?)?;
        let acc = acc.rhs_conv(|tm| tm.rw_all(&self.olt_unfold_at(t, &cdr_y)?.sym()?))?;
        acc.rhs_conv(|tm| tm.rw_all(&self.olt_snd_at(h, &caar_y)?))
    }

    // ------------------------------------------------------------------
    // `op` per-constructor laws
    // ------------------------------------------------------------------

    /// `⊢ op x = fst (OP x)` at a fixed term.
    fn op_unfold_at(&self, x: &Term) -> Result<Thm> {
        apply_def(&self.op_eq, std::slice::from_ref(x))
    }

    /// `⊢ op (aatom b) = natp (aatom b)`.
    pub fn op_atom_at(&self, b: &Term) -> Result<Thm> {
        let atom_b = ap1(&self.th.atom, b)?;
        let proj = self.para_proj(&self.op_p, &self.para_atom(&self.op_p, b)?, true)?;
        self.op_unfold_at(&atom_b)?.trans(proj)
    }

    /// `⊢ op anil = natp anil`.
    pub fn op_nil_at(&self) -> Result<Thm> {
        let proj = self.para_proj(&self.op_p, &self.para_nil(&self.op_p)?, true)?;
        self.op_unfold_at(&self.anil())?.trans(proj)
    }

    /// `⊢ op (aint i) = natp (aint i)` (through the payload constructor).
    pub fn op_int_at(&self, i: &Term) -> Result<Thm> {
        let unfold = self.th.int_unfold(i)?;
        let wrapped = inl(Type::int(), Type::bytes()).apply(i.clone())?;
        unfold
            .clone()
            .cong_arg(self.op.clone())?
            .trans(self.op_atom_at(&wrapped)?)?
            .rhs_conv(|tm| tm.rw_all(&unfold.sym()?))
    }

    /// `⊢ op (asym s) = natp (asym s)`.
    pub fn op_sym_at(&self, s: &Term) -> Result<Thm> {
        let unfold = self.th.sym_unfold(s)?;
        let wrapped = inr(Type::int(), Type::bytes()).apply(s.clone())?;
        unfold
            .clone()
            .cong_arg(self.op.clone())?
            .trans(self.op_atom_at(&wrapped)?)?
            .rhs_conv(|tm| tm.rw_all(&unfold.sym()?))
    }

    /// `⊢ snd (OP x) = op (car x)` at a fixed term — the `op` folding
    /// lemma (case analysis, no induction).
    fn op_snd_at(&self, x: &Term) -> Result<Thm> {
        let snd_aa = snd(self.op_p.lty.clone(), self.op_p.rty.clone());
        let goal = snd_aa
            .clone()
            .apply(ap1(&self.op_p.con, x)?)?
            .equals(ap1(&self.op, &ap1(&self.th.car, x)?)?)?;
        let leaf = |e: &Thm, snd_proj: Thm, car_leaf: Thm| -> Result<Thm> {
            let lhs = e
                .clone()
                .cong_arg(self.op_p.con.clone())?
                .cong_arg(snd_aa.clone())?
                .trans(snd_proj)?; // snd (OP x) = natp anil
            let rhs = e
                .clone()
                .cong_arg(self.th.car.clone())?
                .trans(car_leaf)? // car x = anil
                .cong_arg(self.op.clone())?
                .trans(self.op_nil_at()?)?; // op (car x) = natp anil
            lhs.trans(rhs.sym()?)
        };
        self.by_cases(
            x,
            &goal,
            "ps",
            &|b, e| {
                leaf(
                    e,
                    self.para_proj(&self.op_p, &self.para_atom(&self.op_p, b)?, false)?,
                    self.pr.car_atom()?.all_elim(b.clone())?,
                )
            },
            &|e| {
                leaf(
                    e,
                    self.para_proj(&self.op_p, &self.para_nil(&self.op_p)?, false)?,
                    self.pr.car_nil()?,
                )
            },
            &|h, t, e| {
                let lhs = e
                    .clone()
                    .cong_arg(self.op_p.con.clone())?
                    .cong_arg(snd_aa.clone())?
                    .trans(self.para_proj(
                        &self.op_p,
                        &self.para_cons(&self.op_p, h, t)?,
                        false,
                    )?)? // snd (OP x) = fst (OP h)
                    .trans(self.op_unfold_at(h)?.sym()?)?; // = op h
                let rhs = e
                    .clone()
                    .cong_arg(self.th.car.clone())?
                    .trans(self.th.cs.proj_scons(false, h, t)?)? // car x = h
                    .cong_arg(self.op.clone())?; // op (car x) = op h
                lhs.trans(rhs.sym()?)
            },
        )
    }

    /// `⊢ op (acons h t) = aif (aconsp h) (aif (op (car h)) (aif (aequal
    /// (car h) '0) anil (aif (posp (cdr h)) (aif (op t) (olt (ofe t)
    /// (car h)) anil) anil)) anil) anil` — the fully-folded cons law.
    pub fn op_cons_at(&self, h: &Term, t: &Term) -> Result<Thm> {
        let ht = self.acons_t(h, t)?;
        let proj = self.para_proj(&self.op_p, &self.para_cons(&self.op_p, h, t)?, true)?;
        let acc = self.op_unfold_at(&ht)?.trans(proj)?;
        // Fold `fst (OP t)` → `op t` and `snd (OP h)` → `op (car h)`.
        let acc = acc.rhs_conv(|tm| tm.rw_all(&self.op_unfold_at(t)?.sym()?))?;
        acc.rhs_conv(|tm| tm.rw_all(&self.op_snd_at(h)?))
    }

    // ------------------------------------------------------------------
    // `ht` laws
    // ------------------------------------------------------------------

    /// `⊢ ht x = fst (HP x)` at a fixed term.
    fn ht_unfold_at(&self, x: &Term) -> Result<Thm> {
        apply_def(&self.ht_eq, std::slice::from_ref(x))
    }

    /// `⊢ ht (aatom b) = 0`.
    pub fn ht_atom_at(&self, b: &Term) -> Result<Thm> {
        let atom_b = ap1(&self.th.atom, b)?;
        let proj = self.para_proj(&self.ht_p, &self.para_atom(&self.ht_p, b)?, true)?;
        self.ht_unfold_at(&atom_b)?.trans(proj)
    }

    /// `⊢ ht anil = 0`.
    pub fn ht_nil_at(&self) -> Result<Thm> {
        let proj = self.para_proj(&self.ht_p, &self.para_nil(&self.ht_p)?, true)?;
        self.ht_unfold_at(&self.anil())?.trans(proj)
    }

    /// `⊢ snd (HP x) = ht (car x)` — the `ht` folding lemma.
    fn ht_snd_at(&self, x: &Term) -> Result<Thm> {
        let snd_nn = snd(self.ht_p.lty.clone(), self.ht_p.rty.clone());
        let goal = snd_nn
            .clone()
            .apply(ap1(&self.ht_p.con, x)?)?
            .equals(ap1(&self.ht, &ap1(&self.th.car, x)?)?)?;
        let leaf = |e: &Thm, snd_proj: Thm, car_leaf: Thm| -> Result<Thm> {
            let lhs = e
                .clone()
                .cong_arg(self.ht_p.con.clone())?
                .cong_arg(snd_nn.clone())?
                .trans(snd_proj)?; // snd (HP x) = 0
            let rhs = e
                .clone()
                .cong_arg(self.th.car.clone())?
                .trans(car_leaf)?
                .cong_arg(self.ht.clone())?
                .trans(self.ht_nil_at()?)?; // ht (car x) = 0
            lhs.trans(rhs.sym()?)
        };
        self.by_cases(
            x,
            &goal,
            "hs",
            &|b, e| {
                leaf(
                    e,
                    self.para_proj(&self.ht_p, &self.para_atom(&self.ht_p, b)?, false)?,
                    self.pr.car_atom()?.all_elim(b.clone())?,
                )
            },
            &|e| {
                leaf(
                    e,
                    self.para_proj(&self.ht_p, &self.para_nil(&self.ht_p)?, false)?,
                    self.pr.car_nil()?,
                )
            },
            &|h, t, e| {
                let lhs = e
                    .clone()
                    .cong_arg(self.ht_p.con.clone())?
                    .cong_arg(snd_nn.clone())?
                    .trans(self.para_proj(
                        &self.ht_p,
                        &self.para_cons(&self.ht_p, h, t)?,
                        false,
                    )?)? // snd (HP x) = fst (HP h)
                    .trans(self.ht_unfold_at(h)?.sym()?)?; // = ht h
                let rhs = e
                    .clone()
                    .cong_arg(self.th.car.clone())?
                    .trans(self.th.cs.proj_scons(false, h, t)?)?
                    .cong_arg(self.ht.clone())?; // ht (car x) = ht h
                lhs.trans(rhs.sym()?)
            },
        )
    }

    /// `⊢ ht (acons h t) = succ (ht (car h))`.
    pub fn ht_cons_at(&self, h: &Term, t: &Term) -> Result<Thm> {
        let ht_ = self.acons_t(h, t)?;
        let proj = self.para_proj(&self.ht_p, &self.para_cons(&self.ht_p, h, t)?, true)?;
        self.ht_unfold_at(&ht_)?
            .trans(proj)? // = succ (snd (HP h))
            .rhs_conv(|tm| tm.rw_all(&self.ht_snd_at(h)?))
    }

    // ------------------------------------------------------------------
    // Carrier case analysis (the shared driver)
    // ------------------------------------------------------------------

    /// Prove `goal` (a `bool` term possibly mentioning the free `x`) by
    /// carrier case analysis on `x`. Each case receives the equation
    /// theorem for its shape (hypotheses propagate and are discharged by
    /// the driver). Fresh names are `__c<tag>b` / `__c<tag>h` /
    /// `__c<tag>t` — `goal` must not mention them.
    pub(crate) fn by_cases(
        &self,
        x: &Term,
        goal: &Term,
        tag: &str,
        atom_case: &dyn Fn(&Term, &Thm) -> Result<Thm>,
        nil_case: &dyn Fn(&Thm) -> Result<Thm>,
        cons_case: &dyn Fn(&Term, &Term, &Thm) -> Result<Thm>,
    ) -> Result<Thm> {
        let bad = || Error::ConnectiveRule("acl2 ord by_cases: bad cases disjunction".into());
        let disj = beta_reduce(self.th.cases()?.all_elim(x.clone())?)?;
        let (or_d0, rest) = disj.concl().as_app().ok_or_else(bad)?;
        let (_, d0) = or_d0.as_app().ok_or_else(bad)?;
        let (or_d1, d2) = rest.as_app().ok_or_else(bad)?;
        let (_, d1) = or_d1.as_app().ok_or_else(bad)?;
        let (d0, d1, d2, rest) = (d0.clone(), d1.clone(), d2.clone(), rest.clone());

        // atom branch: ∃b. x = aatom b.
        let br_atom = {
            let pred = d0.as_app().ok_or_else(bad)?.1.clone();
            let bname = format!("__c{tag}b");
            let w = Term::free(&bname, acl2_payload());
            let hyp = Term::app(pred, w.clone());
            let e = beta_reduce(Thm::assume(hyp.clone())?)?; // {hyp} ⊢ x = aatom w
            let g = atom_case(&w, &e)?;
            let step = g.imp_intro(&hyp)?.all_intro(&bname, acl2_payload())?;
            exists_elim(Thm::assume(d0.clone())?, goal.clone(), step)?.imp_intro(&d0)?
        };
        // nil branch.
        let br_nil = nil_case(&Thm::assume(d1.clone())?)?.imp_intro(&d1)?;
        // cons branch: ∃h t. x = acons h t.
        let br_cons = {
            let pred0 = d2.as_app().ok_or_else(bad)?.1.clone();
            let hname = format!("__c{tag}h");
            let tname = format!("__c{tag}t");
            let hh = Term::free(&hname, self.a());
            let hyp0 = Term::app(pred0, hh.clone());
            let inner_ex = beta_reduce(Thm::assume(hyp0.clone())?)?; // {hyp0} ⊢ ∃t. x = acons hh t
            let pred1 = inner_ex.concl().as_app().ok_or_else(bad)?.1.clone();
            let tt = Term::free(&tname, self.a());
            let hyp1 = Term::app(pred1, tt.clone());
            let e = beta_reduce(Thm::assume(hyp1.clone())?)?; // {hyp1} ⊢ x = acons hh tt
            let g = cons_case(&hh, &tt, &e)?;
            let step1 = g.imp_intro(&hyp1)?.all_intro(&tname, self.a())?;
            let g2 = exists_elim(inner_ex, goal.clone(), step1)?;
            let step0 = g2.imp_intro(&hyp0)?.all_intro(&hname, self.a())?;
            exists_elim(Thm::assume(d2.clone())?, goal.clone(), step0)?.imp_intro(&d2)?
        };
        let right = Thm::assume(rest.clone())?
            .or_elim(br_nil, br_cons)?
            .imp_intro(&rest)?;
        disj.or_elim(br_atom, right)
    }

    // ------------------------------------------------------------------
    // The ACL2 defining equations (design §1.2 / §2.2 — the "ordinal
    // axioms as model theorems")
    // ------------------------------------------------------------------

    /// The `O-P` defining-equation RHS at `x`.
    fn op_rhs(&self, x: &Term) -> Result<Term> {
        let aif3 = |c: &Term, y: &Term, z: &Term| -> Result<Term> {
            self.pr
                .aif
                .clone()
                .apply(c.clone())?
                .apply(y.clone())?
                .apply(z.clone())
        };
        let anil = self.anil();
        let a0 = self.a0()?;
        let fe = ap1(&self.ofe, x)?;
        let fc = ap1(&self.ofc, x)?;
        let rs = ap1(&self.ors, x)?;
        let rec_ok = aif3(
            &ap1(&self.op, &rs)?,
            &ap2(&self.olt, &ap1(&self.ofe, &rs)?, &fe)?,
            &anil,
        )?;
        let posp_ck = aif3(&ap1(&self.posp, &fc)?, &rec_ok, &anil)?;
        let zero_ck = aif3(&ap2(&self.pr.equal, &fe, &a0)?, &anil, &posp_ck)?;
        let expt_ok = aif3(&ap1(&self.op, &fe)?, &zero_ck, &anil)?;
        let car_ck = aif3(
            &ap1(&self.pr.consp, &ap1(&self.th.car, x)?)?,
            &expt_ok,
            &anil,
        )?;
        aif3(&ap1(&self.pr.consp, x)?, &car_ck, &ap1(&self.natp, x)?)
    }

    /// **ACL2's `O-P` defining equation as a model theorem**
    /// (design §1.2): `⊢ ∀x. op x = <the normalized O-P body over
    /// ofe/ofc/ors/natp/posp/olt>`. By carrier case analysis.
    pub fn op_def(&self) -> Result<Thm> {
        let x = self.avar("x");
        let goal = ap1(&self.op, &x)?.equals(self.op_rhs(&x)?)?;
        // Transport an at-constructor equation along `e : x = CTOR`.
        let transport =
            |e: &Thm, eq_ctor: Thm| -> Result<Thm> { goal.rw_all(e)?.sym()?.eq_mp(eq_ctor) };
        let thm = self.by_cases(
            &x,
            &goal,
            "od",
            &|b, e| {
                let atom_b = ap1(&self.th.atom, b)?;
                let lhs = self.op_atom_at(b)?; // op (aatom b) = natp (aatom b)
                let rhs = Thm::refl(self.op_rhs(&atom_b)?)?;
                let rhs = self.rw_rhs(rhs, &[&self.pr.consp_atom()?.all_elim(b.clone())?])?;
                let rhs = self.fire_if(rhs)?; // RHS(aatom b) = natp (aatom b)
                transport(e, lhs.trans(rhs.sym()?)?)
            },
            &|e| {
                let lhs = self.op_nil_at()?;
                let rhs = Thm::refl(self.op_rhs(&self.anil())?)?;
                let rhs = self.rw_rhs(rhs, &[&self.pr.consp_nil()?])?;
                let rhs = self.fire_if(rhs)?;
                transport(e, lhs.trans(rhs.sym()?)?)
            },
            &|h, t, e| {
                let ht = self.acons_t(h, t)?;
                let lhs = self.op_cons_at(h, t)?;
                let rhs = Thm::refl(self.op_rhs(&ht)?)?;
                let rhs = self.rw_rhs(
                    rhs,
                    &[
                        &self.ofe_cons_at(h, t)?,             // ofe (acons h t) → car h
                        &self.ors_cons_at(h, t)?,             // ors (acons h t) → t
                        &self.ofc_cons_at(h, t)?,             // ofc (acons h t) → cdr h
                        &self.th.cs.proj_scons(false, h, t)?, // car (acons h t) → h
                        &self.consp_cons_at(h, t)?,           // aconsp (acons h t) → t
                    ],
                )?;
                let rhs = self.fire_ifs(rhs)?;
                transport(e, lhs.trans(rhs.sym()?)?)
            },
        )?;
        thm.all_intro("x", self.a())
    }

    /// The `O<` defining-equation RHS at `(x, y)`.
    fn olt_rhs(&self, x: &Term, y: &Term) -> Result<Term> {
        let aif3 = |c: &Term, u: &Term, v: &Term| -> Result<Term> {
            self.pr
                .aif
                .clone()
                .apply(c.clone())?
                .apply(u.clone())?
                .apply(v.clone())
        };
        let anil = self.anil();
        let (fex, fey) = (ap1(&self.ofe, x)?, ap1(&self.ofe, y)?);
        let (fcx, fcy) = (ap1(&self.ofc, x)?, ap1(&self.ofc, y)?);
        let (rsx, rsy) = (ap1(&self.ors, x)?, ap1(&self.ors, y)?);
        let coeff = aif3(
            &ap2(&self.pr.equal, &fcx, &fcy)?,
            &ap2(&self.olt, &rsx, &rsy)?,
            &ap2(&self.pr.lt, &fcx, &fcy)?,
        )?;
        let expt = aif3(
            &ap2(&self.pr.equal, &fex, &fey)?,
            &coeff,
            &ap2(&self.olt, &fex, &fey)?,
        )?;
        let cons_arm = aif3(&ap1(&self.pr.consp, y)?, &expt, &anil)?;
        let fin_arm = aif3(
            &ap1(&self.pr.consp, y)?,
            &self.pr.t,
            &ap2(&self.pr.lt, x, y)?,
        )?;
        aif3(&ap1(&self.pr.consp, x)?, &cons_arm, &fin_arm)
    }

    /// **ACL2's `O<` defining equation as a model theorem**
    /// (design §1.2): `⊢ ∀x y. olt x y = <the normalized O< body>`. By
    /// nested carrier case analysis on `x` then (in the cons case) `y`.
    pub fn olt_def(&self) -> Result<Thm> {
        let x = self.avar("x");
        let y = self.avar("y");
        let goal = ap2(&self.olt, &x, &y)?.equals(self.olt_rhs(&x, &y)?)?;
        let thm = self.by_cases_lx(&x, &y, &goal)?;
        thm.all_intro("y", self.a())?.all_intro("x", self.a())
    }

    /// The outer (`x`) case analysis of [`Ordinals::olt_def`], split out
    /// for readability.
    fn by_cases_lx(&self, x: &Term, y: &Term, goal: &Term) -> Result<Thm> {
        let y = y.clone();
        self.by_cases(
            x,
            goal,
            "lx",
            &|b, e| {
                let atom_b = ap1(&self.th.atom, b)?;
                let lhs = self.olt_atom_at(b, &y)?;
                let rhs = Thm::refl(self.olt_rhs(&atom_b, &y)?)?;
                let rhs = self.rw_rhs(rhs, &[&self.pr.consp_atom()?.all_elim(b.clone())?])?;
                let rhs = self.fire_if(rhs)?;
                goal.rw_all(e)?.sym()?.eq_mp(lhs.trans(rhs.sym()?)?)
            },
            &|e| {
                let lhs = self.olt_nil_at(&y)?;
                let rhs = Thm::refl(self.olt_rhs(&self.anil(), &y)?)?;
                let rhs = self.rw_rhs(rhs, &[&self.pr.consp_nil()?])?;
                let rhs = self.fire_if(rhs)?;
                goal.rw_all(e)?.sym()?.eq_mp(lhs.trans(rhs.sym()?)?)
            },
            &|h, t, e| {
                let ht = self.acons_t(h, t)?;
                // Inner case analysis on y at fixed x = acons h t.
                let goal_y = ap2(&self.olt, &ht, &y)?.equals(self.olt_rhs(&ht, &y)?)?;
                // Both sides reduce to `anil` at a non-cons y.
                let leaf_y = |e2: &Thm, cv: Thm| -> Result<Thm> {
                    let yv = e2.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
                    let lhs = self.olt_cons_at(h, t, &yv)?;
                    let lhs = self.fire_if(self.rw_rhs(lhs, &[&cv])?)?; // = anil
                    let rhs = Thm::refl(self.olt_rhs(&ht, &yv)?)?;
                    let rhs = self.rw_rhs(rhs, &[&cv, &self.consp_cons_at(h, t)?])?;
                    let rhs = self.fire_ifs(rhs)?; // = anil
                    goal_y.rw_all(e2)?.sym()?.eq_mp(lhs.trans(rhs.sym()?)?)
                };
                let inner = self.by_cases(
                    &y,
                    &goal_y,
                    "ly",
                    &|b2, e2| leaf_y(e2, self.pr.consp_atom()?.all_elim(b2.clone())?),
                    &|e2| leaf_y(e2, self.pr.consp_nil()?),
                    &|h2, t2, e2| {
                        let yv = self.acons_t(h2, t2)?;
                        let lhs = self.olt_cons_at(h, t, &yv)?;
                        let lhs = self.rw_rhs(
                            lhs,
                            &[
                                &self.th.cs.proj_scons(false, h2, t2)?, // car (acons h2 t2) → h2
                                &self.th.cs.proj_scons(true, h2, t2)?,  // cdr (acons h2 t2) → t2
                                &self.consp_cons_at(h2, t2)?,
                            ],
                        )?;
                        let lhs = self.fire_ifs(lhs)?;
                        let rhs = Thm::refl(self.olt_rhs(&ht, &yv)?)?;
                        let rhs = self.rw_rhs(
                            rhs,
                            &[
                                &self.ofe_cons_at(h, t)?,
                                &self.ofe_cons_at(h2, t2)?,
                                &self.ofc_cons_at(h, t)?,
                                &self.ofc_cons_at(h2, t2)?,
                                &self.ors_cons_at(h, t)?,
                                &self.ors_cons_at(h2, t2)?,
                                &self.consp_cons_at(h, t)?,
                                &self.consp_cons_at(h2, t2)?,
                            ],
                        )?;
                        let rhs = self.fire_ifs(rhs)?;
                        goal_y.rw_all(e2)?.sym()?.eq_mp(lhs.trans(rhs.sym()?)?)
                    },
                )?;
                goal.rw_all(e)?.sym()?.eq_mp(inner)
            },
        )
    }

    // ------------------------------------------------------------------
    // Ground folding — `ord_fold` (design §2.3), the o-p/o< analogue of
    // `defun_ground`. Values are constructor literals over `aint ⌜i⌝` /
    // `asym ⌜s⌝` / `anil` / `acons`.
    // ------------------------------------------------------------------

    /// Parse a constructor-literal value.
    fn vshape(&self, v: &Term) -> Result<VShape> {
        if *v == self.anil() {
            return Ok(VShape::Nil);
        }
        let bad = || Error::ConnectiveRule(format!("acl2 ord: not a value: `{v}`"));
        let (f, arg) = v.as_app().ok_or_else(bad)?;
        if *f == self.th.aint {
            return Ok(VShape::Int(arg.clone()));
        }
        if *f == self.th.asym {
            return Ok(VShape::Sym(arg.clone()));
        }
        let (f2, h) = f.as_app().ok_or_else(bad)?;
        if *f2 == self.th.cons {
            return Ok(VShape::Cons(h.clone(), arg.clone()));
        }
        Err(bad())
    }

    fn is_value(&self, v: &Term) -> bool {
        // The boolean constant `t` is a value too (it is `asym ⌜"T"⌝`
        // only up to its definition; folding never needs to open it).
        if *v == self.pr.t {
            return true;
        }
        match self.vshape(v) {
            Ok(VShape::Cons(h, t)) => self.is_value(&h) && self.is_value(&t),
            Ok(_) => true,
            Err(_) => false,
        }
    }

    /// `⊢ v = aatom (in{l,r} lit)` for an `Int`/`Sym` value.
    fn atom_unfold(&self, v: &Term) -> Result<Thm> {
        match self.vshape(v)? {
            VShape::Int(i) => self.th.int_unfold(&i),
            VShape::Sym(s) => self.th.sym_unfold(&s),
            _ => Err(Error::ConnectiveRule(format!(
                "acl2 ord atom_unfold: not a payload atom: `{v}`"
            ))),
        }
    }

    /// `{a = b} ⊢ F` for **distinct** ground values (errors on equal or
    /// non-values) — the recursive freeness engine behind `value_ne`.
    fn value_eq_false(&self, a: &Term, b: &Term) -> Result<Thm> {
        let eq = a.clone().equals(b.clone())?;
        let assumed = Thm::assume(eq.clone())?;
        let dup = || Error::ConnectiveRule(format!("acl2 ord value_ne: `{a}` = `{b}`"));
        use VShape::*;
        let (sa, sb) = (self.vshape(a)?, self.vshape(b)?);
        let wrap = |s: &VShape| -> Result<Term> {
            match s {
                Int(i) => inl(Type::int(), Type::bytes()).apply(i.clone()),
                Sym(v) => inr(Type::int(), Type::bytes()).apply(v.clone()),
                _ => Err(Error::ConnectiveRule("acl2 ord: not an atom shape".into())),
            }
        };
        match (&sa, &sb) {
            (Int(i), Int(j)) => {
                let ne = i.clone().equals(j.clone())?.reduce()?;
                if ne.concl().as_eq().and_then(|(_, r)| r.as_bool()) != Some(false) {
                    return Err(dup());
                }
                let inner = self.th.int_inj(i, j)?.imp_elim(assumed)?; // {eq} ⊢ i = j
                fal_from_lit(ne.eq_mp(inner)?)
            }
            (Sym(s1), Sym(s2)) => {
                let ne = s1.clone().equals(s2.clone())?.reduce()?;
                if ne.concl().as_eq().and_then(|(_, r)| r.as_bool()) != Some(false) {
                    return Err(dup());
                }
                let inner = self.th.sym_inj(s1, s2)?.imp_elim(assumed)?;
                fal_from_lit(ne.eq_mp(inner)?)
            }
            (Int(i), Sym(s)) => self.th.int_ne_sym(i, s)?.imp_elim(assumed),
            (Sym(s), Int(i)) => self.th.int_ne_sym(i, s)?.imp_elim(assumed.sym()?),
            (Int(_) | Sym(_), Nil) => {
                let w = wrap(&sa)?;
                let chain = self.atom_unfold(a)?.sym()?.trans(assumed)?; // aatom w = anil
                self.th
                    .distinct(0, 1, std::slice::from_ref(&w), &[])?
                    .imp_elim(chain)
            }
            (Nil, Int(_) | Sym(_)) => {
                let w = wrap(&sb)?;
                let chain = self.atom_unfold(b)?.sym()?.trans(assumed.sym()?)?;
                self.th
                    .distinct(0, 1, std::slice::from_ref(&w), &[])?
                    .imp_elim(chain)
            }
            (Int(_) | Sym(_), Cons(h, t)) => {
                let w = wrap(&sa)?;
                let chain = self.atom_unfold(a)?.sym()?.trans(assumed)?; // aatom w = acons h t
                self.th
                    .distinct(0, 2, std::slice::from_ref(&w), &[h.clone(), t.clone()])?
                    .imp_elim(chain)
            }
            (Cons(h, t), Int(_) | Sym(_)) => {
                let w = wrap(&sb)?;
                let chain = self.atom_unfold(b)?.sym()?.trans(assumed.sym()?)?;
                self.th
                    .distinct(0, 2, std::slice::from_ref(&w), &[h.clone(), t.clone()])?
                    .imp_elim(chain)
            }
            (Nil, Cons(h, t)) => self
                .th
                .distinct(1, 2, &[], &[h.clone(), t.clone()])?
                .imp_elim(assumed),
            (Cons(h, t), Nil) => self
                .th
                .distinct(1, 2, &[], &[h.clone(), t.clone()])?
                .imp_elim(assumed.sym()?),
            (Cons(h1, t1), Cons(h2, t2)) => {
                let inj = self.th.cons_inj(h1, t1, h2, t2)?.imp_elim(assumed)?;
                if h1 != h2 {
                    self.value_ne(h1, h2)?.not_elim(inj.and_elim_l()?)
                } else if t1 != t2 {
                    self.value_ne(t1, t2)?.not_elim(inj.and_elim_r()?)
                } else {
                    Err(dup())
                }
            }
            (Nil, Nil) => Err(dup()),
        }
    }

    /// `⊢ ¬(a = b)` for distinct ground values.
    fn value_ne(&self, a: &Term, b: &Term) -> Result<Thm> {
        let eq = a.clone().equals(b.clone())?;
        self.value_eq_false(a, b)?.imp_intro(&eq)?.not_intro()
    }

    /// `⊢ aequal a b = t | anil` for ground values.
    fn aequal_val(&self, a: &Term, b: &Term) -> Result<Thm> {
        if a == b {
            self.pr.equal_refl()?.all_elim(a.clone())
        } else {
            self.pr
                .equal_ne()?
                .all_elim(a.clone())?
                .all_elim(b.clone())?
                .imp_elim(self.value_ne(a, b)?)
        }
    }

    /// `⊢ aconsp v = t | anil` for a ground(-shaped) value.
    fn consp_val(&self, v: &Term) -> Result<Thm> {
        match self.vshape(v)? {
            VShape::Cons(h, t) => self.consp_cons_at(&h, &t),
            VShape::Nil => self.pr.consp_nil(),
            VShape::Int(i) => self.consp_int_at(&i),
            VShape::Sym(s) => self.consp_sym_at(&s),
        }
    }

    /// `⊢ aintp v = t | anil`.
    fn intp_val(&self, v: &Term) -> Result<Thm> {
        match self.vshape(v)? {
            VShape::Int(i) => self.pr.intp_int()?.all_elim(i),
            VShape::Sym(s) => self.pr.intp_sym()?.all_elim(s),
            VShape::Nil => self.pr.intp_nil(),
            VShape::Cons(h, t) => self
                .pr
                .intp_cons()?
                .all_elim(h.clone())?
                .all_elim(t.clone()),
        }
    }

    /// `⊢ car v = <value>` / `⊢ cdr v = <value>`.
    fn proj_val(&self, take_cdr: bool, v: &Term) -> Result<Thm> {
        match self.vshape(v)? {
            VShape::Cons(h, t) => self.th.cs.proj_scons(take_cdr, &h, &t),
            VShape::Nil => {
                if take_cdr {
                    self.pr.cdr_nil()
                } else {
                    self.pr.car_nil()
                }
            }
            VShape::Int(i) => {
                if take_cdr {
                    self.pr.cdr_int()?.all_elim(i)
                } else {
                    self.pr.car_int()?.all_elim(i)
                }
            }
            VShape::Sym(s) => {
                if take_cdr {
                    self.pr.cdr_sym()?.all_elim(s)
                } else {
                    self.pr.car_sym()?.all_elim(s)
                }
            }
        }
    }

    /// `⊢ intval v = ⌜i⌝ | 0` (arithmetic completion on non-numbers).
    fn intval_val(&self, v: &Term) -> Result<Thm> {
        match self.vshape(v)? {
            VShape::Int(i) => self.pr.intval_int()?.all_elim(i),
            VShape::Sym(s) => self.pr.intval_sym()?.all_elim(s),
            VShape::Nil => self.pr.intval_nil(),
            VShape::Cons(h, t) => self
                .pr
                .intval_cons()?
                .all_elim(h.clone())?
                .all_elim(t.clone()),
        }
    }

    /// `⊢ alt a b = t | anil` for ground values (through `intval` + the
    /// literal `intLt` certificate).
    fn alt_val(&self, a: &Term, b: &Term) -> Result<Thm> {
        let acc = self.pr.alt_unfold(a, b)?; // cond A (intLt (intval a)(intval b)) t anil
        let iva = self.intval_val(a)?;
        let ivb = self.intval_val(b)?;
        let acc = self.rw_rhs(acc, &[&iva, &ivb])?;
        let la = iva.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
        let lb = ivb.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
        let g = int::int_lt().apply(la)?.apply(lb)?.reduce()?; // ⊢ intLt ⌜i⌝ ⌜j⌝ = ⌜T/F⌝
        self.rw_rhs(acc, &[&g])?
            .rhs_conv(crate::init::cond::collapse_conds)
    }

    /// Continue folding after a law application: `acc : ⊢ t = rhs`, fold
    /// `rhs` on and chain.
    fn fold_on(&self, acc: Thm) -> Result<Thm> {
        let rhs = acc.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
        let cont = self.ord_fold(&rhs)?;
        acc.trans(cont)
    }

    /// **Ground normaliser** (design §2.3): `⊢ t = <value>` for `op` /
    /// `olt` / `natp` / `posp` / `ofe` / `ofc` / `ors` / `aequal` /
    /// `aconsp` / `aintp` / `alt` / `aif` applications over
    /// constructor-literal values. Fails safe (errors) on anything else —
    /// the o-p/o< analogue of `defun_ground`; do **not** feed these heads
    /// to `defun::fold_ground`.
    pub fn ord_fold(&self, t: &Term) -> Result<Thm> {
        if self.is_value(t) {
            return Ok(Thm::refl(t.clone())?);
        }
        let bad = || Error::ConnectiveRule(format!("acl2 ord_fold: unsupported term `{t}`"));
        // aif c y z — fold the guard, fire, fold the survivor.
        if let Some((c, _y, _z)) = self.parse_aif(t) {
            let ce = self.ord_fold(&c)?;
            let acc = Thm::refl(t.clone())?;
            let acc = self.rw_rhs(acc, &[&ce])?;
            let acc = self.fire_if(acc)?;
            return self.fold_on(acc);
        }
        let (f, args) = spine(t);
        if args.len() == 1 {
            let v = &args[0];
            if !self.is_value(v) {
                // Fold the argument first, then the head at the value.
                let ae = self.ord_fold(v)?;
                let acc = Thm::refl(t.clone())?.rhs_conv(|tm| tm.rw_all(&ae))?;
                return self.fold_on(acc);
            }
            if *f == self.pr.consp {
                return self.consp_val(v);
            }
            if *f == self.pr.intp {
                return self.intp_val(v);
            }
            if *f == self.th.car {
                return self.proj_val(false, v);
            }
            if *f == self.th.cdr {
                return self.proj_val(true, v);
            }
            if *f == self.ors {
                return self.ors_at(v)?.trans(self.proj_val(true, v)?);
            }
            if *f == self.ofe {
                return match self.vshape(v)? {
                    VShape::Cons(h, t2) => {
                        self.ofe_cons_at(&h, &t2)?.trans(self.proj_val(false, &h)?)
                    }
                    _ => self.ofe_noncons_at(v, &self.consp_val(v)?),
                };
            }
            if *f == self.ofc {
                return match self.vshape(v)? {
                    VShape::Cons(h, t2) => {
                        self.ofc_cons_at(&h, &t2)?.trans(self.proj_val(true, &h)?)
                    }
                    _ => {
                        let acc = apply_def(&self.ofc_eq, std::slice::from_ref(v))?;
                        self.fire_if(self.rw_rhs(acc, &[&self.consp_val(v)?])?)
                    }
                };
            }
            if *f == self.natp {
                return match self.vshape(v)? {
                    VShape::Int(i) => {
                        let acc = self.natp_int_at(&i)?; // aif (alt (aint i) '0) anil t
                        let g = self.alt_val(&self.th.aint_at(&i)?, &self.a0()?)?;
                        self.fire_if(self.rw_rhs(acc, &[&g])?)
                    }
                    _ => self.natp_nonint_at(v, &self.intp_val(v)?),
                };
            }
            if *f == self.posp {
                return match self.vshape(v)? {
                    VShape::Int(i) => {
                        let acc = self.posp_int_at(&i)?; // = alt '0 (aint i)
                        acc.trans(self.alt_val(&self.a0()?, &self.th.aint_at(&i)?)?)
                    }
                    _ => {
                        let acc = apply_def(&self.posp_eq, std::slice::from_ref(v))?;
                        self.fire_if(self.rw_rhs(acc, &[&self.intp_val(v)?])?)
                    }
                };
            }
            if *f == self.op {
                return match self.vshape(v)? {
                    VShape::Cons(h, t2) => {
                        let acc = self.op_cons_at(&h, &t2)?;
                        // Pre-fold the `h` projections and `ofe t` so
                        // every guard/leaf is over values.
                        let acc = self.rw_rhs(
                            acc,
                            &[
                                &self.proj_val(false, &h)?,
                                &self.proj_val(true, &h)?,
                                &self.ord_fold(&ap1(&self.ofe, &t2)?)?,
                            ],
                        )?;
                        self.fold_on(acc)
                    }
                    VShape::Nil => self.fold_on(self.op_nil_at()?),
                    VShape::Int(i) => self.fold_on(self.op_int_at(&i)?),
                    VShape::Sym(s) => self.fold_on(self.op_sym_at(&s)?),
                };
            }
            return Err(bad());
        }
        if args.len() == 2 {
            let (x, y) = (&args[0], &args[1]);
            if !self.is_value(x) || !self.is_value(y) {
                return Err(bad());
            }
            if *f == self.pr.equal {
                return self.aequal_val(x, y);
            }
            if *f == self.pr.lt {
                return self.alt_val(x, y);
            }
            if *f == self.olt {
                return match self.vshape(x)? {
                    VShape::Cons(h, t2) => {
                        let acc = self.olt_cons_at(&h, &t2, y)?;
                        let mut eqs: Vec<Thm> =
                            vec![self.proj_val(false, &h)?, self.proj_val(true, &h)?];
                        if let VShape::Cons(h2, _) = self.vshape(y)? {
                            eqs.push(self.proj_val(false, y)?); // car y → h2
                            eqs.push(self.proj_val(true, y)?); // cdr y → t2'
                            eqs.push(self.proj_val(false, &h2)?);
                            eqs.push(self.proj_val(true, &h2)?);
                        }
                        let eq_refs: Vec<&Thm> = eqs.iter().collect();
                        let acc = self.rw_rhs(acc, &eq_refs)?;
                        self.fold_on(acc)
                    }
                    VShape::Nil => self.fold_on(self.olt_nil_at(y)?),
                    VShape::Int(i) => self.fold_on(self.olt_int_at(&i, y)?),
                    VShape::Sym(s) => self.fold_on(self.olt_sym_at(&s, y)?),
                };
            }
            return Err(bad());
        }
        Err(bad())
    }

    /// Parse `aif c y z`.
    fn parse_aif(&self, t: &Term) -> Option<(Term, Term, Term)> {
        let (cy, z) = t.as_app()?;
        let (cc, y) = cy.as_app()?;
        let (hd, c) = cc.as_app()?;
        (*hd == self.pr.aif).then(|| (c.clone(), y.clone(), z.clone()))
    }

    // ------------------------------------------------------------------
    // Accessibility (design §5) — `Acc` and its three rules
    // ------------------------------------------------------------------

    /// The step term `∀z. (∀y. below y z ⟹ S y) ⟹ S z` at `s`.
    /// `Γ∪Δ ⊢ below y x` from `hop : Γ ⊢ ¬(op y = anil)` and
    /// `holt : Δ ⊢ ¬(olt y x = anil)` — the `below`-fold seam for the
    /// S5d IND-ORD soundness discharge
    /// (`derivable.rs::discharge_ind_ord`).
    pub(crate) fn below_intro(&self, y: &Term, x: &Term, hop: Thm, holt: Thm) -> Result<Thm> {
        apply_def(&self.below_eq, &[y.clone(), x.clone()])?
            .sym()?
            .eq_mp(hop.and_intro(holt)?)
    }

    fn acc_step_at(&self, s: &Term) -> Result<Term> {
        let a = self.a();
        let y = Term::free("__ay", a.clone());
        let z = Term::free("__az", a.clone());
        let inner = ap2(&self.below, &y, &z)?
            .imp(s.clone().apply(y.clone())?)?
            .forall("__ay", a.clone())?;
        inner
            .imp(s.clone().apply(z.clone())?)?
            .forall("__az", a.clone())
    }

    /// `⊢ ∀x. (∀y. below y x ⟹ acc y) ⟹ acc x` — Acc introduction.
    pub fn acc_intro(&self) -> Result<Thm> {
        let a = self.a();
        let sb = Type::fun(a.clone(), Type::bool());
        let x = Term::free("__ix", a.clone());
        let y = Term::free("__iy", a.clone());
        let s = Term::free("__iS", sb.clone());
        let prem = ap2(&self.below, &y, &x)?
            .imp(ap1(&self.acc, &y)?)?
            .forall("__iy", a.clone())?;
        let hs = self.acc_step_at(&s)?;
        // {prem, hs} ⊢ ∀y. below y x ⟹ S y.
        let inner = {
            let r = ap2(&self.below, &y, &x)?;
            let acc_y = Thm::assume(prem.clone())?
                .all_elim(y.clone())?
                .imp_elim(Thm::assume(r.clone())?)?; // acc y
            let sy = apply_def(&self.acc_eq, &[y.clone()])?
                .eq_mp(acc_y)? // ∀S. step(S) ⟹ S y
                .all_elim(s.clone())?
                .imp_elim(Thm::assume(hs.clone())?)?; // S y
            sy.imp_intro(&r)?.all_intro("__iy", a.clone())?
        };
        let sx = Thm::assume(hs.clone())?
            .all_elim(x.clone())?
            .imp_elim(inner)?; // {prem, hs} ⊢ S x
        let body = sx.imp_intro(&hs)?.all_intro("__iS", sb)?; // {prem} ⊢ ∀S. …
        apply_def(&self.acc_eq, &[x.clone()])?
            .sym()?
            .eq_mp(body)? // {prem} ⊢ acc x
            .imp_intro(&prem)?
            .all_intro("__ix", a)
    }

    /// `⊢ ∀S. (∀z. (∀y. below y z ⟹ S y) ⟹ S z) ⟹ ∀x. acc x ⟹ S x` —
    /// Acc elimination (the well-founded-induction principle).
    pub fn acc_elim(&self) -> Result<Thm> {
        let a = self.a();
        let sb = Type::fun(a.clone(), Type::bool());
        let x = Term::free("__ex", a.clone());
        let s = Term::free("__eS", sb.clone());
        let hs = self.acc_step_at(&s)?;
        let accx = ap1(&self.acc, &x)?;
        let sx = apply_def(&self.acc_eq, &[x.clone()])?
            .eq_mp(Thm::assume(accx.clone())?)?
            .all_elim(s.clone())?
            .imp_elim(Thm::assume(hs.clone())?)?; // {acc x, hs} ⊢ S x
        sx.imp_intro(&accx)?
            .all_intro("__ex", a)?
            .imp_intro(&hs)?
            .all_intro("__eS", sb)
    }

    /// `⊢ ∀x. acc x ⟹ ∀y. below y x ⟹ acc y` — Acc inversion.
    pub fn acc_inv(&self) -> Result<Thm> {
        let a = self.a();
        let x = Term::free("__vx", a.clone());
        let y = Term::free("__vy", a.clone());
        // S0 := λz. ∀y. below y z ⟹ acc y.
        let s0 = {
            let z = Term::free("__vz", a.clone());
            let body = ap2(&self.below, &y, &z)?
                .imp(ap1(&self.acc, &y)?)?
                .forall("__vy", a.clone())?;
            Term::abs(a.clone(), subst::close(&body, "__vz"))
        };
        // The closure step at S0 (applied form).
        let step = {
            let z = Term::free("__vz", a.clone());
            let hyp_in = ap2(&self.below, &y, &z)?
                .imp(Term::app(s0.clone(), y.clone()))?
                .forall("__vy", a.clone())?;
            let inner = {
                let r = ap2(&self.below, &y, &z)?;
                let s0y = Thm::assume(hyp_in.clone())?
                    .all_elim(y.clone())?
                    .imp_elim(Thm::assume(r.clone())?)?; // (S0 y) applied
                let acc_prem = beta_reduce(s0y)?; // ∀y'. below y' y ⟹ acc y'
                let accy = self.acc_intro()?.all_elim(y.clone())?.imp_elim(acc_prem)?; // acc y
                accy.imp_intro(&r)?.all_intro("__vy", a.clone())?
            };
            beta_expand(&s0, z.clone(), inner)?
                .imp_intro(&hyp_in)?
                .all_intro("__vz", a.clone())?
        };
        let accx = ap1(&self.acc, &x)?;
        let s0x = apply_def(&self.acc_eq, &[x.clone()])?
            .eq_mp(Thm::assume(accx.clone())?)?
            .all_elim(s0.clone())?
            .imp_elim(step)?; // (S0 x) applied
        beta_reduce(s0x)? // ∀y. below y x ⟹ acc y
            .imp_intro(&accx)?
            .all_intro("__vx", a)
    }

    // ------------------------------------------------------------------
    // The inversion kit (the L0 slice) + int-order helpers
    // ------------------------------------------------------------------

    /// From `hne : Γ ⊢ ¬(A = anil)` and `eq : Δ ⊢ A = B`, conclude
    /// `Γ ∪ Δ ⊢ ¬(B = anil)`.
    fn ne_nil_transport(&self, hne: &Thm, eq: &Thm) -> Result<Thm> {
        let b = eq.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
        let b_nil = b.equals(self.anil())?;
        let f = hne
            .clone()
            .not_elim(eq.clone().trans(Thm::assume(b_nil.clone())?)?)?;
        f.imp_intro(&b_nil)?.not_intro()
    }

    /// From `hn : Γ ⊢ ¬(intLt a b)`, conclude `Γ ⊢ intLe b a` (through
    /// `int` trichotomy + `le_def`).
    fn int_ge_of_not_lt(&self, a: &Term, b: &Term, hn: Thm) -> Result<Thm> {
        let lt = |u: &Term, v: &Term| -> Result<Term> {
            int::int_lt().apply(u.clone())?.apply(v.clone())
        };
        let goal = int::int_le().apply(b.clone())?.apply(a.clone())?;
        let tri_ab = lt(a, b)?;
        let eq_ab = a.clone().equals(b.clone())?;
        let lt_ba = lt(b, a)?;
        let ledef = int::le_def().all_elim(b.clone())?.all_elim(a.clone())?; // (b≤a) = (b<a ∨ b=a)
        let br_lt = hn
            .not_elim(Thm::assume(tri_ab.clone())?)?
            .false_elim(goal.clone())?
            .imp_intro(&tri_ab)?;
        let br_eq = {
            let ba = Thm::assume(eq_ab.clone())?.sym()?; // b = a
            let disj = ba.or_intro_r(lt_ba.clone())?; // (b<a) ∨ (b=a)
            ledef.clone().sym()?.eq_mp(disj)?.imp_intro(&eq_ab)?
        };
        let br_gt = {
            let disj = Thm::assume(lt_ba.clone())?.or_intro_l(b.clone().equals(a.clone())?)?;
            ledef.sym()?.eq_mp(disj)?.imp_intro(&lt_ba)?
        };
        let rest = eq_ab.clone().or(lt_ba.clone())?;
        let inner = Thm::assume(rest.clone())?
            .or_elim(br_eq, br_gt)?
            .imp_intro(&rest)?;
        int::lt_trichotomy()
            .all_elim(a.clone())?
            .all_elim(b.clone())?
            .or_elim(br_lt, inner)
    }

    /// `⊢ ∀x. ¬(natp x = anil) ⟹ ∃i. (x = aint i) ∧ (intLe 0 i)` —
    /// `natp` inversion: a non-`nil` `natp` answer certifies an integer
    /// atom with a nonnegative payload.
    pub fn natp_inv(&self) -> Result<Thm> {
        let a = self.a();
        let x = self.avar("x");
        let hyp_t = ap1(&self.natp, &x)?.equals(self.anil())?.not()?;
        let hne = Thm::assume(hyp_t.clone())?;
        let lit0 = mk_int(0i64);
        let le0 =
            |v: &Term| -> Result<Term> { int::int_le().apply(lit0.clone())?.apply(v.clone()) };
        let (pred, goal) = {
            let jv = Term::free("__nj", Type::int());
            let body = x.clone().equals(self.th.aint_at(&jv)?)?.and(le0(&jv)?)?;
            let pred = Term::abs(Type::int(), subst::close(&body, "__nj"));
            let goal = body.exists("__nj", Type::int())?;
            (pred, goal)
        };
        // A branch that refutes `hne` via `⊢ natp x = anil`.
        let refute =
            |chain: Thm| -> Result<Thm> { hne.clone().not_elim(chain)?.false_elim(goal.clone()) };
        let proved = self.by_cases(
            &x,
            &goal,
            "ni",
            &|b, e| {
                // Payload split.
                let disj = coprod_cases(&Type::int(), &Type::bytes(), b)?;
                let bad = || Error::ConnectiveRule("acl2 ord natp_inv: bad coprod cases".into());
                let (or_l, dr) = disj.concl().as_app().ok_or_else(bad)?;
                let (_, dl) = or_l.as_app().ok_or_else(bad)?;
                let (dl, dr) = (dl.clone(), dr.clone());
                let br_l = {
                    let pred_l = dl.as_app().ok_or_else(bad)?.1.clone();
                    let w = Term::free("__nw", Type::int());
                    let hyp = Term::app(pred_l, w.clone());
                    let e2 = beta_reduce(Thm::assume(hyp.clone())?)?; // b = inl w
                    // x = aint w.
                    let xe = e
                        .clone()
                        .trans(e2.cong_arg(self.th.atom.clone())?)?
                        .trans(self.th.int_unfold(&w)?.sym()?)?;
                    // natp x = aif (alt (aint w) '0) anil t.
                    let ne_chain = xe
                        .clone()
                        .cong_arg(self.natp.clone())?
                        .trans(self.natp_int_at(&w)?)?;
                    let hne2 = self.ne_nil_transport(&hne, &ne_chain)?;
                    let aw = self.th.aint_at(&w)?;
                    let a0 = self.a0()?;
                    let alt_t = ap2(&self.pr.lt, &aw, &a0)?;
                    let c = alt_t.clone().equals(self.anil())?;
                    let nc = c.clone().not()?;
                    // alt_iff at (aint w, '0), intvals folded.
                    let iff = self
                        .pr
                        .alt_iff_at(&aw, &a0)?
                        .rewrite(&self.pr.intval_int()?.all_elim(w.clone())?)?
                        .rewrite(&self.pr.intval_int()?.all_elim(lit0.clone())?)?;
                    // {c} branch: guard nil ⟹ 0 ≤ w; witness w.
                    let pos = {
                        let lt_w0 = int::int_lt().apply(w.clone())?.apply(lit0.clone())?;
                        let f = iff
                            .clone()
                            .sym()?
                            .eq_mp(Thm::assume(lt_w0.clone())?)? // ¬(alt aw a0 = anil)
                            .not_elim(Thm::assume(c.clone())?)?;
                        let nlt = f.imp_intro(&lt_w0)?.not_intro()?; // {c} ⊢ ¬(w < 0)
                        let ge = self.int_ge_of_not_lt(&w, &lit0, nlt)?; // 0 ≤ w
                        let conj = xe.clone().and_intro(ge)?;
                        let applied = beta_expand(&pred, w.clone(), conj)?;
                        exists_intro(pred.clone(), w.clone(), applied)?
                    };
                    // {¬c} branch: value anil, contradiction.
                    let neg = {
                        let v = self
                            .pr
                            .if_t()?
                            .all_elim(alt_t.clone())?
                            .all_elim(self.anil())?
                            .all_elim(self.pr.t.clone())?
                            .imp_elim(Thm::assume(nc.clone())?)?; // aif … = anil
                        hne2.not_elim(v)?.false_elim(goal.clone())?
                    };
                    let g =
                        Thm::lem(c.clone())?.or_elim(pos.imp_intro(&c)?, neg.imp_intro(&nc)?)?;
                    let step = g.imp_intro(&hyp)?.all_intro("__nw", Type::int())?;
                    exists_elim(Thm::assume(dl.clone())?, goal.clone(), step)?.imp_intro(&dl)?
                };
                let br_r = {
                    let pred_r = dr.as_app().ok_or_else(bad)?.1.clone();
                    let w = Term::free("__ns", Type::bytes());
                    let hyp = Term::app(pred_r, w.clone());
                    let e2 = beta_reduce(Thm::assume(hyp.clone())?)?; // b = inr w
                    let xe = e
                        .clone()
                        .trans(e2.cong_arg(self.th.atom.clone())?)?
                        .trans(self.th.sym_unfold(&w)?.sym()?)?; // x = asym w
                    let asw = self.th.asym_at(&w)?;
                    let chain = xe.cong_arg(self.natp.clone())?.trans(
                        self.natp_nonint_at(&asw, &self.pr.intp_sym()?.all_elim(w.clone())?)?,
                    )?;
                    let g = refute(chain)?;
                    let step = g.imp_intro(&hyp)?.all_intro("__ns", Type::bytes())?;
                    exists_elim(Thm::assume(dr.clone())?, goal.clone(), step)?.imp_intro(&dr)?
                };
                disj.or_elim(br_l, br_r)
            },
            &|e| {
                let chain = e
                    .clone()
                    .cong_arg(self.natp.clone())?
                    .trans(self.natp_nonint_at(&self.anil(), &self.pr.intp_nil()?)?)?;
                refute(chain)
            },
            &|h, t, e| {
                let ht = self.acons_t(h, t)?;
                let iv = self
                    .pr
                    .intp_cons()?
                    .all_elim(h.clone())?
                    .all_elim(t.clone())?;
                let chain = e
                    .clone()
                    .cong_arg(self.natp.clone())?
                    .trans(self.natp_nonint_at(&ht, &iv)?)?;
                refute(chain)
            },
        )?;
        proved.imp_intro(&hyp_t)?.all_intro("x", a)
    }

    /// `⊢ ∀y i. ¬(op y = anil) ⟹ ¬(olt y (aint i) = anil) ⟹
    /// ∃j. (y = aint j) ∧ (intLe 0 j ∧ intLt j i)` — finite-target `o<`
    /// inversion (design §5.2, `olt_fin_inv`).
    pub fn olt_fin_inv(&self) -> Result<Thm> {
        let a = self.a();
        let y = self.avar("y");
        let i = Term::free("i", Type::int());
        let ai = self.th.aint_at(&i)?;
        let lit0 = mk_int(0i64);
        let hop_t = ap1(&self.op, &y)?.equals(self.anil())?.not()?;
        let holt_t = ap2(&self.olt, &y, &ai)?.equals(self.anil())?.not()?;
        let hop = Thm::assume(hop_t.clone())?;
        let holt = Thm::assume(holt_t.clone())?;
        let (pred, goal) = {
            let jv = Term::free("__fj", Type::int());
            let le0j = int::int_le().apply(lit0.clone())?.apply(jv.clone())?;
            let ltji = int::int_lt().apply(jv.clone())?.apply(i.clone())?;
            let body = y
                .clone()
                .equals(self.th.aint_at(&jv)?)?
                .and(le0j.and(ltji)?)?;
            let pred = Term::abs(Type::int(), subst::close(&body, "__fj"));
            let goal = body.exists("__fj", Type::int())?;
            (pred, goal)
        };
        // The shared non-cons arm: `op y` reduces through `natp`, so
        // `natp_inv` yields the integer witness, and the `olt` atom law
        // reduces `olt y (aint i)` to `alt (aint j) (aint i)`.
        let finite_arm = |e: &Thm, op_chain: Thm| -> Result<Thm> {
            // op_chain : op <ctor> = natp <ctor>; e : y = <ctor>.
            let hne = self
                .ne_nil_transport(&hop, &e.clone().cong_arg(self.op.clone())?.trans(op_chain)?)?;
            let ctor = e.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
            let inv = self.natp_inv()?.all_elim(ctor.clone())?.imp_elim(hne)?;
            let bad = || Error::ConnectiveRule("acl2 ord olt_fin_inv: bad ∃".into());
            let pred_n = inv.concl().as_app().ok_or_else(bad)?.1.clone();
            let w = Term::free("__fw", Type::int());
            let hyp = Term::app(pred_n, w.clone());
            let conj = beta_reduce(Thm::assume(hyp.clone())?)?;
            let ctor_eq = conj.clone().and_elim_l()?; // ctor = aint w
            let h0 = conj.and_elim_r()?; // 0 ≤ w
            let y_eq = e.clone().trans(ctor_eq)?; // y = aint w
            let aw = self.th.aint_at(&w)?;
            // olt y (aint i) = alt (aint w) (aint i).
            let olt_chain = y_eq
                .clone()
                .cong_arg(self.olt.clone())?
                .cong_fn(ai.clone())?
                .trans(self.olt_int_at(&w, &ai)?)?;
            let olt_chain = self.rw_rhs(olt_chain, &[&self.consp_int_at(&i)?])?;
            let olt_chain = self.fire_if(olt_chain)?; // = alt (aint w) (aint i)
            let hlt_a = self.ne_nil_transport(&holt, &olt_chain)?;
            let ilt = self
                .pr
                .alt_iff_at(&aw, &ai)?
                .rewrite(&self.pr.intval_int()?.all_elim(w.clone())?)?
                .rewrite(&self.pr.intval_int()?.all_elim(i.clone())?)?
                .eq_mp(hlt_a)?; // intLt w i
            let out = y_eq.and_intro(h0.and_intro(ilt)?)?;
            let applied = beta_expand(&pred, w.clone(), out)?;
            let g = exists_intro(pred.clone(), w.clone(), applied)?;
            let step = g.imp_intro(&hyp)?.all_intro("__fw", Type::int())?;
            exists_elim(inv, goal.clone(), step)
        };
        let proved = self.by_cases(
            &y,
            &goal,
            "fi",
            &|b, e| finite_arm(e, self.op_atom_at(b)?),
            &|e| finite_arm(e, self.op_nil_at()?),
            &|h, t, e| {
                // olt (acons h t) (aint i) = anil — contradiction.
                let chain = e
                    .clone()
                    .cong_arg(self.olt.clone())?
                    .cong_fn(ai.clone())?
                    .trans(self.olt_cons_at(h, t, &ai)?)?;
                let chain = self.rw_rhs(chain, &[&self.consp_int_at(&i)?])?;
                let chain = self.fire_if(chain)?; // = anil
                holt.clone().not_elim(chain)?.false_elim(goal.clone())
            },
        )?;
        proved
            .imp_intro(&holt_t)?
            .imp_intro(&hop_t)?
            .all_intro("i", Type::int())?
            .all_intro("y", a)
    }

    // ------------------------------------------------------------------
    // The guard-splitting kit (design §5.2, continuation form — the
    // packaged ∃-statements are replaced by Rust openers with the same
    // proof content; recorded as an S5 implementation deviation)
    // ------------------------------------------------------------------

    /// From `hy : Γ ⊢ ¬(anil = anil)` conclude `Γ ⊢ goal` (ex falso).
    fn absurd_ne_nil(&self, hy: &Thm, goal: &Term) -> Result<Thm> {
        hy.clone()
            .not_elim(Thm::refl(self.anil())?)?
            .false_elim(goal.clone())
    }

    /// Split on the guard of `hne : Γ ⊢ ¬(aif g x y = anil)`:
    /// `pos(hg_ne : ¬(g = anil), hx : ¬(x = anil))` and
    /// `neg(hg : g = anil, hy : ¬(y = anil))` both prove `goal`.
    fn aif_ne_split(
        &self,
        hne: &Thm,
        _goal: &Term,
        pos: &dyn Fn(&Thm, &Thm) -> Result<Thm>,
        neg: &dyn Fn(&Thm, &Thm) -> Result<Thm>,
    ) -> Result<Thm> {
        let bad = || Error::ConnectiveRule("acl2 ord aif_ne_split: not an aif ≠ nil".into());
        // hne concl: ¬((aif g x y) = anil).
        let (_, eqt) = hne.concl().as_app().ok_or_else(bad)?;
        let (aif_t, _) = eqt.as_eq().ok_or_else(bad)?;
        let (g, x, y) = self.parse_aif(aif_t).ok_or_else(bad)?;
        let gnil = g.clone().equals(self.anil())?;
        let ngnil = gnil.clone().not()?;
        let br_neg = {
            let hg = Thm::assume(gnil.clone())?;
            let chain = Thm::refl(aif_t.clone())?.rhs_conv(|tm| tm.rw_all(&hg))?;
            let chain = self.fire_if(chain)?; // aif g x y = y
            let hy = self.ne_nil_transport(hne, &chain)?;
            neg(&hg, &hy)?.imp_intro(&gnil)?
        };
        let br_pos = {
            let hg_ne = Thm::assume(ngnil.clone())?;
            let chain = self
                .pr
                .if_t()?
                .all_elim(g.clone())?
                .all_elim(x.clone())?
                .all_elim(y.clone())?
                .imp_elim(hg_ne.clone())?; // aif g x y = x
            let hx = self.ne_nil_transport(hne, &chain)?;
            pos(&hg_ne, &hx)?.imp_intro(&ngnil)?
        };
        Thm::lem(gnil)?.or_elim(br_neg, br_pos)
    }

    /// `Γ ⊢ ¬(a = b)` from `hg : Γ ⊢ aequal a b = anil` (contrapose
    /// `equal_refl` — design's `aequal_nil`).
    fn aequal_nil(&self, a: &Term, b: &Term, hg: &Thm) -> Result<Thm> {
        let eq = a.clone().equals(b.clone())?;
        // {a = b} ⊢ aequal a b = aequal a a (congruence in the 2nd slot).
        let cong = Thm::assume(eq.clone())?
            .sym()?
            .cong_arg(Term::app(self.pr.equal.clone(), a.clone()))?;
        // {a = b} ⊢ t = anil: t = aequal a a = aequal a b = anil.
        let chain = self
            .pr
            .equal_refl()?
            .all_elim(a.clone())?
            .sym()? // t = aequal a a
            .trans(cong.sym()?)? // = aequal a b
            .trans(hg.clone())?; // = anil
        let f = self.pr.t_ne_nil()?.not_elim(chain)?;
        f.imp_intro(&eq)?.not_intro()
    }

    /// `Γ ⊢ a = b` from `hne : Γ ⊢ ¬(aequal a b = anil)` (`equal_holds`).
    fn aequal_holds(&self, a: &Term, b: &Term, hne: &Thm) -> Result<Thm> {
        self.pr
            .equal_holds()?
            .all_elim(a.clone())?
            .all_elim(b.clone())?
            .imp_elim(hne.clone())
    }

    /// Open `hc : Γ ⊢ ¬(aconsp v = anil)` — case-split `v` to a cons and
    /// run `k(h, t, e : ⊢ v = acons h t)`; the non-cons cases are
    /// refuted. `goal` must not mention the fresh `__k<tag>` names.
    fn consp_open(
        &self,
        v: &Term,
        hc: &Thm,
        goal: &Term,
        tag: &str,
        k: &dyn Fn(&Term, &Term, &Thm) -> Result<Thm>,
    ) -> Result<Thm> {
        let refute = |cv: Thm| -> Result<Thm> { hc.clone().not_elim(cv)?.false_elim(goal.clone()) };
        self.by_cases(
            v,
            goal,
            tag,
            &|b, e| {
                refute(
                    e.clone()
                        .cong_arg(self.pr.consp.clone())?
                        .trans(self.pr.consp_atom()?.all_elim(b.clone())?)?,
                )
            },
            &|e| {
                refute(
                    e.clone()
                        .cong_arg(self.pr.consp.clone())?
                        .trans(self.pr.consp_nil()?)?,
                )
            },
            &|h, t, e| k(h, t, e),
        )
    }

    /// Open `hne : Γ ⊢ ¬(posp v = anil)` at a value-shaped or arbitrary
    /// `v`: yields `k(j, e : ⊢ v = aint j, pos : ⊢ intLt ⌜0⌝ j)`.
    fn posp_open(
        &self,
        v: &Term,
        hne: &Thm,
        goal: &Term,
        tag: &str,
        k: &dyn Fn(&Term, &Thm, &Thm) -> Result<Thm>,
    ) -> Result<Thm> {
        let lit0 = mk_int(0i64);
        let refute = |chain: Thm| -> Result<Thm> {
            // chain : posp v = anil.
            hne.clone().not_elim(chain)?.false_elim(goal.clone())
        };
        let nonint = |e: &Thm, iv: Thm| -> Result<Thm> {
            let ctor = e.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
            let acc = apply_def(&self.posp_eq, std::slice::from_ref(&ctor))?;
            let acc = self.fire_if(self.rw_rhs(acc, &[&iv])?)?; // posp ctor = anil
            refute(e.clone().cong_arg(self.posp.clone())?.trans(acc)?)
        };
        self.by_cases(
            v,
            goal,
            tag,
            &|b, e| {
                // Payload split as in natp_inv.
                let disj = coprod_cases(&Type::int(), &Type::bytes(), b)?;
                let bad = || Error::ConnectiveRule("acl2 ord posp_open: bad coprod".into());
                let (or_l, dr) = disj.concl().as_app().ok_or_else(bad)?;
                let (_, dl) = or_l.as_app().ok_or_else(bad)?;
                let (dl, dr) = (dl.clone(), dr.clone());
                let wname = format!("__k{tag}w");
                let br_l = {
                    let pred_l = dl.as_app().ok_or_else(bad)?.1.clone();
                    let w = Term::free(&wname, Type::int());
                    let hyp = Term::app(pred_l, w.clone());
                    let e2 = beta_reduce(Thm::assume(hyp.clone())?)?;
                    let xe = e
                        .clone()
                        .trans(e2.cong_arg(self.th.atom.clone())?)?
                        .trans(self.th.int_unfold(&w)?.sym()?)?; // v = aint w
                    let aw = self.th.aint_at(&w)?;
                    let chain = xe
                        .clone()
                        .cong_arg(self.posp.clone())?
                        .trans(self.posp_int_at(&w)?)?; // posp v = alt '0 (aint w)
                    let hlt = self.ne_nil_transport(hne, &chain)?;
                    let pos = self
                        .pr
                        .alt_iff_at(&self.a0()?, &aw)?
                        .rewrite(&self.pr.intval_int()?.all_elim(lit0.clone())?)?
                        .rewrite(&self.pr.intval_int()?.all_elim(w.clone())?)?
                        .eq_mp(hlt)?; // intLt 0 w
                    let g = k(&w, &xe, &pos)?;
                    let step = g.imp_intro(&hyp)?.all_intro(&wname, Type::int())?;
                    exists_elim(Thm::assume(dl.clone())?, goal.clone(), step)?.imp_intro(&dl)?
                };
                let sname = format!("__k{tag}s");
                let br_r = {
                    let pred_r = dr.as_app().ok_or_else(bad)?.1.clone();
                    let w = Term::free(&sname, Type::bytes());
                    let hyp = Term::app(pred_r, w.clone());
                    let e2 = beta_reduce(Thm::assume(hyp.clone())?)?;
                    let xe = e
                        .clone()
                        .trans(e2.cong_arg(self.th.atom.clone())?)?
                        .trans(self.th.sym_unfold(&w)?.sym()?)?;
                    let g = nonint(&xe, self.pr.intp_sym()?.all_elim(w.clone())?)?;
                    let step = g.imp_intro(&hyp)?.all_intro(&sname, Type::bytes())?;
                    exists_elim(Thm::assume(dr.clone())?, goal.clone(), step)?.imp_intro(&dr)?
                };
                disj.or_elim(br_l, br_r)
            },
            &|e| nonint(e, self.pr.intp_nil()?),
            &|h, t, e| {
                nonint(
                    e,
                    self.pr
                        .intp_cons()?
                        .all_elim(h.clone())?
                        .all_elim(t.clone())?,
                )
            },
        )
    }

    /// Open `hne : Γ ⊢ ¬(op (acons h t) = anil)` down the six `O-P`
    /// guards. The continuation receives, in order:
    /// `e1`, `c1` (fresh terms with `h_eq : ⊢ h = acons e1 c1`),
    /// `op_e1 : ⊢ ¬(op e1 = anil)`, `e1_ne0 : ⊢ ¬(e1 = aint ⌜0⌝)`,
    /// `posp_c1 : ⊢ ¬(posp c1 = anil)`, `op_t : ⊢ ¬(op t = anil)`,
    /// `dec : ⊢ ¬(olt (ofe t) e1 = anil)`.
    #[allow(clippy::too_many_arguments)]
    fn op_cons_open(
        &self,
        h: &Term,
        t: &Term,
        hne: &Thm,
        goal: &Term,
        tag: &str,
        k: &dyn Fn(&Term, &Term, &Thm, &Thm, &Thm, &Thm, &Thm, &Thm) -> Result<Thm>,
    ) -> Result<Thm> {
        // op (acons h t) = aif (aconsp h) (…) anil.
        let hne0 = self.ne_nil_transport(hne, &self.op_cons_at(h, t)?)?;
        let absurd = |_hg: &Thm, hy: &Thm| self.absurd_ne_nil(hy, goal);
        self.aif_ne_split(
            &hne0,
            goal,
            &|hconsp, hx1| {
                // hconsp : ¬(aconsp h = anil) — h is a cons.
                self.consp_open(h, hconsp, goal, &format!("{tag}c"), &|e1, c1, h_eq| {
                    // Rewrite the remaining spine at h = acons e1 c1:
                    // car h → e1, cdr h → t? no — cdr h → c1.
                    let car_h = h_eq
                        .clone()
                        .cong_arg(self.th.car.clone())?
                        .trans(self.th.cs.proj_scons(false, e1, c1)?)?; // car h = e1
                    let cdr_h = h_eq
                        .clone()
                        .cong_arg(self.th.cdr.clone())?
                        .trans(self.th.cs.proj_scons(true, e1, c1)?)?; // cdr h = c1
                    let hx1 = {
                        // ¬(X1 = anil) with car h / cdr h folded to e1 / c1.
                        let (_, eqt) = hx1.concl().as_app().ok_or(Error::NotAnEquation)?;
                        let (x1t, _) = eqt.as_eq().ok_or(Error::NotAnEquation)?;
                        let chain = Thm::refl(x1t.clone())?
                            .rhs_conv(|tm| tm.rw_all(&car_h))?
                            .rhs_conv(|tm| tm.rw_all(&cdr_h))?;
                        self.ne_nil_transport(hx1, &chain)?
                    };
                    // X1 = aif (op e1) (aif (aequal e1 '0) anil (aif (posp c1)
                    //        (aif (op t) (olt (ofe t) e1) anil) anil)) anil.
                    self.aif_ne_split(
                        &hx1,
                        goal,
                        &|op_e1, hx2| {
                            self.aif_ne_split(
                                hx2,
                                goal,
                                // aequal e1 '0 ≠ anil ⟹ value anil — absurd.
                                &absurd,
                                &|hz, hx3| {
                                    // hz : aequal e1 '0 = anil ⟹ e1 ≠ 0.
                                    let e1_ne0 = self.aequal_nil(e1, &self.a0()?, hz)?;
                                    self.aif_ne_split(
                                        hx3,
                                        goal,
                                        &|posp_c1, hx4| {
                                            self.aif_ne_split(
                                                hx4,
                                                goal,
                                                &|op_t, dec| {
                                                    k(
                                                        e1, c1, h_eq, op_e1, &e1_ne0, posp_c1,
                                                        op_t, dec,
                                                    )
                                                },
                                                &absurd,
                                            )
                                        },
                                        &absurd,
                                    )
                                },
                            )
                        },
                        &absurd,
                    )
                })
            },
            &absurd,
        )
    }

    /// `⊢ ∀x. ¬(op x = anil) ⟹ ¬(op (ofe x) = anil)` — the first
    /// exponent of an ordinal is an ordinal (design's `op_fe`).
    pub fn op_fe(&self) -> Result<Thm> {
        let a = self.a();
        let x = self.avar("x");
        let hyp_t = ap1(&self.op, &x)?.equals(self.anil())?.not()?;
        let hop = Thm::assume(hyp_t.clone())?;
        let goal = ap1(&self.op, &ap1(&self.ofe, &x)?)?
            .equals(self.anil())?
            .not()?;
        // Non-cons: ofe x = '0 and op '0 = t.
        let finite = |e: &Thm| -> Result<Thm> {
            let ctor = e.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
            let fe_eq = e
                .clone()
                .cong_arg(self.ofe.clone())?
                .trans(self.ofe_noncons_at(
                    &ctor,
                    &self.consp_val(&ctor).or_else(|_| -> Result<Thm> {
                        // `ctor` may be `aatom b` at a free payload — the
                        // atom law handles it directly.
                        let b = ctor.as_app().ok_or(Error::NotAnEquation)?.1.clone();
                        self.pr.consp_atom()?.all_elim(b)
                    })?,
                )?)?; // ofe x = aint 0
            let op_chain = fe_eq
                .cong_arg(self.op.clone())?
                .trans(self.ord_fold(&ap1(&self.op, &self.a0()?)?)?)?; // op (ofe x) = t
            // ¬(op (ofe x) = anil) from t ≠ anil.
            let concl_eq = ap1(&self.op, &ap1(&self.ofe, &x)?)?.equals(self.anil())?;
            let f = self
                .pr
                .t_ne_nil()?
                .not_elim(op_chain.sym()?.trans(Thm::assume(concl_eq.clone())?)?)?;
            f.imp_intro(&concl_eq)?.not_intro()
        };
        let proved = self.by_cases(
            &x,
            &goal,
            "fe",
            &|_b, e| finite(e),
            &|e| finite(e),
            &|h, t, e| {
                let hne_c = self.ne_nil_transport(&hop, &e.clone().cong_arg(self.op.clone())?)?;
                self.op_cons_open(
                    h,
                    t,
                    &hne_c,
                    &goal,
                    "fe",
                    &|e1, c1, h_eq, op_e1, _ne0, _pc, _opt, _dec| {
                        // ofe x = car h = e1; transport op_e1 backward.
                        let fe_eq = e
                            .clone()
                            .cong_arg(self.ofe.clone())?
                            .trans(self.ofe_cons_at(h, t)?)? // ofe x = car h
                            .trans(
                                h_eq.clone()
                                    .cong_arg(self.th.car.clone())?
                                    .trans(self.th.cs.proj_scons(false, e1, c1)?)?,
                            )?; // = e1
                        let concl_eq = ap1(&self.op, &ap1(&self.ofe, &x)?)?.equals(self.anil())?;
                        let f = op_e1.clone().not_elim(
                            fe_eq
                                .cong_arg(self.op.clone())?
                                .sym()?
                                .trans(Thm::assume(concl_eq.clone())?)?,
                        )?;
                        f.imp_intro(&concl_eq)?.not_intro()
                    },
                )
            },
        )?;
        proved.imp_intro(&hyp_t)?.all_intro("x", a)
    }

    /// `Γ ⊢ intLe a b` from `h : Γ ⊢ intLt a b` (via `le_def`).
    fn int_lt_imp_le(&self, a: &Term, b: &Term, h: Thm) -> Result<Thm> {
        let eq_ab = a.clone().equals(b.clone())?;
        int::le_def()
            .all_elim(a.clone())?
            .all_elim(b.clone())?
            .sym()?
            .eq_mp(h.or_intro_l(eq_ab)?)
    }

    // ------------------------------------------------------------------
    // Well-founded induction over `acc` (the Rust driver)
    // ------------------------------------------------------------------

    /// `⊢ ∀x. acc x ⟹ (motive x)` — well-founded induction.
    /// `prove_case(z, ih)` proves the single β-contraction of
    /// `motive z` given `ih : {…} ⊢ ∀y. below y z ⟹ (motive y)` (motive
    /// instances in applied form). `zname`/`yname` are the fresh
    /// variable names (distinct across nested inductions).
    fn acc_induct(
        &self,
        motive: &Term,
        zname: &str,
        yname: &str,
        prove_case: &dyn Fn(&Term, &Thm) -> Result<Thm>,
    ) -> Result<Thm> {
        let a = self.a();
        let z = Term::free(zname, a.clone());
        let y = Term::free(yname, a.clone());
        let hyp_in = ap2(&self.below, &y, &z)?
            .imp(Term::app(motive.clone(), y.clone()))?
            .forall(yname, a.clone())?;
        let ih = Thm::assume(hyp_in.clone())?;
        let body = prove_case(&z, &ih)?;
        let mz = beta_expand(motive, z.clone(), body)?;
        let step = mz.imp_intro(&hyp_in)?.all_intro(zname, a.clone())?;
        self.acc_elim()?.all_elim(motive.clone())?.imp_elim(step)
    }

    // ------------------------------------------------------------------
    // main_ord (design §6.2–§6.3): every ordinal whose first exponent is
    // equal-or-below an accessible exponent is accessible.
    // ------------------------------------------------------------------

    /// The `Main'` body at `(x, e)`:
    /// `¬(op x = anil) ⟹ ((ofe x = e) ∨ ¬(olt (ofe x) e = anil)) ⟹ acc x`.
    fn m_body(&self, x: &Term, e: &Term) -> Result<Term> {
        let hop = ap1(&self.op, x)?.equals(self.anil())?.not()?;
        let fe = ap1(&self.ofe, x)?;
        let disj = fe
            .clone()
            .equals(e.clone())?
            .or(ap2(&self.olt, &fe, e)?.equals(self.anil())?.not()?)?;
        hop.imp(disj.imp(ap1(&self.acc, x)?)?)
    }

    /// `acc x` for a **non-cons** `x` from `e : x = <leaf ctor>`,
    /// `op_chain : op <ctor> = natp <ctor>`, and `hop : ¬(op x = anil)`
    /// — the shared finite arm (`natp_inv` + L0).
    fn finite_acc(&self, x: &Term, e: &Thm, op_chain: Thm, hop: &Thm) -> Result<Thm> {
        let hne =
            self.ne_nil_transport(hop, &e.clone().cong_arg(self.op.clone())?.trans(op_chain)?)?;
        let ctor = e.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
        let inv = self.natp_inv()?.all_elim(ctor)?.imp_elim(hne)?;
        let goal = ap1(&self.acc, x)?;
        let bad = || Error::ConnectiveRule("acl2 ord finite_acc: bad ∃".into());
        let pred = inv.concl().as_app().ok_or_else(bad)?.1.clone();
        let w = Term::free("__fz", Type::int());
        let hyp = Term::app(pred, w.clone());
        let conj = beta_reduce(Thm::assume(hyp.clone())?)?;
        let ctor_eq = conj.clone().and_elim_l()?;
        let h0 = conj.and_elim_r()?;
        let x_eq = e.clone().trans(ctor_eq)?; // x = aint w
        let acc_w = self.l0_finite_wf()?.all_elim(w.clone())?.imp_elim(h0)?; // acc (aint w)
        let acc_x = acc_w.rewrite(&x_eq.sym()?)?;
        let step = acc_x.imp_intro(&hyp)?.all_intro("__fz", Type::int())?;
        exists_elim(inv, goal, step)
    }

    /// **main_ord** (THE hard proof, design §6.3):
    /// `⊢ ∀e. acc e ⟹ ∀x. ¬(op x = anil) ⟹
    ///    ((ofe x = e) ∨ ¬(olt (ofe x) e = anil)) ⟹ acc x`.
    pub fn main_ord(&self) -> Result<Thm> {
        let a = self.a();
        let m = {
            let ev = Term::free("__me", a.clone());
            let xv = Term::free("__mx", a.clone());
            let body = self.m_body(&xv, &ev)?.forall("__mx", a.clone())?;
            Term::abs(a.clone(), subst::close(&body, "__me"))
        };
        let thm = self.acc_induct(&m, "__we", "__wy1", &|ev, ih_e| self.main_case(ev, ih_e))?;
        crate::init::eq::beta_nf_concl(thm)
    }

    /// The `Main'` closure step at `ev` with `ih_e`.
    fn main_case(&self, ev: &Term, ih_e: &Thm) -> Result<Thm> {
        let a = self.a();
        let anil = self.anil();
        // ME: ∀y. ¬(op y = anil) ⟹ ¬(olt (ofe y) ev = anil) ⟹ acc y.
        let me = {
            let yv = Term::free("__ny", a.clone());
            let fe = ap1(&self.ofe, &yv)?;
            let hop_t = ap1(&self.op, &yv)?.equals(anil.clone())?.not()?;
            let hdec_t = ap2(&self.olt, &fe, ev)?.equals(anil.clone())?.not()?;
            let hop = Thm::assume(hop_t.clone())?;
            let hdec = Thm::assume(hdec_t.clone())?;
            let op_fe_y = self.op_fe()?.all_elim(yv.clone())?.imp_elim(hop.clone())?;
            let below_fe = apply_def(&self.below_eq, &[fe.clone(), ev.clone()])?
                .sym()?
                .eq_mp(op_fe_y.and_intro(hdec)?)?; // below (ofe yv) ev
            let m_fe = beta_reduce(ih_e.clone().all_elim(fe.clone())?.imp_elim(below_fe)?)?; // ∀x. op x ⟹ ((ofe x = ofe yv) ∨ …) ⟹ acc x
            let right = ap2(&self.olt, &fe, &fe)?.equals(anil.clone())?.not()?;
            let disj = Thm::refl(fe.clone())?.or_intro_l(right)?;
            let acc_y = m_fe.all_elim(yv.clone())?.imp_elim(hop)?.imp_elim(disj)?;
            acc_y
                .imp_intro(&hdec_t)?
                .imp_intro(&hop_t)?
                .all_intro("__ny", a.clone())?
        };
        let me_at = |v: &Term, hop: &Thm, hdec: &Thm| -> Result<Thm> {
            me.clone()
                .all_elim(v.clone())?
                .imp_elim(hop.clone())?
                .imp_elim(hdec.clone())
        };

        // Fix x with hop and the disjunction.
        let xv = Term::free("__mx", a.clone());
        let hop_t = ap1(&self.op, &xv)?.equals(anil.clone())?.not()?;
        let hop = Thm::assume(hop_t.clone())?;
        let fex = ap1(&self.ofe, &xv)?;
        let left_t = fex.clone().equals(ev.clone())?;
        let right_t = ap2(&self.olt, &fex, ev)?.equals(anil.clone())?.not()?;
        let disj_t = left_t.clone().or(right_t.clone())?;
        let goal_x = ap1(&self.acc, &xv)?;

        let br_strict = me_at(&xv, &hop, &Thm::assume(right_t.clone())?)?.imp_intro(&right_t)?;
        let br_eq = {
            let he = Thm::assume(left_t.clone())?; // ofe xv = ev
            let inner = self.by_cases(
                &xv,
                &goal_x,
                "mq",
                &|b, e| self.finite_acc(&xv, e, self.op_atom_at(b)?, &hop),
                &|e| self.finite_acc(&xv, e, self.op_nil_at()?, &hop),
                &|h, t, e| {
                    let hne_c =
                        self.ne_nil_transport(&hop, &e.clone().cong_arg(self.op.clone())?)?;
                    self.op_cons_open(
                        h,
                        t,
                        &hne_c,
                        &goal_x,
                        "mo",
                        &|e1, c1, h_eq, _op_e1, _ne0, posp_c1, op_t, dec| {
                            // ev = e1 (through he and ofe at the cons).
                            let car_h = h_eq
                                .clone()
                                .cong_arg(self.th.car.clone())?
                                .trans(self.th.cs.proj_scons(false, e1, c1)?)?;
                            let fe_eq = e
                                .clone()
                                .cong_arg(self.ofe.clone())?
                                .trans(self.ofe_cons_at(h, t)?)?
                                .trans(car_h)?; // ofe xv = e1
                            let ev_eq = he.clone().sym()?.trans(fe_eq)?; // ev = e1
                            self.posp_open(c1, posp_c1, &goal_x, "mp", &|j1, c1_eq, j1_pos| {
                                let q = self.q_lemma(ev, &me)?;
                                let le_j1 =
                                    self.int_lt_imp_le(&mk_int(0i64), j1, j1_pos.clone())?;
                                let q_j1 = q.all_elim(j1.clone())?.imp_elim(le_j1)?; // ∀r. op r ⟹ dec ⟹ acc (acons (acons ev (aint j1)) r)
                                let dec_ev = dec.clone().rewrite(&ev_eq.clone().sym()?)?;
                                let acc_big = q_j1
                                    .all_elim(t.clone())?
                                    .imp_elim(op_t.clone())?
                                    .imp_elim(dec_ev)?;
                                // acc (acons (acons ev (aint j1)) t) → acc xv.
                                acc_big
                                    .rewrite(&c1_eq.clone().sym()?)? // aint j1 → c1
                                    .rewrite(&ev_eq.clone())? // ev → e1
                                    .rewrite(&h_eq.clone().sym()?)? // acons e1 c1 → h
                                    .rewrite(&e.clone().sym()?) // acons h t → xv
                            })
                        },
                    )
                },
            )?;
            inner.imp_intro(&left_t)?
        };
        let acc_x = Thm::assume(disj_t.clone())?.or_elim(br_eq, br_strict)?;
        acc_x
            .imp_intro(&disj_t)?
            .imp_intro(&hop_t)?
            .all_intro("__mx", a)
    }

    /// The coefficient-induction lemma `Q` at a fixed `ev` (with `ME` in
    /// scope): `⊢ ∀c:int. 0 ≤ c ⟹ ∀r. ¬(op r = anil) ⟹
    /// ¬(olt (ofe r) ev = anil) ⟹ acc (acons (acons ev (aint c)) r)`.
    fn q_lemma(&self, ev: &Term, me: &Thm) -> Result<Thm> {
        let a = self.a();
        let qm = {
            let cv = Term::free("__qc0", Type::int());
            let rv = Term::free("__qr0", a.clone());
            let xhat = self.acons_t(&self.acons_t(ev, &self.th.aint_at(&cv)?)?, &rv)?;
            let body = ap1(&self.op, &rv)?
                .equals(self.anil())?
                .not()?
                .imp(
                    ap2(&self.olt, &ap1(&self.ofe, &rv)?, ev)?
                        .equals(self.anil())?
                        .not()?
                        .imp(ap1(&self.acc, &xhat)?)?,
                )?
                .forall("__qr0", a.clone())?;
            Term::abs(Type::int(), subst::close(&body, "__qc0"))
        };
        nonneg_si_on("__qc", &qm, |cv, _hnn, ih_c| self.q_case(ev, cv, ih_c, me))
    }

    /// The `Q` closure step at coefficient value `cv` (design §6.3's
    /// rest induction, run through the inner `acc_induct`).
    fn q_case(&self, ev: &Term, cv: &Term, ih_c: &Thm, me: &Thm) -> Result<Thm> {
        let a = self.a();
        let anil = self.anil();
        // N := λr. ¬(op r = anil) ⟹ ¬(olt (ofe r) ev = anil) ⟹
        //          acc (acons (acons ev (aint cv)) r).
        let nm = {
            let rv = Term::free("__nr0", a.clone());
            let xhat = self.acons_t(&self.acons_t(ev, &self.th.aint_at(cv)?)?, &rv)?;
            let body = ap1(&self.op, &rv)?.equals(anil.clone())?.not()?.imp(
                ap2(&self.olt, &ap1(&self.ofe, &rv)?, ev)?
                    .equals(anil.clone())?
                    .not()?
                    .imp(ap1(&self.acc, &xhat)?)?,
            )?;
            Term::abs(a.clone(), subst::close(&body, "__nr0"))
        };
        let n_all = self.acc_induct(&nm, "__wr", "__wy2", &|zv, ih_r| {
            self.n_case(ev, cv, zv, ih_r, ih_c, me)
        })?; // ∀x. acc x ⟹ (N x)
        // Close: ∀r. op r ⟹ dec ⟹ acc X̂(r), from acc r via ME.
        let rv = Term::free("__qr", a.clone());
        let hop_t = ap1(&self.op, &rv)?.equals(anil.clone())?.not()?;
        let hdec_t = ap2(&self.olt, &ap1(&self.ofe, &rv)?, ev)?
            .equals(anil.clone())?
            .not()?;
        let hop = Thm::assume(hop_t.clone())?;
        let hdec = Thm::assume(hdec_t.clone())?;
        let acc_r = me
            .clone()
            .all_elim(rv.clone())?
            .imp_elim(hop.clone())?
            .imp_elim(hdec.clone())?;
        let n_r = beta_reduce(n_all.all_elim(rv.clone())?.imp_elim(acc_r)?)?;
        let out = n_r.imp_elim(hop)?.imp_elim(hdec)?;
        out.imp_intro(&hdec_t)?
            .imp_intro(&hop_t)?
            .all_intro("__qr", a)
    }

    /// The `N` closure step at `zv` — the `acc_intro` body with the
    /// 4-way `o<`-inversion (design §6.3, cases 1–4), inlined as guard
    /// splits.
    #[allow(clippy::too_many_arguments)]
    fn n_case(
        &self,
        ev: &Term,
        cv: &Term,
        zv: &Term,
        ih_r: &Thm,
        ih_c: &Thm,
        me: &Thm,
    ) -> Result<Thm> {
        let a = self.a();
        let anil = self.anil();
        let acv = self.th.aint_at(cv)?;
        let head = self.acons_t(ev, &acv)?; // acons ev (aint cv)
        let xhat = self.acons_t(&head, zv)?;
        let hop_z_t = ap1(&self.op, zv)?.equals(anil.clone())?.not()?;
        let hdec_z_t = ap2(&self.olt, &ap1(&self.ofe, zv)?, ev)?
            .equals(anil.clone())?
            .not()?;

        // acc X̂(zv) by acc_intro.
        let yv = Term::free("__qy", a.clone());
        let r_t = ap2(&self.below, &yv, &xhat)?;
        let opened = apply_def(&self.below_eq, &[yv.clone(), xhat.clone()])?
            .eq_mp(Thm::assume(r_t.clone())?)?;
        let (hop_y, holt_y) = opened.conjuncts()?;
        let goal_y = ap1(&self.acc, &yv)?;

        let acc_y = self.by_cases(
            &yv,
            &goal_y,
            "nz",
            &|b, ey| self.finite_acc(&yv, ey, self.op_atom_at(b)?, &hop_y),
            &|ey| self.finite_acc(&yv, ey, self.op_nil_at()?, &hop_y),
            &|hy, ry, ey| {
                let hne_y =
                    self.ne_nil_transport(&hop_y, &ey.clone().cong_arg(self.op.clone())?)?;
                self.op_cons_open(
                    hy,
                    ry,
                    &hne_y,
                    &goal_y,
                    "ny",
                    &|ey1, cy1, hy_eq, _op_ey1, _ne0y, posp_cy1, op_ry, dec_y| {
                        // Unfold olt yv X̂ at cons/cons and pre-rewrite all
                        // projections.
                        let car_hy = hy_eq
                            .clone()
                            .cong_arg(self.th.car.clone())?
                            .trans(self.th.cs.proj_scons(false, ey1, cy1)?)?;
                        let cdr_hy = hy_eq
                            .clone()
                            .cong_arg(self.th.cdr.clone())?
                            .trans(self.th.cs.proj_scons(true, ey1, cy1)?)?;
                        let law = self.olt_cons_at(hy, ry, &xhat)?;
                        let law = self.rw_rhs(
                            law,
                            &[
                                &car_hy,
                                &cdr_hy,
                                &self.th.cs.proj_scons(false, &head, zv)?, // car X̂ → head
                                &self.th.cs.proj_scons(true, &head, zv)?,  // cdr X̂ → zv
                                &self.th.cs.proj_scons(false, ev, &acv)?,  // car head → ev
                                &self.th.cs.proj_scons(true, ev, &acv)?,   // cdr head → aint cv
                                &self.consp_cons_at(&head, zv)?,
                            ],
                        )?;
                        let law = self.fire_if(law)?; // outer aconsp X̂ = t fired
                        // holt at yv transported to the split shape.
                        let holt2 = self.ne_nil_transport(
                            &holt_y,
                            &ey.clone()
                                .cong_arg(self.olt.clone())?
                                .cong_fn(xhat.clone())?
                                .trans(law)?,
                        )?;
                        // ofe yv = ey1 (shared by the strict/coeff/rest arms).
                        let fe_y = ey
                            .clone()
                            .cong_arg(self.ofe.clone())?
                            .trans(self.ofe_cons_at(hy, ry)?)?
                            .trans(car_hy.clone())?; // ofe yv = ey1
                        self.aif_ne_split(
                            &holt2,
                            &goal_y,
                            &|heq_ne, hin| {
                                // ey1 = ev.
                                let ey1_eq_ev = self.aequal_holds(ey1, ev, heq_ne)?;
                                self.aif_ne_split(
                                    hin,
                                    &goal_y,
                                    &|hceq_ne, hrest| {
                                        // REST: cy1 = aint cv; below ry zv → IH_r.
                                        let cy1_eq = self.aequal_holds(cy1, &acv, hceq_ne)?;
                                        let below_ry =
                                            apply_def(&self.below_eq, &[ry.clone(), zv.clone()])?
                                                .sym()?
                                                .eq_mp(op_ry.clone().and_intro(hrest.clone())?)?;
                                        let n_ry = beta_reduce(
                                            ih_r.clone()
                                                .all_elim(ry.clone())?
                                                .imp_elim(below_ry)?,
                                        )?;
                                        let dec_ev = dec_y.clone().rewrite(&ey1_eq_ev.clone())?;
                                        let acc_big =
                                            n_ry.imp_elim(op_ry.clone())?.imp_elim(dec_ev)?;
                                        acc_big
                                            .rewrite(&cy1_eq.sym()?)? // aint cv → cy1
                                            .rewrite(&ey1_eq_ev.clone().sym()?)? // ev → ey1
                                            .rewrite(&hy_eq.clone().sym()?)?
                                            .rewrite(&ey.clone().sym()?)
                                    },
                                    &|hceq, halt| {
                                        // COEFF: cy1 < cv strictly.
                                        let _ = hceq;
                                        self.posp_open(
                                            cy1,
                                            posp_cy1,
                                            &goal_y,
                                            "nc",
                                            &|jy, cy1_eq, _jy_pos| {
                                                let ajy = self.th.aint_at(jy)?;
                                                let halt2 =
                                                    halt.clone().rewrite(&cy1_eq.clone())?; // ¬(alt (aint jy)(aint cv) = anil)
                                                let ilt = self
                                                    .pr
                                                    .alt_iff_at(&ajy, &acv)?
                                                    .rewrite(
                                                        &self
                                                            .pr
                                                            .intval_int()?
                                                            .all_elim(jy.clone())?,
                                                    )?
                                                    .rewrite(
                                                        &self
                                                            .pr
                                                            .intval_int()?
                                                            .all_elim(cv.clone())?,
                                                    )?
                                                    .eq_mp(halt2)?; // intLt jy cv
                                                let le0jy = self.int_lt_imp_le(
                                                    &mk_int(0i64),
                                                    jy,
                                                    _jy_pos.clone(),
                                                )?;
                                                let q_jy = beta_reduce(
                                                    ih_c.clone()
                                                        .all_elim(jy.clone())?
                                                        .imp_elim(le0jy)?
                                                        .imp_elim(ilt)?,
                                                )?;
                                                let dec_ev =
                                                    dec_y.clone().rewrite(&ey1_eq_ev.clone())?;
                                                let acc_big = q_jy
                                                    .all_elim(ry.clone())?
                                                    .imp_elim(op_ry.clone())?
                                                    .imp_elim(dec_ev)?;
                                                acc_big
                                                    .rewrite(&cy1_eq.clone().sym()?)? // aint jy → cy1
                                                    .rewrite(&ey1_eq_ev.clone().sym()?)? // ev → ey1
                                                    .rewrite(&hy_eq.clone().sym()?)?
                                                    .rewrite(&ey.clone().sym()?)
                                            },
                                        )
                                    },
                                )
                            },
                            &|_heq, hstrict| {
                                // STRICT: olt ey1 ev ≠ anil → ME.
                                let chain = fe_y
                                    .clone()
                                    .cong_arg(self.olt.clone())?
                                    .cong_fn(ev.clone())?; // olt (ofe yv) ev = olt ey1 ev
                                let hdec = self.ne_nil_transport(hstrict, &chain.sym()?)?;
                                me.clone()
                                    .all_elim(yv.clone())?
                                    .imp_elim(hop_y.clone())?
                                    .imp_elim(hdec)
                            },
                        )
                    },
                )
            },
        )?;
        let prem = acc_y.imp_intro(&r_t)?.all_intro("__qy", a.clone())?;
        let acc_xhat = self.acc_intro()?.all_elim(xhat)?.imp_elim(prem)?;
        acc_xhat.imp_intro(&hdec_z_t)?.imp_intro(&hop_z_t)
    }

    // ------------------------------------------------------------------
    // Grading + THE well-foundedness theorem (design §6.4)
    // ------------------------------------------------------------------

    /// `⊢ ∀k:nat. (graded body k)` with body
    /// `∀x. ¬(op x = anil) ⟹ natLe (ht x) k ⟹ acc x` (motive-applied
    /// form under the binder) — the tower-height grading, by plain `nat`
    /// induction; the IH is used at the *first exponent* (a different
    /// `x`), which is why the plain induction suffices.
    fn graded_wf_raw(&self) -> Result<Thm> {
        let a = self.a();
        let anil = self.anil();
        let nle = |u: &Term, v: &Term| -> Result<Term> {
            Ok(Term::app(
                Term::app(crate::init::nat::nat_le(), u.clone()),
                v.clone(),
            ))
        };
        // P := λk. ∀x. op x ⟹ ht x ≤ k ⟹ acc x.
        let p = {
            let kv = Term::free("__gk", Type::nat());
            let xv = Term::free("__gx", a.clone());
            let body = ap1(&self.op, &xv)?
                .equals(anil.clone())?
                .not()?
                .imp(nle(&ap1(&self.ht, &xv)?, &kv)?.imp(ap1(&self.acc, &xv)?)?)?
                .forall("__gx", a.clone())?;
            Term::abs(Type::nat(), subst::close(&body, "__gk"))
        };
        // Base: k = 0 — a cons has successor height, so x is a leaf.
        let base = {
            let xv = Term::free("__gx", a.clone());
            let hop_t = ap1(&self.op, &xv)?.equals(anil.clone())?.not()?;
            let hle_t = nle(&ap1(&self.ht, &xv)?, &crate::init::nat::zero())?;
            let hop = Thm::assume(hop_t.clone())?;
            let hle = Thm::assume(hle_t.clone())?;
            let goal = ap1(&self.acc, &xv)?;
            let inner = self.by_cases(
                &xv,
                &goal,
                "gz",
                &|b, e| self.finite_acc(&xv, e, self.op_atom_at(b)?, &hop),
                &|e| self.finite_acc(&xv, e, self.op_nil_at()?, &hop),
                &|h, t, e| {
                    // ht x = S (ht (car h)) ≤ 0 — absurd.
                    let ht_eq = e
                        .clone()
                        .cong_arg(self.ht.clone())?
                        .trans(self.ht_cons_at(h, t)?)?;
                    let bad = hle.clone().rewrite(&ht_eq)?; // S (ht (car h)) ≤ 0
                    crate::init::nat::not_succ_le_zero()
                        .all_elim(ap1(&self.ht, &ap1(&self.th.car, h)?)?)?
                        .not_elim(bad)?
                        .false_elim(goal.clone())
                },
            )?;
            let body = inner
                .imp_intro(&hle_t)?
                .imp_intro(&hop_t)?
                .all_intro("__gx", a.clone())?;
            beta_expand(&p, crate::init::nat::zero(), body)?
        };
        // Step: k ↦ S k, via op_fe + the IH at the first exponent +
        // main_ord's equal disjunct.
        let step = {
            let kv = Term::free("__gk", Type::nat());
            let ih_redex = Term::app(p.clone(), kv.clone());
            let ih = beta_reduce(Thm::assume(ih_redex.clone())?)?;
            let xv = Term::free("__gx", a.clone());
            let hop_t = ap1(&self.op, &xv)?.equals(anil.clone())?.not()?;
            let hle_t = nle(&ap1(&self.ht, &xv)?, &crate::init::nat::succ(kv.clone()))?;
            let hop = Thm::assume(hop_t.clone())?;
            let hle = Thm::assume(hle_t.clone())?;
            let goal = ap1(&self.acc, &xv)?;
            let inner = self.by_cases(
                &xv,
                &goal,
                "gs",
                &|b, e| self.finite_acc(&xv, e, self.op_atom_at(b)?, &hop),
                &|e| self.finite_acc(&xv, e, self.op_nil_at()?, &hop),
                &|h, t, e| {
                    let car_h = ap1(&self.th.car, h)?;
                    // ht (car h) ≤ k (successor cancellation).
                    let ht_eq = e
                        .clone()
                        .cong_arg(self.ht.clone())?
                        .trans(self.ht_cons_at(h, t)?)?;
                    let hle2 = hle.clone().rewrite(&ht_eq)?; // S (ht (car h)) ≤ S k
                    let hle3 = crate::init::nat::le_succ_succ()
                        .all_elim(ap1(&self.ht, &car_h)?)?
                        .all_elim(kv.clone())?
                        .eq_mp(hle2)?; // ht (car h) ≤ k
                    // op (car h) via op_fe + ofe x = car h.
                    let fe_eq = e
                        .clone()
                        .cong_arg(self.ofe.clone())?
                        .trans(self.ofe_cons_at(h, t)?)?; // ofe xv = car h
                    let op_fe_x = self.op_fe()?.all_elim(xv.clone())?.imp_elim(hop.clone())?; // ¬(op (ofe xv) = anil)
                    let op_car =
                        self.ne_nil_transport(&op_fe_x, &fe_eq.clone().cong_arg(self.op.clone())?)?; // ¬(op (car h) = anil)
                    // IH at car h → acc (car h).
                    let acc_car = ih
                        .clone()
                        .all_elim(car_h.clone())?
                        .imp_elim(op_car.clone())?
                        .imp_elim(hle3)?;
                    // main_ord at e := car h, equal disjunct (the
                    // conclusion is already β-normal).
                    let m = self
                        .main_ord()?
                        .all_elim(car_h.clone())?
                        .imp_elim(acc_car)?;
                    let right = ap2(&self.olt, &ap1(&self.ofe, &xv)?, &car_h)?
                        .equals(anil.clone())?
                        .not()?;
                    let disj = fe_eq.or_intro_l(right)?;
                    m.all_elim(xv.clone())?
                        .imp_elim(hop.clone())?
                        .imp_elim(disj)
                },
            )?;
            let body = inner
                .imp_intro(&hle_t)?
                .imp_intro(&hop_t)?
                .all_intro("__gx", a.clone())?;
            beta_expand(&p, crate::init::nat::succ(kv), body)?.imp_intro(&ih_redex)?
        };
        crate::init::ext::nat_induct(base, step)
    }

    /// **graded_wf** (clean form): `⊢ ∀k. ∀x. ¬(op x = anil) ⟹
    /// natLe (ht x) k ⟹ acc x`.
    pub fn graded_wf(&self) -> Result<Thm> {
        crate::init::eq::beta_nf_concl(self.graded_wf_raw()?)
    }

    /// **THE S5 well-foundedness theorem — full ε₀** (design §6.4):
    /// `⊢ ∀x. ¬(op x = anil) ⟹ acc x`. The grade is discharged
    /// internally at `k := ht x`; no meta-level fragment cap.
    pub fn wf(&self) -> Result<Thm> {
        let a = self.a();
        let x = self.avar("x");
        let hop_t = ap1(&self.op, &x)?.equals(self.anil())?.not()?;
        let hop = Thm::assume(hop_t.clone())?;
        let htx = ap1(&self.ht, &x)?;
        let g = beta_reduce(self.graded_wf_raw()?.all_elim(htx.clone())?)?;
        let refl_le = crate::init::nat::le_refl().all_elim(htx)?;
        g.all_elim(x.clone())?
            .imp_elim(hop)?
            .imp_elim(refl_le)?
            .imp_intro(&hop_t)?
            .all_intro("x", a)
    }

    /// **wf_induct**: `⊢ ∀S. (∀z. (∀y. below y z ⟹ S y) ⟹ S z) ⟹
    /// ∀x. ¬(op x = anil) ⟹ S x` — well-founded induction over all
    /// ordinal notations ([`Ordinals::wf`] + [`Ordinals::acc_elim`]).
    pub fn wf_induct(&self) -> Result<Thm> {
        let a = self.a();
        let sb = Type::fun(a.clone(), Type::bool());
        let s = Term::free("__wS", sb.clone());
        let hs = self.acc_step_at(&s)?;
        let x = Term::free("__wx", a.clone());
        let hop_t = ap1(&self.op, &x)?.equals(self.anil())?.not()?;
        let acc_x = self
            .wf()?
            .all_elim(x.clone())?
            .imp_elim(Thm::assume(hop_t.clone())?)?;
        let sx = self
            .acc_elim()?
            .all_elim(s.clone())?
            .imp_elim(Thm::assume(hs.clone())?)?
            .all_elim(x.clone())?
            .imp_elim(acc_x)?;
        sx.imp_intro(&hop_t)?
            .all_intro("__wx", a)?
            .imp_intro(&hs)?
            .all_intro("__wS", sb)
    }

    // ------------------------------------------------------------------
    // L0 — well-foundedness below ω (design §6.1)
    // ------------------------------------------------------------------

    /// **L0 (the "below ω" milestone):**
    /// `⊢ ∀i:int. intLe ⌜0⌝ i ⟹ acc (aint i)` — every finite ordinal is
    /// accessible, by strong induction on the nonnegative ints
    /// ([`nonneg_si_on`]) closing with `acc_intro` + [`Ordinals::olt_fin_inv`].
    pub fn l0_finite_wf(&self) -> Result<Thm> {
        let a = self.a();
        let motive = {
            let iv = Term::free("__li", Type::int());
            let body = ap1(&self.acc, &self.th.aint_at(&iv)?)?;
            Term::abs(Type::int(), subst::close(&body, "__li"))
        };
        nonneg_si_on("i", &motive, |iv, _hnn, ih| {
            let aiv = self.th.aint_at(iv)?;
            let y = Term::free("__oy", a.clone());
            let r_t = ap2(&self.below, &y, &aiv)?;
            // Open `below y (aint iv)`.
            let opened = apply_def(&self.below_eq, &[y.clone(), aiv.clone()])?
                .eq_mp(Thm::assume(r_t.clone())?)?;
            let (hop, holt) = opened.conjuncts()?;
            // ∃j. y = aint j ∧ (0 ≤ j ∧ j < iv).
            let inv = self
                .olt_fin_inv()?
                .all_elim(y.clone())?
                .all_elim(iv.clone())?
                .imp_elim(hop)?
                .imp_elim(holt)?;
            let goal_y = ap1(&self.acc, &y)?;
            let bad = || Error::ConnectiveRule("acl2 ord l0: bad ∃".into());
            let pred_j = inv.concl().as_app().ok_or_else(bad)?.1.clone();
            let j = Term::free("__oj", Type::int());
            let hyp = Term::app(pred_j, j.clone());
            let conj = beta_reduce(Thm::assume(hyp.clone())?)?;
            let y_eq = conj.clone().and_elim_l()?; // y = aint j
            let rest = conj.and_elim_r()?;
            let h0 = rest.clone().and_elim_l()?; // 0 ≤ j
            let hlt = rest.and_elim_r()?; // j < iv
            let acc_j = beta_reduce(
                ih.clone()
                    .all_elim(j.clone())?
                    .imp_elim(h0)?
                    .imp_elim(hlt)?,
            )?; // acc (aint j)
            let acc_y = acc_j.rewrite(&y_eq.sym()?)?; // acc y
            let step = acc_y.imp_intro(&hyp)?.all_intro("__oj", Type::int())?;
            let acc_y = exists_elim(inv, goal_y, step)?; // {r_t} ⊢ acc y
            let prem = acc_y.imp_intro(&r_t)?.all_intro("__oy", a.clone())?;
            self.acc_intro()?.all_elim(aiv)?.imp_elim(prem)
        })
    }

    // ------------------------------------------------------------------
    // S5c — int-order plumbing for the typed-arithmetic pack (design §8)
    // ------------------------------------------------------------------

    /// `intval x`.
    fn iv(&self, x: &Term) -> Result<Term> {
        self.pr.intval.clone().apply(x.clone())
    }

    /// `⊢ aint ⌜1⌝`.
    fn a1(&self) -> Result<Term> {
        self.th.aint_at(&mk_int(1i64))
    }

    /// From `chain : Γ ⊢ X = t`, conclude `Γ ⊢ ¬(X = anil)`.
    fn holds_of_eq_t(&self, chain: Thm) -> Result<Thm> {
        let x = chain.concl().as_eq().ok_or(Error::NotAnEquation)?.0.clone();
        let eq = x.equals(self.anil())?;
        let f = self
            .pr
            .t_ne_nil()?
            .not_elim(chain.sym()?.trans(Thm::assume(eq.clone())?)?)?;
        f.imp_intro(&eq)?.not_intro()
    }

    /// From `hn : Γ ⊢ ¬(intLt (intval x) (intval y))`, conclude
    /// `Γ ⊢ alt x y = anil` (fire the `alt` guard to `⌜F⌝`).
    fn alt_nil_of_not_lt(&self, x: &Term, y: &Term, hn: Thm) -> Result<Thm> {
        let gf = eqf_intro(hn)?; // (intLt (iv x) (iv y)) = ⌜F⌝
        self.pr
            .alt_unfold(x, y)?
            .rhs_conv(|tm| tm.rw_all(&gf))?
            .rhs_conv(crate::init::cond::collapse_conds)
    }

    /// From `hg : Γ ⊢ alt x y = anil`, conclude
    /// `Γ ⊢ ¬(intLt (intval x) (intval y))` (contrapose [`Prims::alt_iff_at`]).
    fn not_lt_of_alt_nil(&self, x: &Term, y: &Term, hg: Thm) -> Result<Thm> {
        let lt_t = int::int_lt().apply(self.iv(x)?)?.apply(self.iv(y)?)?;
        let holds = self
            .pr
            .alt_iff_at(x, y)?
            .sym()?
            .eq_mp(Thm::assume(lt_t.clone())?)?; // {lt} ⊢ ¬(alt x y = anil)
        holds.not_elim(hg)?.imp_intro(&lt_t)?.not_intro()
    }

    /// Transport `hn : Γ ⊢ ¬P` along `eq : Δ ⊢ P = Q` to `Γ∪Δ ⊢ ¬Q`.
    fn not_transport(&self, hn: Thm, eq: Thm) -> Result<Thm> {
        let q = eq.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
        let p_thm = eq.sym()?.eq_mp(Thm::assume(q.clone())?)?; // {Q} ⊢ P
        hn.not_elim(p_thm)?.imp_intro(&q)?.not_intro()
    }

    /// `⊢ intAdd ⌜0⌝ x = x` at a fixed term.
    fn zero_add_at(&self, x: &Term) -> Result<Thm> {
        int::add_comm()
            .all_elim(mk_int(0i64))?
            .all_elim(x.clone())? // 0+x = x+0
            .trans(int::add_zero().all_elim(x.clone())?) // = x
    }

    /// `Γ ⊢ intLe (a+c) (b+c)` from `h : Γ ⊢ intLe a b` (`le_def` split
    /// over [`crate::init::int::lt_add_mono`]).
    fn le_add_mono_at(&self, a: &Term, b: &Term, c: &Term, h: Thm) -> Result<Thm> {
        let add = |u: &Term, v: &Term| -> Result<Term> {
            int::int_add().apply(u.clone())?.apply(v.clone())
        };
        let (ac, bc) = (add(a, c)?, add(b, c)?);
        let led_out = int::le_def().all_elim(ac.clone())?.all_elim(bc.clone())?;
        let disj = int::le_def()
            .all_elim(a.clone())?
            .all_elim(b.clone())?
            .eq_mp(h)?; // (a<b) ∨ (a=b)
        let lt_t = int::int_lt().apply(a.clone())?.apply(b.clone())?;
        let eq_t = a.clone().equals(b.clone())?;
        let br_lt = {
            let ltc = int::lt_add_mono()
                .all_elim(a.clone())?
                .all_elim(b.clone())?
                .all_elim(c.clone())?
                .imp_elim(Thm::assume(lt_t.clone())?)?; // a+c < b+c
            led_out
                .clone()
                .sym()?
                .eq_mp(ltc.or_intro_l(ac.clone().equals(bc.clone())?)?)?
                .imp_intro(&lt_t)?
        };
        let br_eq = {
            let eqc = Thm::assume(eq_t.clone())?
                .cong_arg(int::int_add())?
                .cong_fn(c.clone())?; // a+c = b+c
            led_out
                .sym()?
                .eq_mp(eqc.or_intro_r(int::int_lt().apply(ac)?.apply(bc)?)?)?
                .imp_intro(&eq_t)?
        };
        disj.or_elim(br_lt, br_eq)
    }

    /// `Γ ⊢ ¬(intLt a b)` from `hle : Γ ⊢ intLe b a` (irreflexivity).
    fn not_lt_of_ge(&self, a: &Term, b: &Term, hle: Thm) -> Result<Thm> {
        let lt_t = int::int_lt().apply(a.clone())?.apply(b.clone())?;
        let bb = int::lt_of_le_of_lt()
            .all_elim(b.clone())?
            .all_elim(a.clone())?
            .all_elim(b.clone())?
            .imp_elim(hle)?
            .imp_elim(Thm::assume(lt_t.clone())?)?; // b < b
        int::lt_irrefl()
            .all_elim(b.clone())?
            .not_elim(bb)?
            .imp_intro(&lt_t)?
            .not_intro()
    }

    /// From `hne : Γ ⊢ ¬(aequal (alt x '0) anil = anil)` (the evaluated
    /// `(EQUAL (< x '0) 'NIL)` antecedent), conclude
    /// `Γ ⊢ intLe ⌜0⌝ (intval x)`.
    fn nonneg_of_hne(&self, x: &Term, hne: &Thm) -> Result<Thm> {
        let a0 = self.a0()?;
        let alt_x0 = ap2(&self.pr.lt, x, &a0)?;
        let eq_nil = self.aequal_holds(&alt_x0, &self.anil(), hne)?; // alt x '0 = anil
        let hn = self.not_lt_of_alt_nil(x, &a0, eq_nil)?; // ¬(intLt (iv x) (iv '0))
        let iv0 = self.pr.intval_int()?.all_elim(mk_int(0i64))?; // intval (aint 0) = 0
        let hn = hn.rewrite(&iv0)?; // ¬(intLt (iv x) 0)
        self.int_ge_of_not_lt(&self.iv(x)?, &mk_int(0i64), hn) // 0 ≤ iv x
    }

    // ------------------------------------------------------------------
    // S5c — the typed-arithmetic pack's model theorems (design §8)
    // ------------------------------------------------------------------

    /// `⊢ ∀A B. aconsp (aplus A B) = anil`.
    fn consp_plus_thm(&self) -> Result<Thm> {
        let a = self.a();
        let (xa, xb) = (self.avar("A"), self.avar("B"));
        let unf = self.pr.plus_unfold(&xa, &xb)?; // aplus A B = aint z
        let z = unf
            .concl()
            .as_eq()
            .ok_or(Error::NotAnEquation)?
            .1
            .as_app()
            .ok_or(Error::NotAnEquation)?
            .1
            .clone();
        unf.cong_arg(self.pr.consp.clone())?
            .trans(self.consp_int_at(&z)?)?
            .all_intro("B", a.clone())?
            .all_intro("A", a)
    }

    /// `⊢ ∀A. aconsp (aneg A) = anil`.
    fn consp_neg_thm(&self) -> Result<Thm> {
        let a = self.a();
        let xa = self.avar("A");
        let unf = self.pr.neg_unfold(&xa)?; // aneg A = aint z
        let z = unf
            .concl()
            .as_eq()
            .ok_or(Error::NotAnEquation)?
            .1
            .as_app()
            .ok_or(Error::NotAnEquation)?
            .1
            .clone();
        unf.cong_arg(self.pr.consp.clone())?
            .trans(self.consp_int_at(&z)?)?
            .all_intro("A", a)
    }

    /// `⊢ ∀A B. ¬(aintp (aplus A B) = anil)`.
    fn intp_plus_thm(&self) -> Result<Thm> {
        let a = self.a();
        let (xa, xb) = (self.avar("A"), self.avar("B"));
        let unf = self.pr.plus_unfold(&xa, &xb)?;
        let z = unf
            .concl()
            .as_eq()
            .ok_or(Error::NotAnEquation)?
            .1
            .as_app()
            .ok_or(Error::NotAnEquation)?
            .1
            .clone();
        let chain = unf
            .cong_arg(self.pr.intp.clone())?
            .trans(self.pr.intp_int()?.all_elim(z)?)?; // aintp (aplus A B) = t
        self.holds_of_eq_t(chain)?
            .all_intro("B", a.clone())?
            .all_intro("A", a)
    }

    /// `⊢ ∀A. ¬(aintp (aneg A) = anil)`.
    fn intp_neg_thm(&self) -> Result<Thm> {
        let a = self.a();
        let xa = self.avar("A");
        let unf = self.pr.neg_unfold(&xa)?;
        let z = unf
            .concl()
            .as_eq()
            .ok_or(Error::NotAnEquation)?
            .1
            .as_app()
            .ok_or(Error::NotAnEquation)?
            .1
            .clone();
        let chain = unf
            .cong_arg(self.pr.intp.clone())?
            .trans(self.pr.intp_int()?.all_elim(z)?)?;
        self.holds_of_eq_t(chain)?.all_intro("A", a)
    }

    /// `⊢ ∀X. ¬(aintp X = anil) ⟹ (aconsp X = anil)` — integers are not
    /// conses (carrier case analysis; the cons case refutes the premise).
    fn intp_not_consp_thm(&self) -> Result<Thm> {
        let a = self.a();
        let x = self.avar("X");
        let hyp_t = ap1(&self.pr.intp, &x)?.equals(self.anil())?.not()?;
        let hne = Thm::assume(hyp_t.clone())?;
        let goal = ap1(&self.pr.consp, &x)?.equals(self.anil())?;
        let proved = self.by_cases(
            &x,
            &goal,
            "nc",
            &|b, e| {
                e.clone()
                    .cong_arg(self.pr.consp.clone())?
                    .trans(self.pr.consp_atom()?.all_elim(b.clone())?)
            },
            &|e| {
                e.clone()
                    .cong_arg(self.pr.consp.clone())?
                    .trans(self.pr.consp_nil()?)
            },
            &|h, t, e| {
                let intp_nil = e.clone().cong_arg(self.pr.intp.clone())?.trans(
                    self.pr
                        .intp_cons()?
                        .all_elim(h.clone())?
                        .all_elim(t.clone())?,
                )?;
                hne.clone().not_elim(intp_nil)?.false_elim(goal.clone())
            },
        )?;
        proved.imp_intro(&hyp_t)?.all_intro("X", a)
    }

    /// `⊢ ∀A B. ¬(aequal (alt A '0) anil = anil) ⟹
    /// ¬(aequal (alt B '0) anil = anil) ⟹ (alt (aplus A B) '0 = anil)` —
    /// nonnegative ints are closed under `+` (via `intval` completion, so
    /// it holds for **all** carrier values).
    fn plus_nonneg_thm(&self) -> Result<Thm> {
        let a = self.a();
        let anil = self.anil();
        let a0 = self.a0()?;
        let lit0 = mk_int(0i64);
        let (xa, xb) = (self.avar("A"), self.avar("B"));
        let ng = |x: &Term| -> Result<Term> {
            ap2(&self.pr.equal, &ap2(&self.pr.lt, x, &a0)?, &anil)?
                .equals(anil.clone())?
                .not()
        };
        let (ng_a, ng_b) = (ng(&xa)?, ng(&xb)?);
        let ha = self.nonneg_of_hne(&xa, &Thm::assume(ng_a.clone())?)?; // 0 ≤ va
        let hb = self.nonneg_of_hne(&xb, &Thm::assume(ng_b.clone())?)?; // 0 ≤ vb
        let (va, vb) = (self.iv(&xa)?, self.iv(&xb)?);
        let vab = int::int_add().apply(va.clone())?.apply(vb.clone())?;
        // vb ≤ va+vb (mono at 0 ≤ va), then 0 ≤ va+vb by transitivity.
        let s1 = self
            .le_add_mono_at(&lit0, &va, &vb, ha)? // 0+vb ≤ va+vb
            .rewrite(&self.zero_add_at(&vb)?)?; // vb ≤ va+vb
        let s2 = int::le_trans()
            .all_elim(lit0.clone())?
            .all_elim(vb.clone())?
            .all_elim(vab.clone())?
            .imp_elim(hb)?
            .imp_elim(s1)?; // 0 ≤ va+vb
        let hn = self.not_lt_of_ge(&vab, &lit0, s2)?; // ¬(va+vb < 0)
        // Transport to the intval forms and land the alt equation.
        let aplus_ab = ap2(&self.pr.plus, &xa, &xb)?;
        let ivplus = self
            .pr
            .intval_plus()?
            .all_elim(xa.clone())?
            .all_elim(xb.clone())?; // iv (aplus A B) = va+vb
        let iv0 = self.pr.intval_int()?.all_elim(lit0.clone())?; // iv '0 = 0
        let lt_eq = Thm::refl(int::int_lt())?
            .cong_app(ivplus.sym()?)?
            .cong_app(iv0.sym()?)?; // (va+vb < 0) = (iv (aplus A B) < iv '0)
        let hn = self.not_transport(hn, lt_eq)?;
        self.alt_nil_of_not_lt(&aplus_ab, &a0, hn)?
            .imp_intro(&ng_b)?
            .imp_intro(&ng_a)?
            .all_intro("B", a.clone())?
            .all_intro("A", a)
    }

    /// `⊢ ∀A B. ¬(aequal (alt A '0) anil = anil) ⟹
    /// ¬(alt B (aplus '1 (aplus A B)) = anil)` — `0 ≤ a ⟹ b < 1+(a+b)`.
    fn lt_plus_one_thm(&self) -> Result<Thm> {
        let a = self.a();
        let anil = self.anil();
        let a0 = self.a0()?;
        let a1 = self.a1()?;
        let (lit0, lit1) = (mk_int(0i64), mk_int(1i64));
        let (xa, xb) = (self.avar("A"), self.avar("B"));
        let ng_a = ap2(&self.pr.equal, &ap2(&self.pr.lt, &xa, &a0)?, &anil)?
            .equals(anil.clone())?
            .not()?;
        let ha = self.nonneg_of_hne(&xa, &Thm::assume(ng_a.clone())?)?; // 0 ≤ va
        let (va, vb) = (self.iv(&xa)?, self.iv(&xb)?);
        let add = |u: &Term, v: &Term| -> Result<Term> {
            int::int_add().apply(u.clone())?.apply(v.clone())
        };
        let vab = add(&va, &vb)?;
        // vb ≤ va+vb.
        let s1 = self
            .le_add_mono_at(&lit0, &va, &vb, ha)?
            .rewrite(&self.zero_add_at(&vb)?)?;
        // va+vb < 1+(va+vb): cancel k := va+vb against ⊢ 0 < 1.
        let zero_lt_one = int::int_lt()
            .apply(lit0.clone())?
            .apply(lit1.clone())?
            .reduce()?
            .eqt_elim()?; // ⊢ 0 < 1
        let s2 = int::lt_add_cancel_left_at(&vab, &lit0, &lit1)? // (k+0 < k+1) = (0 < 1)
            .sym()?
            .eq_mp(zero_lt_one)? // k+0 < k+1
            .rewrite(&int::add_zero().all_elim(vab.clone())?)? // k < k+1
            .rewrite(
                &int::add_comm()
                    .all_elim(vab.clone())?
                    .all_elim(lit1.clone())?,
            )?; // k < 1+k
        let one_ab = add(&lit1, &vab)?;
        let hlt = int::lt_of_le_of_lt()
            .all_elim(vb.clone())?
            .all_elim(vab.clone())?
            .all_elim(one_ab)?
            .imp_elim(s1)?
            .imp_elim(s2)?; // vb < 1+(va+vb)
        // Transport 1+(va+vb) back to iv (aplus '1 (aplus A B)).
        let aplus_ab = ap2(&self.pr.plus, &xa, &xb)?;
        let big = ap2(&self.pr.plus, &a1, &aplus_ab)?;
        let iv_big = self
            .pr
            .intval_plus()?
            .all_elim(a1.clone())?
            .all_elim(aplus_ab.clone())? // iv big = intAdd (iv '1) (iv (aplus A B))
            .rewrite(&self.pr.intval_int()?.all_elim(lit1.clone())?)?
            .rewrite(
                &self
                    .pr
                    .intval_plus()?
                    .all_elim(xa.clone())?
                    .all_elim(xb.clone())?,
            )?; // iv big = 1+(va+vb)
        let lt_eq = Thm::refl(int::int_lt())?
            .cong_app(Thm::refl(vb.clone())?)?
            .cong_app(iv_big.sym()?)?; // (vb < 1+(va+vb)) = (iv B < iv big)
        let hlt = lt_eq.eq_mp(hlt)?;
        let holds = self.pr.alt_iff_at(&xb, &big)?.sym()?.eq_mp(hlt)?; // ¬(alt B big = anil)
        holds
            .imp_intro(&ng_a)?
            .all_intro("B", a.clone())?
            .all_intro("A", a)
    }

    /// `⊢ ∀A. ¬(alt A '0 = anil) ⟹ (alt (aneg A) '0 = anil)` — the
    /// negation of a negative is nonnegative.
    fn neg_nonneg_thm(&self) -> Result<Thm> {
        let a = self.a();
        let anil = self.anil();
        let a0 = self.a0()?;
        let lit0 = mk_int(0i64);
        let xa = self.avar("A");
        let ng_t = ap2(&self.pr.lt, &xa, &a0)?.equals(anil.clone())?.not()?;
        let iv0 = self.pr.intval_int()?.all_elim(lit0.clone())?;
        let hlt = self
            .pr
            .alt_iff_at(&xa, &a0)?
            .eq_mp(Thm::assume(ng_t.clone())?)?
            .rewrite(&iv0)?; // va < 0
        let va = self.iv(&xa)?;
        let nva = int::int_neg().apply(va.clone())?;
        // 0 < -va: shift by -va and simplify.
        let s1 = int::lt_add_mono()
            .all_elim(va.clone())?
            .all_elim(lit0.clone())?
            .all_elim(nva.clone())?
            .imp_elim(hlt)? // va+(-va) < 0+(-va)
            .rewrite(&int::add_neg().all_elim(va.clone())?)? // 0 < 0+(-va)
            .rewrite(&self.zero_add_at(&nva)?)?; // 0 < -va
        let s2 = int::lt_imp_le()
            .all_elim(lit0.clone())?
            .all_elim(nva.clone())?
            .imp_elim(s1)?; // 0 ≤ -va
        let hn = self.not_lt_of_ge(&nva, &lit0, s2)?; // ¬(-va < 0)
        let aneg_a = ap1(&self.pr.neg, &xa)?;
        let iv_neg = self.pr.intval_neg()?.all_elim(xa.clone())?; // iv (aneg A) = -va
        let lt_eq = Thm::refl(int::int_lt())?
            .cong_app(iv_neg.sym()?)?
            .cong_app(iv0.sym()?)?; // (-va < 0) = (iv (aneg A) < iv '0)
        let hn = self.not_transport(hn, lt_eq)?;
        self.alt_nil_of_not_lt(&aneg_a, &a0, hn)?
            .imp_intro(&ng_t)?
            .all_intro("A", a)
    }

    // ------------------------------------------------------------------
    // S5c — the seven ordinal UserRows + the axiom pack (design §3, §8)
    // ------------------------------------------------------------------

    /// The seven ordinal [`UserRow`]s (NATP, POSP, O-FIRST-EXPT,
    /// O-FIRST-COEFF, O-RST, O<, O-P): bodies are the §1.2 normalized
    /// ACL2 sources, models are this theory's constants (minted once,
    /// env-independent), `def_eq_model`s are the **proved** defining
    /// equations ([`Ordinals::olt_def`]/[`Ordinals::op_def`] for the
    /// recursive pair; `apply_def` for the plain constants) —
    /// [`install_user_rows`] re-pins each against `model_image` output.
    fn user_rows(&self, tm: &Terms) -> Result<Vec<UserRow>> {
        let a = self.a();
        let x = tm.sym(b"X")?;
        let y = tm.sym(b"Y")?;
        let q0 = tm.quote(&self.a0()?)?;
        let qt = tm.quote(&self.pr.t)?;
        let qnil = tm.quote(&self.anil())?;
        let app1 = |f: &[u8], v: &Term| tm.app(f, std::slice::from_ref(v));
        let ofe_e = |v: &Term| app1(b"O-FIRST-EXPT", v);
        let ofc_e = |v: &Term| app1(b"O-FIRST-COEFF", v);
        let ors_e = |v: &Term| app1(b"O-RST", v);

        // The §1.2 normalized bodies.
        let natp_body = tm.mk_if(
            &app1(b"INTEGERP", &x)?,
            &tm.mk_if(&tm.app(b"<", &[x.clone(), q0.clone()])?, &qnil, &qt)?,
            &qnil,
        )?;
        let posp_body = tm.mk_if(
            &app1(b"INTEGERP", &x)?,
            &tm.app(b"<", &[q0.clone(), x.clone()])?,
            &qnil,
        )?;
        let ofe_body = tm.mk_if(
            &app1(b"CONSP", &x)?,
            &app1(b"CAR", &app1(b"CAR", &x)?)?,
            &q0,
        )?;
        let ofc_body = tm.mk_if(&app1(b"CONSP", &x)?, &app1(b"CDR", &app1(b"CAR", &x)?)?, &x)?;
        let ors_body = app1(b"CDR", &x)?;
        let olt_body = {
            let coeff = tm.mk_if(
                &tm.app(b"EQUAL", &[ofc_e(&x)?, ofc_e(&y)?])?,
                &tm.app(b"O<", &[ors_e(&x)?, ors_e(&y)?])?,
                &tm.app(b"<", &[ofc_e(&x)?, ofc_e(&y)?])?,
            )?;
            let expt = tm.mk_if(
                &tm.app(b"EQUAL", &[ofe_e(&x)?, ofe_e(&y)?])?,
                &coeff,
                &tm.app(b"O<", &[ofe_e(&x)?, ofe_e(&y)?])?,
            )?;
            let cons_arm = tm.mk_if(&app1(b"CONSP", &y)?, &expt, &qnil)?;
            let fin_arm = tm.mk_if(
                &app1(b"CONSP", &y)?,
                &qt,
                &tm.app(b"<", &[x.clone(), y.clone()])?,
            )?;
            tm.mk_if(&app1(b"CONSP", &x)?, &cons_arm, &fin_arm)?
        };
        let op_body = {
            let rec_ok = tm.mk_if(
                &app1(b"O-P", &ors_e(&x)?)?,
                &tm.app(b"O<", &[ofe_e(&ors_e(&x)?)?, ofe_e(&x)?])?,
                &qnil,
            )?;
            let posp_ck = tm.mk_if(&app1(b"POSP", &ofc_e(&x)?)?, &rec_ok, &qnil)?;
            let zero_ck = tm.mk_if(
                &tm.app(b"EQUAL", &[ofe_e(&x)?, q0.clone()])?,
                &qnil,
                &posp_ck,
            )?;
            let expt_ok = tm.mk_if(&app1(b"O-P", &ofe_e(&x)?)?, &zero_ck, &qnil)?;
            let car_ck = tm.mk_if(&app1(b"CONSP", &app1(b"CAR", &x)?)?, &expt_ok, &qnil)?;
            tm.mk_if(&app1(b"CONSP", &x)?, &car_ck, &app1(b"NATP", &x)?)?
        };

        // The plain-constant defining equations (`apply_def` recipe).
        let simple_def = |eq: &Thm| -> Result<Thm> {
            apply_def(eq, &[Term::free("X", a.clone())])?.all_intro("X", a.clone())
        };
        let row = |name: &str,
                   formals: &[&str],
                   body: Term,
                   model: &Term,
                   def_eq_model: Thm,
                   def_eq: &Thm|
         -> Result<UserRow> {
            let formals: Vec<SmolStr> = formals.iter().map(|f| SmolStr::new(f)).collect();
            let formal_syms: Vec<Term> = formals
                .iter()
                .map(|f| tm.sym(f.as_bytes()))
                .collect::<Result<_>>()?;
            let def_enc = tm.mk_equal(&tm.app(name.as_bytes(), &formal_syms)?, &body)?;
            Ok(UserRow {
                name: SmolStr::new(name),
                formals,
                body,
                rec_formal: None,
                model: model.clone(),
                def_enc,
                def_eq_model,
                def_eq: def_eq.clone(),
            })
        };
        Ok(vec![
            row(
                "NATP",
                &["X"],
                natp_body,
                &self.natp,
                simple_def(&self.natp_eq)?,
                &self.natp_eq,
            )?,
            row(
                "POSP",
                &["X"],
                posp_body,
                &self.posp,
                simple_def(&self.posp_eq)?,
                &self.posp_eq,
            )?,
            row(
                "O-FIRST-EXPT",
                &["X"],
                ofe_body,
                &self.ofe,
                simple_def(&self.ofe_eq)?,
                &self.ofe_eq,
            )?,
            row(
                "O-FIRST-COEFF",
                &["X"],
                ofc_body,
                &self.ofc,
                simple_def(&self.ofc_eq)?,
                &self.ofc_eq,
            )?,
            row(
                "O-RST",
                &["X"],
                ors_body,
                &self.ors,
                simple_def(&self.ors_eq)?,
                &self.ors_eq,
            )?,
            row(
                "O<",
                &["X", "Y"],
                olt_body,
                &self.olt,
                self.olt_def()?,
                &self.olt_eq,
            )?,
            row(
                "O-P",
                &["X"],
                op_body,
                &self.op,
                self.op_def()?,
                &self.op_eq,
            )?,
        ])
    }

    /// The S5 axiom pack (design §8): the classical `cases` split, the
    /// `equal-mp`/`contra`/`truth` propositional glue (all `Schema`
    /// arms), and the typed-arithmetic `ModelEq`/`ModelHolds`/
    /// `ModelImplies` rows. Every model discharge theorem is checked
    /// here against its `model_*_target` statement (fail-safe: drift
    /// errors before the row is ever installed).
    fn axiom_pack(&self, env: &Acl2Env) -> Result<Vec<AxiomRow>> {
        let tm = &*env.tm;
        let x = tm.sym(b"X")?;
        let y = tm.sym(b"Y")?;
        let va = tm.sym(b"A")?;
        let vb = tm.sym(b"B")?;
        let q0 = tm.quote(&self.a0()?)?;
        let q1 = tm.quote(&self.a1()?)?;
        let qnil = tm.quote(&self.anil())?;
        let schema = |name: &str, enc: Term| AxiomRow {
            name: SmolStr::new(name),
            enc,
            discharge: Discharge::Schema,
        };
        let checked = |name: &str, enc: Term, discharge: Discharge| -> Result<AxiomRow> {
            let (target, thm) = match &discharge {
                Discharge::ModelEq(t) => (model_eq_target(env, &enc)?, t),
                Discharge::ModelHolds(t) => (model_holds_target(env, &enc)?, t),
                Discharge::ModelImplies(t) => (model_implies_target(env, &enc)?, t),
                _ => {
                    return Err(Error::ConnectiveRule(
                        "acl2 axiom_pack: checked rows are model-discharged".into(),
                    ));
                }
            };
            if !thm.hyps().is_empty() || *thm.concl() != target {
                return Err(Error::ConnectiveRule(format!(
                    "acl2 axiom_pack: `{name}` model theorem does not state its target"
                )));
            }
            Ok(AxiomRow {
                name: SmolStr::new(name),
                enc,
                discharge,
            })
        };
        let plus_ab = tm.app(b"BINARY-+", &[va.clone(), vb.clone()])?;
        let neg_a = tm.app(b"UNARY--", &[va.clone()])?;
        let lt0 = |v: &Term| tm.app(b"<", &[v.clone(), q0.clone()]);
        Ok(vec![
            // cases: (IMPLIES (IMPLIES X Y) (IMPLIES (IMPLIES (EQUAL X 'NIL) Y) Y))
            // — the classical object case split (fills the "no classical
            // axiom" gap; ACL2's logic is classical).
            schema(
                "cases",
                tm.mk_implies(
                    &tm.mk_implies(&x, &y)?,
                    &tm.mk_implies(&tm.mk_implies(&tm.mk_equal(&x, &qnil)?, &y)?, &y)?,
                )?,
            ),
            // equal-mp: (IMPLIES (EQUAL X Y) (IMPLIES X Y)).
            schema(
                "equal-mp",
                tm.mk_implies(&tm.mk_equal(&x, &y)?, &tm.mk_implies(&x, &y)?)?,
            ),
            // contra: (IMPLIES X (IMPLIES (EQUAL X 'NIL) Y)).
            schema(
                "contra",
                tm.mk_implies(&x, &tm.mk_implies(&tm.mk_equal(&x, &qnil)?, &y)?)?,
            ),
            // truth: 'T.
            schema("truth", tm.quote(&self.pr.t)?),
            checked(
                "consp-plus",
                tm.mk_equal(&tm.app(b"CONSP", &[plus_ab.clone()])?, &qnil)?,
                Discharge::ModelEq(self.consp_plus_thm()?),
            )?,
            checked(
                "consp-neg",
                tm.mk_equal(&tm.app(b"CONSP", &[neg_a.clone()])?, &qnil)?,
                Discharge::ModelEq(self.consp_neg_thm()?),
            )?,
            checked(
                "integerp-plus",
                tm.app(b"INTEGERP", &[plus_ab.clone()])?,
                Discharge::ModelHolds(self.intp_plus_thm()?),
            )?,
            checked(
                "integerp-neg",
                tm.app(b"INTEGERP", &[neg_a.clone()])?,
                Discharge::ModelHolds(self.intp_neg_thm()?),
            )?,
            checked(
                "integerp-not-consp",
                tm.mk_implies(
                    &tm.app(b"INTEGERP", &[x.clone()])?,
                    &tm.mk_equal(&tm.app(b"CONSP", &[x.clone()])?, &qnil)?,
                )?,
                Discharge::ModelImplies(self.intp_not_consp_thm()?),
            )?,
            checked(
                "plus-nonneg",
                tm.mk_implies(
                    &tm.mk_equal(&lt0(&va)?, &qnil)?,
                    &tm.mk_implies(
                        &tm.mk_equal(&lt0(&vb)?, &qnil)?,
                        &tm.mk_equal(&lt0(&plus_ab)?, &qnil)?,
                    )?,
                )?,
                Discharge::ModelImplies(self.plus_nonneg_thm()?),
            )?,
            checked(
                "lt-plus-one",
                tm.mk_implies(
                    &tm.mk_equal(&lt0(&va)?, &qnil)?,
                    &tm.app(
                        b"<",
                        &[
                            vb.clone(),
                            tm.app(b"BINARY-+", &[q1.clone(), plus_ab.clone()])?,
                        ],
                    )?,
                )?,
                Discharge::ModelImplies(self.lt_plus_one_thm()?),
            )?,
            checked(
                "neg-nonneg",
                tm.mk_implies(&lt0(&va)?, &tm.mk_equal(&lt0(&neg_a)?, &qnil)?)?,
                Discharge::ModelImplies(self.neg_nonneg_thm()?),
            )?,
        ])
    }
}

/// **S5c/S5d — the ordinal environment** (design §3/§7): extend an S6
/// env by the seven ordinal [`UserRow`]s (through the
/// [`install_user_rows`] hand-row seam — deliberately the S7 admission
/// path), the S5 axiom pack, and the single-IH **IND-ORD** clause
/// (`ind_ord = vec![1]` — measured induction along `o<`, soundness by
/// [`Ordinals::wf_induct`]; S7 registers further shapes on demand).
pub fn with_ordinals(env: &Acl2Env) -> Result<Acl2Env> {
    if !env.s6 {
        return Err(Error::ConnectiveRule(
            "acl2 with_ordinals: requires an S6 env (the ordinal stage builds on IND/CongImpl)"
                .into(),
        ));
    }
    let o = ordinals()?;
    let rows = o.user_rows(&env.tm)?;
    let mut env2 = install_user_rows(env, rows)?;
    let pack = o.axiom_pack(&env2)?;
    env2.axioms.extend(pack);
    env2.ind_ord = vec![1];
    Ok(env2)
}

// ============================================================================
// Strong induction on the nonnegative ints (design §4's driver)
// ============================================================================

/// `natToInt n : int`.
fn n2i(n: &Term) -> Term {
    Term::app(covalence_hol_eval::defs::nat_to_int(), n.clone())
}

/// `⊢ ∀<ivar>:int. intLe ⌜0⌝ <ivar> ⟹ body` by strong induction on the
/// nonnegative ints, transported from `nat` strong induction through the
/// `natToInt` bridge ([`crate::init::int::int_nonneg_nat`] /
/// [`crate::init::int::nat_to_int_nonneg`] / the order coherence).
///
/// `motive = λ<ivar>:int. body`. `prove_case(iv, hnn, ih)` must prove
/// `⊢ body[iv]` given the (opaque) case value `iv : int`,
/// `hnn : ⊢ ⌜0⌝ ≤ iv`, and
/// `ih : {…} ⊢ ∀j:int. ⌜0⌝ ≤ j ⟹ intLt j iv ⟹ (motive j)` (the motive
/// instances in applied form — `beta_reduce` after instantiating).
pub(crate) fn nonneg_si_on(
    ivar: &str,
    motive: &Term,
    prove_case: impl FnOnce(&Term, &Thm, &Thm) -> Result<Thm>,
) -> Result<Thm> {
    let it = Type::int();
    let nt = Type::nat();
    let lit0 = mk_int(0i64);
    let le0 = |v: &Term| -> Result<Term> { int::int_le().apply(lit0.clone())?.apply(v.clone()) };
    let bad = || Error::ConnectiveRule("acl2 ord nonneg_si_on: bad ∃".into());

    // nat motive: λn. motive (natToInt n).
    let nmotive = {
        let nv = Term::free("__sn", nt.clone());
        let body = Term::app(motive.clone(), n2i(&nv));
        Term::abs(nt.clone(), subst::close(&body, "__sn"))
    };
    let all_nat = crate::init::cv_recursion::strong_induct_on("__sn", &nmotive, |nv, ihn| {
        let iv = n2i(nv);
        let hnn = int::nat_to_int_nonneg().all_elim(nv.clone())?; // 0 ≤ natToInt nv
        // ih over ints: ∀j. 0 ≤ j ⟹ j < iv ⟹ (motive j).
        let ih = {
            let j = Term::free("__sj", it.clone());
            let h0 = le0(&j)?;
            let hlt = int::int_lt().apply(j.clone())?.apply(iv.clone())?;
            let ex = int::int_nonneg_nat()
                .all_elim(j.clone())?
                .imp_elim(Thm::assume(h0.clone())?)?; // ∃m. j = natToInt m
            let goal_j = Term::app(motive.clone(), j.clone());
            let step = {
                let m = Term::free("__sm", nt.clone());
                let pred = ex.concl().as_app().ok_or_else(bad)?.1.clone();
                let hm_redex = Term::app(pred, m.clone());
                let hm = beta_reduce(Thm::assume(hm_redex.clone())?)?; // j = natToInt m
                // natLt m nv from j < iv.
                let ltn = Thm::assume(hlt.clone())?.rewrite(&hm)?; // natToInt m < natToInt nv
                let nlt = int::n2i_lt_iff()
                    .all_elim(m.clone())?
                    .all_elim(nv.clone())?
                    .eq_mp(ltn)?; // natLt m nv
                let pm = beta_reduce(ihn.clone().all_elim(m.clone())?.imp_elim(nlt)?)?; // (motive (natToInt m))
                let pj = pm.rewrite(&hm.sym()?)?; // (motive j)
                pj.imp_intro(&hm_redex)?.all_intro("__sm", nt.clone())?
            };
            exists_elim(ex, goal_j, step)?
                .imp_intro(&hlt)?
                .imp_intro(&h0)?
                .all_intro("__sj", it.clone())?
        };
        let body = prove_case(&iv, &hnn, &ih)?;
        beta_expand(motive, iv.clone(), body)
    })?;
    // Transport: ∀i. 0 ≤ i ⟹ body[i]. `strong_induct_on` β-normalises
    // its conclusion, so `all_nat` states the *reduced* motive — the goal
    // here is the β-nf of `motive i` accordingly.
    let i = Term::free(ivar, it.clone());
    let hyp = le0(&i)?;
    let ex = int::int_nonneg_nat()
        .all_elim(i.clone())?
        .imp_elim(Thm::assume(hyp.clone())?)?; // ∃n. i = natToInt n
    let goal_i = crate::init::eq::beta_nf(Term::app(motive.clone(), i.clone()))
        .concl()
        .as_eq()
        .ok_or(Error::NotAnEquation)?
        .1
        .clone();
    let step = {
        let w = Term::free("__sw", nt.clone());
        let pred = ex.concl().as_app().ok_or_else(bad)?.1.clone();
        let hw_redex = Term::app(pred, w.clone());
        let hw = beta_reduce(Thm::assume(hw_redex.clone())?)?; // i = natToInt w
        let p = all_nat.all_elim(w.clone())?; // body[natToInt w] (reduced)
        let pi = p.rewrite(&hw.sym()?)?; // body[i]
        pi.imp_intro(&hw_redex)?.all_intro("__sw", nt.clone())?
    };
    exists_elim(ex, goal_i, step)? // {0 ≤ i} ⊢ body[i]
        .imp_intro(&hyp)?
        .all_intro(ivar, it)
}

/// A constructor-literal value shape.
enum VShape {
    Int(Term),
    Sym(Term),
    Nil,
    Cons(Term, Term),
}

/// Split an application spine `f a₁ … aₙ` into `(f, [a₁…aₙ])`.
fn spine(t: &Term) -> (&Term, Vec<Term>) {
    let mut cur = t;
    let mut args = Vec::new();
    while let Some((f, a)) = cur.as_app() {
        args.push(a.clone());
        cur = f;
    }
    args.reverse();
    (cur, args)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn o() -> &'static Ordinals {
        ordinals().unwrap()
    }

    fn a() -> Type {
        o().th.ty.clone()
    }

    fn avar(n: &str) -> Term {
        Term::free(n, a())
    }

    fn aint(i: i64) -> Term {
        o().th.aint_at(&mk_int(i)).unwrap()
    }

    fn acons(h: &Term, t: &Term) -> Term {
        o().acons_t(h, t).unwrap()
    }

    fn app1(f: &Term, x: &Term) -> Term {
        ap1(f, x).unwrap()
    }

    fn app2(f: &Term, x: &Term, y: &Term) -> Term {
        ap2(f, x, y).unwrap()
    }

    /// Assert a closed theorem with an exact conclusion.
    fn check(thm: &Thm, expected: &Term) {
        assert!(thm.hyps().is_empty(), "must be closed: {thm}");
        assert_eq!(thm.concl(), expected);
    }

    /// `aif c y z` as a term.
    fn aif3(c: &Term, y: &Term, z: &Term) -> Term {
        o().pr
            .aif
            .clone()
            .apply(c.clone())
            .unwrap()
            .apply(y.clone())
            .unwrap()
            .apply(z.clone())
            .unwrap()
    }

    /// **G1 №1 — the model layer builds; per-constructor laws exact.**
    #[test]
    fn t_ord_defs_build() {
        let d = o();
        let aa = Type::fun(a(), a());
        let aaa = Type::fun(a(), aa.clone());
        for c in [&d.natp, &d.posp, &d.ofe, &d.ofc, &d.ors, &d.op] {
            assert_eq!(c.type_of().unwrap(), aa);
        }
        assert_eq!(d.olt.type_of().unwrap(), aaa);
        assert_eq!(d.ht.type_of().unwrap(), Type::fun(a(), Type::nat()));
        assert_eq!(
            d.below.type_of().unwrap(),
            Type::fun(a(), Type::fun(a(), Type::bool()))
        );
        assert_eq!(d.acc.type_of().unwrap(), Type::fun(a(), Type::bool()));

        let (h, t, y) = (avar("h"), avar("t"), avar("y"));
        let nil = d.th.nil.clone();
        let a0 = d.a0().unwrap();
        let car = |v: &Term| app1(&d.th.car, v);
        let cdr = |v: &Term| app1(&d.th.cdr, v);
        let ht_ = acons(&h, &t);

        // ofe/ofc/ors at cons.
        check(
            &d.ofe_cons_at(&h, &t).unwrap(),
            &app1(&d.ofe, &ht_).equals(car(&h)).unwrap(),
        );
        check(
            &d.ofc_cons_at(&h, &t).unwrap(),
            &app1(&d.ofc, &ht_).equals(cdr(&h)).unwrap(),
        );
        check(
            &d.ors_cons_at(&h, &t).unwrap(),
            &app1(&d.ors, &ht_).equals(t.clone()).unwrap(),
        );

        // olt per-constructor laws (atom via the aint route, nil, cons).
        let i = Term::free("i", Type::int());
        let ai = d.th.aint_at(&i).unwrap();
        check(
            &d.olt_int_at(&i, &y).unwrap(),
            &app2(&d.olt, &ai, &y)
                .equals(aif3(
                    &app1(&d.pr.consp, &y),
                    &d.pr.t,
                    &app2(&d.pr.lt, &ai, &y),
                ))
                .unwrap(),
        );
        check(
            &d.olt_nil_at(&y).unwrap(),
            &app2(&d.olt, &nil, &y)
                .equals(aif3(
                    &app1(&d.pr.consp, &y),
                    &d.pr.t,
                    &app2(&d.pr.lt, &nil, &y),
                ))
                .unwrap(),
        );
        let caar_y = car(&car(&y));
        let cdar_y = cdr(&car(&y));
        let expected_cons = aif3(
            &app1(&d.pr.consp, &y),
            &aif3(
                &app2(&d.pr.equal, &car(&h), &caar_y),
                &aif3(
                    &app2(&d.pr.equal, &cdr(&h), &cdar_y),
                    &app2(&d.olt, &t, &cdr(&y)),
                    &app2(&d.pr.lt, &cdr(&h), &cdar_y),
                ),
                &app2(&d.olt, &car(&h), &caar_y),
            ),
            &nil,
        );
        check(
            &d.olt_cons_at(&h, &t, &y).unwrap(),
            &app2(&d.olt, &ht_, &y).equals(expected_cons).unwrap(),
        );

        // op per-constructor laws.
        check(
            &d.op_int_at(&i).unwrap(),
            &app1(&d.op, &ai).equals(app1(&d.natp, &ai)).unwrap(),
        );
        check(
            &d.op_nil_at().unwrap(),
            &app1(&d.op, &nil).equals(app1(&d.natp, &nil)).unwrap(),
        );
        let expected_op_cons = aif3(
            &app1(&d.pr.consp, &h),
            &aif3(
                &app1(&d.op, &car(&h)),
                &aif3(
                    &app2(&d.pr.equal, &car(&h), &a0),
                    &nil,
                    &aif3(
                        &app1(&d.posp, &cdr(&h)),
                        &aif3(
                            &app1(&d.op, &t),
                            &app2(&d.olt, &app1(&d.ofe, &t), &car(&h)),
                            &nil,
                        ),
                        &nil,
                    ),
                ),
                &nil,
            ),
            &nil,
        );
        check(
            &d.op_cons_at(&h, &t).unwrap(),
            &app1(&d.op, &ht_).equals(expected_op_cons).unwrap(),
        );

        // ht laws.
        check(
            &d.ht_nil_at().unwrap(),
            &app1(&d.ht, &nil).equals(crate::init::nat::zero()).unwrap(),
        );
        check(
            &d.ht_cons_at(&h, &t).unwrap(),
            &app1(&d.ht, &ht_)
                .equals(crate::init::nat::succ(app1(&d.ht, &car(&h))))
                .unwrap(),
        );
    }

    /// **G1 №3 — ground folding through `ord_fold`** (the designed
    /// instances: ω·2 is an ordinal, zero exponents / non-cons cars /
    /// garbage are not, 1 < ω < ω·2, ω² < ω^ω, and a reflexive `anil`
    /// control).
    #[test]
    fn t_ord_fold_ground() {
        let d = o();
        let nil = d.th.nil.clone();
        let t_ = d.pr.t.clone();
        // ⌜((1 . 2) . 0)⌝ = ω·2;  ⌜((1 . 1) . 0)⌝ = ω.
        let w2 = acons(&acons(&aint(1), &aint(2)), &aint(0));
        let w1 = acons(&acons(&aint(1), &aint(1)), &aint(0));
        // ((0 . 2) . 0) — zero first exponent (not an ordinal).
        let zexp = acons(&acons(&aint(0), &aint(2)), &aint(0));
        // (5) = acons 5 anil — car is not a cons.
        let five = acons(&aint(5), &nil);
        // ω² = ((2 . 1) . 0);  ω^ω = (((1 . 1) . 0) . 1) . 0).
        let wsq = acons(&acons(&aint(2), &aint(1)), &aint(0));
        let wpw = acons(&acons(&w1, &aint(1)), &aint(0));

        let fold_check = |t: &Term, expected: &Term| {
            let thm = d.ord_fold(t).unwrap();
            check(&thm, &t.clone().equals(expected.clone()).unwrap());
        };

        fold_check(&app1(&d.op, &w2), &t_);
        fold_check(&app1(&d.op, &zexp), &nil);
        fold_check(&app1(&d.op, &five), &nil);
        fold_check(&app1(&d.op, &aint(3)), &t_);
        fold_check(&app1(&d.op, &wpw), &t_);
        fold_check(&app2(&d.olt, &aint(1), &w1), &t_);
        fold_check(&app2(&d.olt, &w1, &w2), &t_);
        fold_check(&app2(&d.olt, &wsq, &wpw), &t_);
        // Reflexive negative control: ¬(ω < ω).
        fold_check(&app2(&d.olt, &w1, &w1), &nil);
    }

    /// **G2 №5 — the three Acc rules, closed + exact** (design §5.1).
    #[test]
    fn t_acc_rules() {
        let d = o();
        let sb = Type::fun(a(), Type::bool());
        let (x, y, z, s) = (avar("x"), avar("y"), avar("z"), Term::free("S", sb.clone()));
        let below2 = |u: &Term, v: &Term| app2(&d.below, u, v);
        let acc1 = |u: &Term| app1(&d.acc, u);
        let sap = |u: &Term| Term::app(s.clone(), u.clone());

        // acc_intro: ∀x. (∀y. below y x ⟹ acc y) ⟹ acc x.
        let intro = d.acc_intro().unwrap();
        let expected = below2(&y, &x)
            .imp(acc1(&y))
            .unwrap()
            .forall("y", a())
            .unwrap()
            .imp(acc1(&x))
            .unwrap()
            .forall("x", a())
            .unwrap();
        check(&intro, &expected);

        // acc_elim: ∀S. (∀z. (∀y. below y z ⟹ S y) ⟹ S z) ⟹
        //           ∀x. acc x ⟹ S x.
        let elim = d.acc_elim().unwrap();
        let step = below2(&y, &z)
            .imp(sap(&y))
            .unwrap()
            .forall("y", a())
            .unwrap()
            .imp(sap(&z))
            .unwrap()
            .forall("z", a())
            .unwrap();
        let expected = step
            .imp(acc1(&x).imp(sap(&x)).unwrap().forall("x", a()).unwrap())
            .unwrap()
            .forall("S", sb.clone())
            .unwrap();
        check(&elim, &expected);

        // acc_inv: ∀x. acc x ⟹ ∀y. below y x ⟹ acc y.
        let inv = d.acc_inv().unwrap();
        let expected = acc1(&x)
            .imp(
                below2(&y, &x)
                    .imp(acc1(&y))
                    .unwrap()
                    .forall("y", a())
                    .unwrap(),
            )
            .unwrap()
            .forall("x", a())
            .unwrap();
        check(&inv, &expected);
    }

    /// **G2 №6 (driver smoke) + №7 — L0, the "below ω" milestone:**
    /// `⊢ ∀i:int. 0 ≤ i ⟹ acc (aint i)`, closed + exact; the
    /// `nonneg_si_on` driver is exercised by the proof itself plus a
    /// trivial smoke instance.
    #[test]
    fn t_l0_finite_wf() {
        let d = o();
        let lit0 = mk_int(0i64);

        // Driver smoke: ⊢ ∀i. 0 ≤ i ⟹ (aint i = aint i).
        let smoke = {
            let motive = {
                let iv = Term::free("__si", Type::int());
                let body =
                    d.th.aint_at(&iv)
                        .unwrap()
                        .equals(d.th.aint_at(&iv).unwrap())
                        .unwrap();
                Term::abs(Type::int(), subst::close(&body, "__si"))
            };
            nonneg_si_on("i", &motive, |iv, _hnn, _ih| {
                Thm::refl(d.th.aint_at(iv).unwrap())
            })
            .unwrap()
        };
        assert!(smoke.hyps().is_empty());
        let i = Term::free("i", Type::int());
        let le0i = int::int_le()
            .apply(lit0.clone())
            .unwrap()
            .apply(i.clone())
            .unwrap();
        let ai = d.th.aint_at(&i).unwrap();
        let expected = le0i
            .clone()
            .imp(ai.clone().equals(ai.clone()).unwrap())
            .unwrap()
            .forall("i", Type::int())
            .unwrap();
        assert_eq!(smoke.concl(), &expected);

        // THE L0 theorem: ⊢ ∀i. 0 ≤ i ⟹ acc (aint i).
        let l0 = d.l0_finite_wf().unwrap();
        assert!(l0.hyps().is_empty(), "L0 must be closed");
        let expected = le0i
            .imp(app1(&d.acc, &ai))
            .unwrap()
            .forall("i", Type::int())
            .unwrap();
        assert_eq!(l0.concl(), &expected);

        // Inversion-kit statements (natp_inv / olt_fin_inv), closed.
        assert!(d.natp_inv().unwrap().hyps().is_empty());
        assert!(d.olt_fin_inv().unwrap().hyps().is_empty());
    }

    /// op_fe smoke (kit): closed + exact statement.
    #[test]
    fn t_op_fe_smoke() {
        let d = o();
        let x = avar("x");
        let thm = d.op_fe().unwrap();
        assert!(thm.hyps().is_empty());
        let expected = app1(&d.op, &x)
            .equals(d.th.nil.clone())
            .unwrap()
            .not()
            .unwrap()
            .imp(
                app1(&d.op, &app1(&d.ofe, &x))
                    .equals(d.th.nil.clone())
                    .unwrap()
                    .not()
                    .unwrap(),
            )
            .unwrap()
            .forall("x", a())
            .unwrap();
        assert_eq!(thm.concl(), &expected);
    }

    /// **G2 №8 — THE S5 THEOREM: full-ε₀ well-foundedness.**
    /// `main_ord`, `graded_wf`, `wf`, `wf_induct` — all closed, exact
    /// statements.
    #[test]
    fn t_wf_epsilon0() {
        let d = o();
        let nil = d.th.nil.clone();
        let (x, y, z, e, k) = (
            avar("x"),
            avar("y"),
            avar("z"),
            avar("e"),
            Term::free("k", Type::nat()),
        );
        let sb = Type::fun(a(), Type::bool());
        let s = Term::free("S", sb.clone());
        let ne_nil = |t: &Term| t.clone().equals(nil.clone()).unwrap().not().unwrap();
        let op_at = |v: &Term| ne_nil(&app1(&d.op, v));

        // wf: ∀x. ¬(op x = anil) ⟹ acc x — THE theorem.
        let wf = d.wf().unwrap();
        assert!(wf.hyps().is_empty(), "wf must be closed");
        let expected_wf = op_at(&x)
            .imp(app1(&d.acc, &x))
            .unwrap()
            .forall("x", a())
            .unwrap();
        assert_eq!(wf.concl(), &expected_wf);

        // main_ord: ∀e. acc e ⟹ ∀x. op x ⟹ ((ofe x = e) ∨ ¬(olt (ofe x) e
        // = anil)) ⟹ acc x.
        let main = d.main_ord().unwrap();
        assert!(main.hyps().is_empty(), "main_ord must be closed");
        let fex = app1(&d.ofe, &x);
        let disj = fex
            .clone()
            .equals(e.clone())
            .unwrap()
            .or(ne_nil(&app2(&d.olt, &fex, &e)))
            .unwrap();
        let expected_main = app1(&d.acc, &e)
            .imp(
                op_at(&x)
                    .imp(disj.imp(app1(&d.acc, &x)).unwrap())
                    .unwrap()
                    .forall("x", a())
                    .unwrap(),
            )
            .unwrap()
            .forall("e", a())
            .unwrap();
        assert_eq!(main.concl(), &expected_main);

        // graded_wf: ∀k x. op x ⟹ ht x ≤ k ⟹ acc x.
        let graded = d.graded_wf().unwrap();
        assert!(graded.hyps().is_empty(), "graded_wf must be closed");
        let le_ht = Term::app(
            Term::app(crate::init::nat::nat_le(), app1(&d.ht, &x)),
            k.clone(),
        );
        let expected_graded = op_at(&x)
            .imp(le_ht.imp(app1(&d.acc, &x)).unwrap())
            .unwrap()
            .forall("x", a())
            .unwrap()
            .forall("k", Type::nat())
            .unwrap();
        assert_eq!(graded.concl(), &expected_graded);

        // wf_induct: ∀S. (∀z. (∀y. below y z ⟹ S y) ⟹ S z) ⟹
        //            ∀x. op x ⟹ S x.
        let wfi = d.wf_induct().unwrap();
        assert!(wfi.hyps().is_empty(), "wf_induct must be closed");
        let sap = |u: &Term| Term::app(s.clone(), u.clone());
        let step = app2(&d.below, &y, &z)
            .imp(sap(&y))
            .unwrap()
            .forall("y", a())
            .unwrap()
            .imp(sap(&z))
            .unwrap()
            .forall("z", a())
            .unwrap();
        let expected_wfi = step
            .imp(op_at(&x).imp(sap(&x)).unwrap().forall("x", a()).unwrap())
            .unwrap()
            .forall("S", sb)
            .unwrap();
        assert_eq!(wfi.concl(), &expected_wfi);

        // Ground composition: acc ⌜ω·2⌝ through wf + ord_fold.
        let w2 = acons(&acons(&aint(1), &aint(2)), &aint(0));
        let opw2 = d.ord_fold(&app1(&d.op, &w2)).unwrap(); // op ω·2 = t
        let ne = {
            let eqn = app1(&d.op, &w2).equals(nil.clone()).unwrap();
            let f =
                d.pr.t_ne_nil()
                    .unwrap()
                    .not_elim(
                        opw2.sym()
                            .unwrap()
                            .trans(Thm::assume(eqn.clone()).unwrap())
                            .unwrap(),
                    )
                    .unwrap();
            f.imp_intro(&eqn).unwrap().not_intro().unwrap()
        };
        let acc_w2 = wf.all_elim(w2.clone()).unwrap().imp_elim(ne).unwrap();
        check(&acc_w2, &app1(&d.acc, &w2));
    }

    /// **G1 №2 — ACL2's two ordinal defining equations, closed + exact.**
    #[test]
    fn t_olt_op_def_eqs() {
        let d = o();
        let (x, y) = (avar("x"), avar("y"));

        let op_def = d.op_def().unwrap();
        assert!(op_def.hyps().is_empty(), "op_def must be closed");
        let expected = app1(&d.op, &x)
            .equals(d.op_rhs(&x).unwrap())
            .unwrap()
            .forall("x", a())
            .unwrap();
        assert_eq!(op_def.concl(), &expected);

        let olt_def = d.olt_def().unwrap();
        assert!(olt_def.hyps().is_empty(), "olt_def must be closed");
        let expected = app2(&d.olt, &x, &y)
            .equals(d.olt_rhs(&x, &y).unwrap())
            .unwrap()
            .forall("y", a())
            .unwrap()
            .forall("x", a())
            .unwrap();
        assert_eq!(olt_def.concl(), &expected);
    }

    // ------------------------------------------------------------------
    // G3 — env integration (S5c, design §11 №9–12)
    // ------------------------------------------------------------------

    use crate::init::acl2::defun::Acl2Session;
    use crate::init::acl2::derivable::{
        ClauseKind, acl2_rule_set, derivable, derive_axiom, derive_comp_folded, derive_def,
        derive_inst_ground, derive_mp, finite_sigma, ground_env, model_implies_target, s6_env,
        transport_equal, transport_equal_open, transport_implies_open,
    };

    /// The ordinal env (S6 + seven ordinal rows + the S5 axiom pack) with
    /// its per-generation soundness, shared across the G3 tests.
    fn ord_session() -> &'static Acl2Session {
        use std::sync::LazyLock;
        static ORD_ENV: LazyLock<std::result::Result<Acl2Session, String>> = LazyLock::new(|| {
            let e6 = s6_env().map_err(|e| e.to_string())?;
            let env = with_ordinals(&e6).map_err(|e| e.to_string())?;
            Ok(Acl2Session::new(env))
        });
        ORD_ENV.as_ref().unwrap()
    }

    /// **G3 №9 — layout:** `with_ordinals(s6_env)` has 22 axioms (10 s6 +
    /// 12 pack), 18 table rows, 7 user rows, 1 IND-ORD shape — 87
    /// clauses at the design indices; the ground/s6 layouts are
    /// unchanged; the S5 schema pack and the two ordinal `Def` clauses
    /// derive with exact statements.
    #[test]
    fn t_ord_env_layout() {
        // Regressions.
        let e0 = ground_env().unwrap();
        assert!(!e0.s6);
        assert!(e0.ind_ord.is_empty());
        assert_eq!(e0.n_clauses(), 29);
        let e6 = s6_env().unwrap();
        assert_eq!(e6.axioms.len(), 10);
        assert!(e6.ind_ord.is_empty());
        assert_eq!(e6.n_clauses(), 46);

        let env = ord_session().env();
        assert_eq!(env.axioms.len(), 22);
        assert_eq!(env.rows.len(), 18);
        assert_eq!(env.users.len(), 7);
        assert_eq!(env.ind_ord, vec![1]);
        assert_eq!(env.n_clauses(), 87);
        assert_eq!(env.clause_index(ClauseKind::Mp), 22);
        assert_eq!(env.clause_index(ClauseKind::Inst), 23);
        assert_eq!(env.clause_index(ClauseKind::Ind), 24);
        assert_eq!(env.clause_index(ClauseKind::Cong(0)), 25);
        assert_eq!(env.clause_index(ClauseKind::Comp(0)), 43);
        assert_eq!(env.clause_index(ClauseKind::CongImpl(0)), 61);
        assert_eq!(env.clause_index(ClauseKind::Def(0)), 79);
        assert_eq!(env.clause_index(ClauseKind::Def(6)), 85);
        assert_eq!(env.clause_index(ClauseKind::IndOrd(0)), 86);
        let rs = acl2_rule_set(env);
        assert_eq!(rs.n_clauses().unwrap(), 87);

        // The S5 schema axioms derive with their exact encodings.
        let tm = &*env.tm;
        let x = tm.sym(b"X").unwrap();
        let y = tm.sym(b"Y").unwrap();
        let qnil = tm.quote(&tm.th.nil).unwrap();
        let cases_enc = tm
            .mk_implies(
                &tm.mk_implies(&x, &y).unwrap(),
                &tm.mk_implies(
                    &tm.mk_implies(&tm.mk_equal(&x, &qnil).unwrap(), &y).unwrap(),
                    &y,
                )
                .unwrap(),
            )
            .unwrap();
        let equal_mp_enc = tm
            .mk_implies(
                &tm.mk_equal(&x, &y).unwrap(),
                &tm.mk_implies(&x, &y).unwrap(),
            )
            .unwrap();
        let contra_enc = tm
            .mk_implies(
                &x,
                &tm.mk_implies(&tm.mk_equal(&x, &qnil).unwrap(), &y).unwrap(),
            )
            .unwrap();
        let truth_enc = tm.quote(&o().pr.t).unwrap();
        for (name, enc) in [
            ("cases", cases_enc),
            ("equal-mp", equal_mp_enc),
            ("contra", contra_enc),
            ("truth", truth_enc),
        ] {
            let d = derive_axiom(env, name).unwrap();
            check(&d, &derivable(env, &enc).unwrap());
        }
    }

    /// **G3 №10 — soundness of the ordinal env:** closed, exact ∀A
    /// statement (exercises all seven hand-row `discharge_def`s, the
    /// four S5 schema arms, the `ModelEq`/`ModelHolds`/`ModelImplies`
    /// pack discharges, and — since S5d — the `wf_induct`-routed
    /// IND-ORD discharge).
    #[test]
    fn t_ord_soundness() {
        let sess = ord_session();
        let env = sess.env();
        let tm = &*env.tm;
        let s = sess.soundness().unwrap();

        let av = Term::free("A", a());
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
        let expected = derivable(env, &av)
            .unwrap()
            .imp(body)
            .unwrap()
            .forall("A", a())
            .unwrap();
        check(&s, &expected);
    }

    /// **G3 №11 — the ordinal Def clauses + a ground object derivation:**
    /// `derive_def` for `O-P`/`O<` (exact encodings);
    /// `⊢ Derivable ⌜(O-P '((1 . 2) . 0))⌝` via the user computation
    /// clause + `ord_fold` + the `equal-mp`/`truth` pack rows; and the
    /// transported ground control `⊢ olt ⌜1⌝ ⌜ω⌝ = t`.
    #[test]
    fn t_ord_defs_derive() {
        let d = o();
        let sess = ord_session();
        let env = sess.env();
        let tm = &*env.tm;

        // Def clauses, exact.
        for name in ["O-P", "O<"] {
            let (j, u) = env.user(name).unwrap();
            let der = derive_def(env, j).unwrap();
            check(&der, &derivable(env, &u.def_enc).unwrap());
        }

        // Ground: v = ⌜((1 . 2) . 0)⌝ = ω·2 is an ordinal, in-object.
        let v = acons(&acons(&aint(1), &aint(2)), &aint(0));
        let qv = tm.quote(&v).unwrap();
        let qt = tm.quote(&d.pr.t).unwrap();
        let opv = tm.app(b"O-P", &[qv.clone()]).unwrap();

        // 1. Computation clause, model image folded by `ord_fold`.
        let k = env.row("O-P").unwrap();
        let ground = d.ord_fold(&app1(&d.op, &v)).unwrap(); // ⊢ op v = t
        let d_comp = derive_comp_folded(env, k, std::slice::from_ref(&v), &ground).unwrap();
        let p = tm.mk_equal(&opv, &qt).unwrap();
        check(&d_comp, &derivable(env, &p).unwrap());

        // 2. equal-symm to flip, equal-mp + truth to detach.
        let q_rev = tm.mk_equal(&qt, &opv).unwrap();
        let (_, symm) = env.axiom("equal-symm").unwrap();
        let symm = symm.clone();
        let s = finite_sigma(tm, &[(b"X", opv.clone()), (b"Y", qt.clone())]).unwrap();
        let d_symm =
            derive_inst_ground(env, &symm, &s, derive_axiom(env, "equal-symm").unwrap()).unwrap();
        let d_rev = derive_mp(env, &p, &q_rev, d_symm, d_comp).unwrap();
        check(&d_rev, &derivable(env, &q_rev).unwrap());

        let (_, emp) = env.axiom("equal-mp").unwrap();
        let emp = emp.clone();
        let s = finite_sigma(tm, &[(b"X", qt.clone()), (b"Y", opv.clone())]).unwrap();
        let d_emp =
            derive_inst_ground(env, &emp, &s, derive_axiom(env, "equal-mp").unwrap()).unwrap();
        let imp_t_opv = tm.mk_implies(&qt, &opv).unwrap();
        let d_imp = derive_mp(env, &q_rev, &imp_t_opv, d_emp, d_rev).unwrap();
        let d_t = derive_axiom(env, "truth").unwrap();
        check(&d_t, &derivable(env, &qt).unwrap());
        let d_final = derive_mp(env, &qt, &opv, d_imp, d_t).unwrap();
        check(&d_final, &derivable(env, &opv).unwrap());

        // 3. Transported ground control: ⊢ olt ⌜1⌝ ⌜ω⌝ = t.
        let w1 = acons(&acons(&aint(1), &aint(1)), &aint(0));
        let k2 = env.row("O<").unwrap();
        let ground2 = d.ord_fold(&app2(&d.olt, &aint(1), &w1)).unwrap();
        let d_lt = derive_comp_folded(env, k2, &[aint(1), w1.clone()], &ground2).unwrap();
        let phi = tm
            .mk_equal(
                &tm.app(
                    b"O<",
                    &[tm.quote(&aint(1)).unwrap(), tm.quote(&w1).unwrap()],
                )
                .unwrap(),
                &qt,
            )
            .unwrap();
        check(&d_lt, &derivable(env, &phi).unwrap());
        let projected = sess.project(&phi, d_lt).unwrap();
        let final_thm = transport_equal(env, &projected).unwrap();
        check(
            &final_thm,
            &app2(&d.olt, &aint(1), &w1).equals(d.pr.t.clone()).unwrap(),
        );
    }

    /// **G3 №12 — open IMPLIES transport:** the projected `plus-nonneg`
    /// axiom transports to exactly its own `ModelImplies` source
    /// statement (`model_implies_target`); coverage and shape failures
    /// mint nothing.
    #[test]
    fn t_transport_implies_open() {
        let sess = ord_session();
        let env = sess.env();

        let (i, enc) = env.axiom("plus-nonneg").unwrap();
        let enc = enc.clone();
        let der = derive_axiom(env, "plus-nonneg").unwrap();
        let projected = sess.project(&enc, der).unwrap();
        let out = transport_implies_open(env, &projected, &[(b"A", "a"), (b"B", "b")]).unwrap();
        // Exactly the target statement…
        check(&out, &model_implies_target(env, &enc).unwrap());
        // …which is exactly the installed ModelImplies source (the
        // §S6-gate cross-check pattern).
        match &env.axioms[i].discharge {
            Discharge::ModelImplies(src) => assert_eq!(out.concl(), src.concl()),
            _ => panic!("plus-nonneg must be a ModelImplies row"),
        }

        // Coverage negative control: an unbound object variable errors.
        assert!(transport_implies_open(env, &projected, &[(b"A", "a")]).is_err());
        // Duplicate bind errors.
        assert!(
            transport_implies_open(env, &projected, &[(b"A", "a"), (b"A", "b"), (b"B", "c")])
                .is_err()
        );
        // A projected EQUAL-form (no IMPLIES spine) is rejected here —
        // and conversely the EQUAL transport rejects the IMPLIES form.
        let (_, cp) = env.axiom("consp-plus").unwrap();
        let cp = cp.clone();
        let der = derive_axiom(env, "consp-plus").unwrap();
        let proj_cp = sess.project(&cp, der).unwrap();
        assert!(transport_implies_open(env, &proj_cp, &[(b"A", "a"), (b"B", "b")]).is_err());
        assert!(transport_equal_open(env, &projected, &[(b"A", "a"), (b"B", "b")]).is_err());
        // The EQUAL form still transports on its own path (control).
        let eq_out = transport_equal_open(env, &proj_cp, &[(b"A", "a"), (b"B", "b")]).unwrap();
        let d = o();
        let (xa, xb) = (avar("a"), avar("b"));
        let expected = app1(&d.pr.consp, &app2(&d.pr.plus, &xa, &xb))
            .equals(d.th.nil.clone())
            .unwrap()
            .forall("b", a())
            .unwrap()
            .forall("a", a())
            .unwrap();
        check(&eq_out, &expected);
    }

    /// **G3 (install controls):** the hand-row seam fails safe — a wrong
    /// (but proved) `def_eq_model` fails the `model_image` pin, a name
    /// collision is rejected, and `with_ordinals` demands an S6 env.
    #[test]
    fn t_install_user_rows_controls() {
        let d = o();
        let e6 = s6_env().unwrap();

        // Non-S6 envs are rejected outright.
        assert!(with_ordinals(&ground_env().unwrap()).is_err());

        // A wrong def_eq_model (POSP's proved equation on the NATP row)
        // fails the pin; nothing is installed.
        let mut rows = d.user_rows(&e6.tm).unwrap();
        let posp_eq = apply_def(&d.posp_eq, &[Term::free("X", a())])
            .unwrap()
            .all_intro("X", a())
            .unwrap();
        rows[0].def_eq_model = posp_eq;
        assert!(install_user_rows(&e6, rows).is_err());

        // Name collision with a primitive row.
        let mut rows = d.user_rows(&e6.tm).unwrap();
        rows[0].name = SmolStr::new("CAR");
        assert!(install_user_rows(&e6, rows).is_err());

        // The honest batch installs (rows only — the cheap slice of
        // `with_ordinals`, no pack/soundness here).
        let rows = d.user_rows(&e6.tm).unwrap();
        let env = install_user_rows(&e6, rows).unwrap();
        assert_eq!(env.rows.len(), 18);
        assert_eq!(env.users.len(), 7);
    }
}
