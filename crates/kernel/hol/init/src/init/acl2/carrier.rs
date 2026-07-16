//! **S0 — the ACL2 object-universe carrier.**
//!
//! The model carrier is a **second instance of the carved exact-type
//! construction** ([`crate::init::inductive::carved`]) at atom payload
//! `P := coprod int bytes`:
//!
//! ```text
//!   A  :=  aatom P  |  anil  |  acons A A          (P = coprod int bytes)
//!   aint i := aatom (inl i)      asym s := aatom (inr s)
//! ```
//!
//! so structural induction, case analysis, constructor injectivity /
//! distinctness, and the paramorphic recursor all come out of the *same
//! proofs* as the flagship `sexpr` instance, run at the other payload.
//! Integers enter as first-class payload — **not** bytes-encoded (the
//! open-form `bytes ↔ nat` seam is declaration-only) and **not** as an
//! unconstrained free variable (the `lang/lisp` `int_head` trap) — so
//! every ∀-quantified arithmetic fact lifts from the proved
//! [`crate::init::int`] theory at later stages.
//!
//! ACL2's `nil` is modelled by the datatype leaf `anil` (the carved
//! `car`/`cdr` leaf defaults `car (aatom b) = car anil = anil` then *are*
//! ACL2's completion axioms); `t` is `asym "T"` (S1). **Representation
//! contract:** front ends must never emit `asym "NIL"` — it would be a
//! junk value distinct from `anil`.
//!
//! Everything is a derived theorem over existing kernel rules; nothing
//! here is trusted, no axiom is postulated.

use std::sync::LazyLock;

use covalence_core::{Error, Result, Term, Type, subst};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::derived::DerivedRules;
use covalence_inductive::{ArgSort, CtorSpec, InductiveSpec};

use crate::init::coprod::{inl_inj, inl_ne_inr, inr_inj};
use crate::init::ext::TermExt;
use crate::init::inductive::Inductive;
use crate::init::inductive::api::derive_cases_native;
use crate::init::inductive::carved::{CarvedSExpr, apply_def};

use covalence_hol_eval::defs::{coprod, inl, inr};

/// The atom payload `P := coprod int bytes` — integer atoms left,
/// symbol atoms (as their name bytes) right.
pub fn acl2_payload() -> Type {
    coprod(Type::int(), Type::bytes())
}

/// The process-global carved instance at the ACL2 payload. Built exactly
/// once; the initializer calls [`CarvedSExpr::build_with`] directly and
/// never another theory `LazyLock` (re-entrancy discipline).
pub fn acl2_carved() -> Result<&'static CarvedSExpr> {
    static ACL2_CARVED: LazyLock<std::result::Result<CarvedSExpr, String>> = LazyLock::new(|| {
        CarvedSExpr::build_with(acl2_payload(), "acl2.sexpr").map_err(|e| e.to_string())
    });
    ACL2_CARVED
        .as_ref()
        .map_err(|e| Error::ConnectiveRule(format!("acl2 carved build failed: {e}")))
}

/// The engine spec of the ACL2 carrier (binder hints `b`/`h`/`t` —
/// load-bearing for `induct`'s `inst` keys, same as the `sexpr` spec).
pub fn acl2_spec() -> InductiveSpec<Type> {
    InductiveSpec::new(
        "acl2.sexpr",
        vec![
            CtorSpec::new("aatom", [("b", ArgSort::Ext(acl2_payload()))]),
            CtorSpec::nullary("anil"),
            CtorSpec::new("acons", [("h", ArgSort::Rec), ("t", ArgSort::Rec)]),
        ],
    )
}

/// Split a `⊢ C = body` definition into `(C, the equation)`.
fn defined(name: &str, body: Term) -> Result<(Term, Thm)> {
    let eq = Thm::define(name, body)?;
    let c = eq.concl().as_eq().ok_or(Error::NotAnEquation)?.0.clone();
    Ok((c, eq))
}

/// The ACL2 carrier theory: the carved instance plus the derived payload
/// constructors `aint`/`asym` and their freeness. Built exactly once
/// ([`acl2`]).
pub struct Acl2 {
    /// The underlying carved instance (recursor, induction, projections).
    pub cs: &'static CarvedSExpr,
    /// The carrier type `A`.
    pub ty: Type,
    /// `aatom : coprod int bytes → A`.
    pub atom: Term,
    /// `anil : A` (ACL2's `nil`).
    pub nil: Term,
    /// `acons : A → A → A`.
    pub cons: Term,
    /// `car : A → A` (`car (acons h t) = h`; leaves default to `anil`).
    pub car: Term,
    /// `cdr : A → A` (same default).
    pub cdr: Term,
    /// `aint : int → A` — `Thm::define`d as `λi. aatom (inl i)`.
    pub aint: Term,
    aint_eq: Thm,
    /// `asym : bytes → A` — `Thm::define`d as `λs. aatom (inr s)`.
    pub asym: Term,
    asym_eq: Thm,
}

/// The process-global ACL2 carrier theory.
pub fn acl2() -> Result<&'static Acl2> {
    static ACL2: LazyLock<std::result::Result<Acl2, String>> =
        LazyLock::new(|| Acl2::build().map_err(|e| e.to_string()));
    ACL2.as_ref()
        .map_err(|e| Error::ConnectiveRule(format!("acl2 carrier build failed: {e}")))
}

impl Acl2 {
    fn build() -> Result<Acl2> {
        let cs = acl2_carved()?;

        // aint := λi:int. aatom (inl i).
        let (aint, aint_eq) = {
            let i = Term::free("__i", Type::int());
            let body = cs
                .atom
                .clone()
                .apply(inl(Type::int(), Type::bytes()).apply(i)?)?;
            defined(
                "acl2.int",
                Term::abs(Type::int(), subst::close(&body, "__i")),
            )?
        };
        // asym := λs:bytes. aatom (inr s).
        let (asym, asym_eq) = {
            let s = Term::free("__s", Type::bytes());
            let body = cs
                .atom
                .clone()
                .apply(inr(Type::int(), Type::bytes()).apply(s)?)?;
            defined(
                "acl2.sym",
                Term::abs(Type::bytes(), subst::close(&body, "__s")),
            )?
        };

        Ok(Acl2 {
            cs,
            ty: cs.tau.clone(),
            atom: cs.atom.clone(),
            nil: cs.snil.clone(),
            cons: cs.scons.clone(),
            car: cs.car.clone(),
            cdr: cs.cdr.clone(),
            aint,
            aint_eq,
            asym,
            asym_eq,
        })
    }

    // ------------------------------------------------------------------
    // Term builders
    // ------------------------------------------------------------------

    /// `aint i : A`.
    pub fn aint_at(&self, i: &Term) -> Result<Term> {
        self.aint.clone().apply(i.clone())
    }

    /// `asym s : A`.
    pub fn asym_at(&self, s: &Term) -> Result<Term> {
        self.asym.clone().apply(s.clone())
    }

    /// `asym ⌜s⌝ : A` at a bytes literal (symbol names).
    pub fn asym_lit(&self, s: &[u8]) -> Result<Term> {
        self.asym_at(&covalence_hol_eval::mk_blob(covalence_types::Bytes::from(
            s.to_vec(),
        )))
    }

    /// `⊢ aint i = aatom (inl i)` / `⊢ asym s = aatom (inr s)` — unfold a
    /// payload constructor through its definition (`apply_def`).
    fn payload_unfold(&self, is_int: bool, v: &Term) -> Result<Thm> {
        let eq = if is_int { &self.aint_eq } else { &self.asym_eq };
        apply_def(eq, std::slice::from_ref(v))
    }

    /// `inl v` / `inr v` at the payload coprod.
    fn payload_wrap(is_int: bool, v: &Term) -> Result<Term> {
        if is_int {
            inl(Type::int(), Type::bytes()).apply(v.clone())
        } else {
            inr(Type::int(), Type::bytes()).apply(v.clone())
        }
    }

    // ------------------------------------------------------------------
    // Freeness (all closed kernel theorems)
    // ------------------------------------------------------------------

    /// `⊢ (acons h t = acons h2 t2) ⟹ (h = h2 ∧ t = t2)` — `acons`
    /// injectivity at both (recursive) positions, from the instance's
    /// projection-based freeness.
    pub fn cons_inj(&self, h: &Term, t: &Term, h2: &Term, t2: &Term) -> Result<Thm> {
        self.cs
            .inductive()
            .injective(2, &[h.clone(), t.clone()], &[h2.clone(), t2.clone()])
    }

    /// `⊢ (aatom l = aatom l2) ⟹ l = l2` — payload injectivity of the
    /// datatype `aatom` constructor.
    pub fn atom_inj(&self, l: &Term, l2: &Term) -> Result<Thm> {
        self.cs.inj_atom(l, l2)
    }

    /// `⊢ (Cᵢ x⃗ = Cⱼ y⃗) ⟹ F` for `i ≠ j` (constructor order:
    /// `aatom`, `anil`, `acons`).
    pub fn distinct(&self, i: usize, j: usize, xs: &[Term], ys: &[Term]) -> Result<Thm> {
        self.cs.inductive().distinct(i, j, xs, ys)
    }

    /// Shared spine of [`Self::int_inj`] / [`Self::sym_inj`]:
    /// `⊢ (K v = K v2) ⟹ v = v2` for `K ∈ {aint, asym}`, via `atom_inj`
    /// composed with the coprod injection's injectivity.
    fn payload_inj(&self, is_int: bool, v: &Term, v2: &Term) -> Result<Thm> {
        let ctor = if is_int { &self.aint } else { &self.asym };
        let eq = ctor
            .clone()
            .apply(v.clone())?
            .equals(ctor.clone().apply(v2.clone())?)?;
        // {eq} ⊢ aatom (inj v) = aatom (inj v2).
        let atoms = self
            .payload_unfold(is_int, v)?
            .sym()?
            .trans(Thm::assume(eq.clone())?)?
            .trans(self.payload_unfold(is_int, v2)?)?;
        // {eq} ⊢ inj v = inj v2.
        let labels = self
            .atom_inj(
                &Self::payload_wrap(is_int, v)?,
                &Self::payload_wrap(is_int, v2)?,
            )?
            .imp_elim(atoms)?;
        // {eq} ⊢ v = v2 (coprod injection injectivity).
        let core = if is_int {
            inl_inj(&Type::int(), &Type::bytes(), v, v2)?
        } else {
            inr_inj(&Type::int(), &Type::bytes(), v, v2)?
        }
        .imp_elim(labels)?;
        core.imp_intro(&eq)
    }

    /// `⊢ (aint i = aint j) ⟹ i = j`.
    pub fn int_inj(&self, i: &Term, j: &Term) -> Result<Thm> {
        self.payload_inj(true, i, j)
    }

    /// `⊢ (asym s = asym s2) ⟹ s = s2`.
    pub fn sym_inj(&self, s: &Term, s2: &Term) -> Result<Thm> {
        self.payload_inj(false, s, s2)
    }

    /// `⊢ (aint i = asym s) ⟹ F` — integer and symbol atoms are
    /// distinct (`inl ≠ inr` at the payload).
    pub fn int_ne_sym(&self, i: &Term, s: &Term) -> Result<Thm> {
        let eq = self.aint_at(i)?.equals(self.asym_at(s)?)?;
        let atoms = self
            .payload_unfold(true, i)?
            .sym()?
            .trans(Thm::assume(eq.clone())?)?
            .trans(self.payload_unfold(false, s)?)?;
        let labels = self
            .atom_inj(
                &Self::payload_wrap(true, i)?,
                &Self::payload_wrap(false, s)?,
            )?
            .imp_elim(atoms)?; // {eq} ⊢ inl i = inr s
        let f = inl_ne_inr(&Type::int(), &Type::bytes(), i, s)?.not_elim(labels)?; // {eq} ⊢ F
        f.imp_intro(&eq)
    }

    /// `⊢ ¬(asym ⌜s1⌝ = asym ⌜s2⌝)` for **distinct byte literals** —
    /// contrapose [`Self::sym_inj`] against `reduce`'s literal
    /// disequality. Errors if the literals are equal.
    pub fn sym_ne(&self, s1: &[u8], s2: &[u8]) -> Result<Thm> {
        let b1 = covalence_hol_eval::mk_blob(covalence_types::Bytes::from(s1.to_vec()));
        let b2 = covalence_hol_eval::mk_blob(covalence_types::Bytes::from(s2.to_vec()));
        // ⊢ (⌜s1⌝ = ⌜s2⌝) = ⌜F⌝ by literal evaluation.
        let ne = b1.clone().equals(b2.clone())?.reduce()?;
        match ne.concl().as_eq().and_then(|(_, r)| r.as_bool()) {
            Some(false) => {}
            _ => {
                return Err(Error::ConnectiveRule(format!(
                    "acl2 sym_ne: literals did not reduce to distinct ({ne})"
                )));
            }
        }
        let eq = self.asym_at(&b1)?.equals(self.asym_at(&b2)?)?;
        let inner = self.sym_inj(&b1, &b2)?.imp_elim(Thm::assume(eq.clone())?)?; // {eq} ⊢ ⌜s1⌝ = ⌜s2⌝
        let f_lit = ne.eq_mp(inner)?; // {eq} ⊢ ⌜F⌝
        let f = covalence_hol_eval::fal_from_lit(f_lit)?; // {eq} ⊢ F
        f.imp_intro(&eq)?.not_intro()
    }

    // ------------------------------------------------------------------
    // Induction + case analysis
    // ------------------------------------------------------------------

    /// Rule-form structural induction: from `⊢ P (aatom b)` (free `b`),
    /// `⊢ P anil`, `⊢ P h ⟹ P t ⟹ P (acons h t)` (free `h`, `t`)
    /// conclude `⊢ ∀s:A. P s`. Binder-hint names `b`/`h`/`t` are
    /// mandatory (`inst` is keyed on them).
    pub fn induct(&self, motive: &Term, cases: Vec<Thm>) -> Result<Thm> {
        self.cs.induct(motive, cases)
    }

    /// Exhaustiveness:
    /// `⊢ ∀s. (∃b. s = aatom b) ∨ ((s = anil) ∨ (∃h t. s = acons h t))`.
    pub fn cases(&self) -> Result<Thm> {
        let ctors = [self.atom.clone(), self.nil.clone(), self.cons.clone()];
        derive_cases_native(&acl2_spec(), &self.ty, &ctors, &|m: &Term, c: Vec<Thm>| {
            Ok(self.cs.induct(m, c)?)
        })
        .map_err(|e| Error::ConnectiveRule(format!("acl2 cases: {e}")))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::init::eq::{beta_expand, beta_reduce};
    use crate::init::ext::ThmExt;

    fn a() -> &'static Acl2 {
        acl2().unwrap()
    }

    fn avar(n: &str) -> Term {
        Term::free(n, a().ty.clone())
    }

    /// The theory builds; the constructors have the designed types; the
    /// carrier is a fresh type (distinct from the `sexpr` instance).
    #[test]
    fn t_carrier_builds() {
        let th = a();
        let p = acl2_payload();
        assert_eq!(
            th.atom.type_of().unwrap(),
            Type::fun(p.clone(), th.ty.clone())
        );
        assert_eq!(th.nil.type_of().unwrap(), th.ty);
        assert_eq!(
            th.cons.type_of().unwrap(),
            Type::fun(th.ty.clone(), Type::fun(th.ty.clone(), th.ty.clone()))
        );
        assert_eq!(
            th.aint.type_of().unwrap(),
            Type::fun(Type::int(), th.ty.clone())
        );
        assert_eq!(
            th.asym.type_of().unwrap(),
            Type::fun(Type::bytes(), th.ty.clone())
        );
        // A genuinely fresh subtype, not the sexpr carrier.
        let sexpr = crate::init::inductive::carved::carved().unwrap();
        assert_ne!(th.ty, sexpr.tau);
    }

    /// **S0 gate:** `acons` injectivity as a closed kernel theorem with
    /// the exact designed statement.
    #[test]
    fn t_cons_inj() {
        let th = a();
        let (h, t, h2, t2) = (avar("h"), avar("t"), avar("h2"), avar("t2"));
        let thm = th.cons_inj(&h, &t, &h2, &t2).unwrap();
        assert!(thm.hyps().is_empty(), "cons_inj must be closed");
        let lhs = th
            .cons
            .clone()
            .apply(h.clone())
            .unwrap()
            .apply(t.clone())
            .unwrap();
        let rhs = th
            .cons
            .clone()
            .apply(h2.clone())
            .unwrap()
            .apply(t2.clone())
            .unwrap();
        let expected = lhs
            .equals(rhs)
            .unwrap()
            .imp(h.equals(h2).unwrap().and(t.equals(t2).unwrap()).unwrap())
            .unwrap();
        assert_eq!(thm.concl(), &expected);
    }

    /// **S0 gate:** all six ordered constructor-distinctness pairs are
    /// closed theorems (mirrors `carved::distinctness_all_pairs`).
    #[test]
    fn t_distinct_all_pairs() {
        let th = a();
        let b = Term::free("b", acl2_payload());
        let (h, t) = (avar("h"), avar("t"));
        let args: [&[Term]; 3] = [std::slice::from_ref(&b), &[], &[h.clone(), t.clone()]];
        for i in 0..3 {
            for j in 0..3 {
                if i == j {
                    continue;
                }
                let d = th.distinct(i, j, args[i], args[j]).unwrap();
                assert!(d.hyps().is_empty(), "distinct({i},{j}) must be closed");
            }
        }
        // Exact statement at the (atom, nil) pair: (aatom b = anil) ⟹ F.
        let d01 = th.distinct(0, 1, std::slice::from_ref(&b), &[]).unwrap();
        let atom_b = th.atom.clone().apply(b).unwrap();
        let (ante, _) = d01
            .concl()
            .as_app()
            .and_then(|(f, _)| f.as_app())
            .map(|(_, a)| (a.clone(), ()))
            .expect("distinct concl is an implication");
        assert_eq!(ante, atom_b.equals(th.nil.clone()).unwrap());
    }

    /// **S0 gate:** derived-constructor freeness — `aint`/`asym`
    /// injectivity, `aint ≠ asym`, and a ground symbol disequality
    /// (`reduce`'s literal path), all closed with exact statements.
    #[test]
    fn t_payload_freeness() {
        let th = a();
        let i = Term::free("i", Type::int());
        let j = Term::free("j", Type::int());
        let s = Term::free("s", Type::bytes());
        let s2 = Term::free("s2", Type::bytes());

        let ii = th.int_inj(&i, &j).unwrap();
        assert!(ii.hyps().is_empty());
        let expected = th
            .aint_at(&i)
            .unwrap()
            .equals(th.aint_at(&j).unwrap())
            .unwrap()
            .imp(i.clone().equals(j.clone()).unwrap())
            .unwrap();
        assert_eq!(ii.concl(), &expected);

        let si = th.sym_inj(&s, &s2).unwrap();
        assert!(si.hyps().is_empty());
        let expected = th
            .asym_at(&s)
            .unwrap()
            .equals(th.asym_at(&s2).unwrap())
            .unwrap()
            .imp(s.clone().equals(s2.clone()).unwrap())
            .unwrap();
        assert_eq!(si.concl(), &expected);

        let ns = th.int_ne_sym(&i, &s).unwrap();
        assert!(ns.hyps().is_empty());

        // Ground instance: ⊢ ¬(asym "T" = asym "NIL").
        let ne = th.sym_ne(b"T", b"NIL").unwrap();
        assert!(ne.hyps().is_empty(), "sym_ne must be closed");
        let expected = th
            .asym_lit(b"T")
            .unwrap()
            .equals(th.asym_lit(b"NIL").unwrap())
            .unwrap()
            .not()
            .unwrap();
        assert_eq!(ne.concl(), &expected);

        // Equal literals must NOT produce a "theorem".
        assert!(th.sym_ne(b"T", b"T").is_err());
    }

    /// **S0 gate:** the exhaustiveness theorem, with the exact designed
    /// disjunction after instantiation.
    #[test]
    fn t_cases() {
        let th = a();
        let cases = th.cases().unwrap();
        assert!(cases.hyps().is_empty(), "cases must be closed");
        let sv = avar("s0");
        let inst = beta_reduce(cases.all_elim(sv.clone()).unwrap()).unwrap();
        // (∃b. s0 = aatom b) ∨ ((s0 = anil) ∨ (∃h t. s0 = acons h t)).
        let d0 = {
            let b = Term::free("__cases_c0", acl2_payload());
            sv.clone()
                .equals(th.atom.clone().apply(b.clone()).unwrap())
                .unwrap()
                .exists("__cases_c0", acl2_payload())
                .unwrap()
        };
        let d1 = sv.clone().equals(th.nil.clone()).unwrap();
        let d2 = {
            let h = Term::free("__cases_c0", th.ty.clone());
            let t = Term::free("__cases_c1", th.ty.clone());
            sv.clone()
                .equals(
                    th.cons
                        .clone()
                        .apply(h.clone())
                        .unwrap()
                        .apply(t.clone())
                        .unwrap(),
                )
                .unwrap()
                .exists("__cases_c1", th.ty.clone())
                .unwrap()
                .exists("__cases_c0", th.ty.clone())
                .unwrap()
        };
        let expected = d0.or(d1.or(d2).unwrap()).unwrap();
        assert_eq!(inst.concl(), &expected);
    }

    /// **S0 gate:** the paramorphic recursor computes — one `prec_eq`
    /// computation equation per constructor at `β := A`, with the
    /// engine-contract shape at the `acons` case.
    #[test]
    fn t_prec_smoke() {
        let th = a();
        let cs = th.cs;
        let beta = th.ty.clone();
        let steps = [
            Term::free("sa", Type::fun(acl2_payload(), beta.clone())),
            Term::free("sn", beta.clone()),
            Term::free(
                "sc",
                Type::fun(
                    th.ty.clone(),
                    Type::fun(
                        th.ty.clone(),
                        Type::fun(beta.clone(), Type::fun(beta.clone(), beta.clone())),
                    ),
                ),
            ),
        ];
        for i in 0..3 {
            let eq = cs.prec_eq(&steps, i, &beta).unwrap();
            assert!(eq.hyps().is_empty(), "prec_eq({i}) must be closed");
        }
        // The acons equation: ∀h t. rec s⃗ (acons h t) = sc h t (rec s⃗ h) (rec s⃗ t).
        let (h, t) = (avar("h"), avar("t"));
        let eq2 = cs
            .prec_eq(&steps, 2, &beta)
            .unwrap()
            .all_elim(h.clone())
            .unwrap()
            .all_elim(t.clone())
            .unwrap();
        let rec = cs.prec(&steps, &beta).unwrap();
        let lhs = rec
            .clone()
            .apply(
                th.cons
                    .clone()
                    .apply(h.clone())
                    .unwrap()
                    .apply(t.clone())
                    .unwrap(),
            )
            .unwrap();
        let rhs = steps[2]
            .clone()
            .apply(h.clone())
            .unwrap()
            .apply(t.clone())
            .unwrap()
            .apply(rec.clone().apply(h).unwrap())
            .unwrap()
            .apply(rec.apply(t).unwrap())
            .unwrap();
        assert_eq!(eq2.concl(), &lhs.equals(rhs).unwrap());
    }

    // ------------------------------------------------------------------
    // The induction-instance gate: `aappend` associativity, the
    // `init/lisp.rs::append_assoc` skeleton transplanted onto the ACL2
    // carrier (S4 preview).
    // ------------------------------------------------------------------

    /// A test-local `aappend` theory over the ACL2 carrier (the lisp.rs
    /// paramorphism, payload swapped).
    struct Append {
        cs: &'static CarvedSExpr,
        append: Term,
        append_eq: Thm,
    }

    impl Append {
        fn build() -> Result<Append> {
            let cs = acl2_carved()?;
            let tau = &cs.tau;
            let x = Term::free("__x", tau.clone());
            let y = Term::free("__y", tau.clone());
            let rec_x = cs.prec(&Self::steps(cs, &y)?, tau)?.apply(x)?;
            let l_y = Term::abs(tau.clone(), subst::close(&rec_x, "__y"));
            let body = Term::abs(tau.clone(), subst::close(&l_y, "__x"));
            let (append, append_eq) = defined("acl2.test.append", body)?;
            Ok(Append {
                cs,
                append,
                append_eq,
            })
        }

        /// `λb. w`, `w`, `λh t bh bt. acons h bt`.
        fn steps(cs: &CarvedSExpr, w: &Term) -> Result<[Term; 3]> {
            let tau = &cs.tau;
            let sa = Term::abs(cs.payload.clone(), w.clone());
            let sn = w.clone();
            let h = Term::free("__h", tau.clone());
            let bt = Term::free("__bt", tau.clone());
            let scons_h_bt = cs.scons.clone().apply(h)?.apply(bt)?;
            let l_bt = Term::abs(tau.clone(), subst::close(&scons_h_bt, "__bt"));
            let l_bh = Term::abs(tau.clone(), l_bt);
            let l_t = Term::abs(tau.clone(), l_bh);
            let sc = Term::abs(tau.clone(), subst::close(&l_t, "__h"));
            Ok([sa, sn, sc])
        }

        /// `⊢ aappend (aatom b) w = w` / `⊢ aappend anil w = w`.
        fn leaf(&self, atom_arg: Option<&Term>, w: &Term) -> Result<Thm> {
            let steps = Self::steps(self.cs, w)?;
            let tau = &self.cs.tau;
            match atom_arg {
                Some(b) => {
                    let atom_b = self.cs.atom.clone().apply(b.clone())?;
                    let e = apply_def(&self.append_eq, &[atom_b, w.clone()])?;
                    let comp = self.cs.prec_eq(&steps, 0, tau)?.all_elim(b.clone())?;
                    e.trans(comp)?.reduce_rhs()
                }
                None => {
                    let e = apply_def(&self.append_eq, &[self.cs.snil.clone(), w.clone()])?;
                    let comp = self.cs.prec_eq(&steps, 1, tau)?;
                    e.trans(comp)
                }
            }
        }

        /// `⊢ aappend (acons h t) w = acons h (aappend t w)` (fold the
        /// recursor images back before reducing — the lisp.rs:301 trick).
        fn scons(&self, h: &Term, t: &Term, w: &Term) -> Result<Thm> {
            let steps = Self::steps(self.cs, w)?;
            let tau = &self.cs.tau;
            let scons_ht = self.cs.scons.clone().apply(h.clone())?.apply(t.clone())?;
            let e = apply_def(&self.append_eq, &[scons_ht, w.clone()])?;
            let comp = self
                .cs
                .prec_eq(&steps, 2, tau)?
                .all_elim(h.clone())?
                .all_elim(t.clone())?;
            let ah = apply_def(&self.append_eq, &[h.clone(), w.clone()])?;
            let at = apply_def(&self.append_eq, &[t.clone(), w.clone()])?;
            let e = e.trans(comp)?;
            let e = e.rhs_conv(|tm| tm.rw_all(&ah.sym()?))?;
            let e = e.rhs_conv(|tm| tm.rw_all(&at.sym()?))?;
            e.reduce_rhs()
        }

        /// `⊢ ∀y z x. aappend (aappend x y) z = aappend x (aappend y z)`
        /// by structural induction on `x`.
        fn assoc(&self) -> Result<Thm> {
            let tau = self.cs.tau.clone();
            let y = Term::free("y", tau.clone());
            let z = Term::free("z", tau.clone());
            let ap = |a: &Term, b: &Term| self.append.clone().apply(a.clone())?.apply(b.clone());
            let yz = ap(&y, &z)?;

            let motive = {
                let x = Term::free("x", tau.clone());
                let lhs = ap(&ap(&x, &y)?, &z)?;
                let rhs = ap(&x, &yz)?;
                Term::abs(tau.clone(), subst::close(&lhs.equals(rhs)?, "x"))
            };

            let leaf_case = |atom_arg: Option<&Term>, leaf_c: Term| -> Result<Thm> {
                let inner = self.leaf(atom_arg, &y)?; // aappend leaf y = y
                let lhs_eq = inner.cong_arg(self.append.clone())?.cong_fn(z.clone())?;
                let rhs_eq = self.leaf(atom_arg, &yz)?;
                let raw = lhs_eq.trans(rhs_eq.sym()?)?;
                beta_expand(&motive, leaf_c, raw)
            };
            let b = Term::free("b", self.cs.payload.clone());
            let case_atom = leaf_case(Some(&b), self.cs.atom.clone().apply(b.clone())?)?;
            let case_nil = leaf_case(None, self.cs.snil.clone())?;

            let case_cons = {
                let h = Term::free("h", tau.clone());
                let t = Term::free("t", tau.clone());
                let ph = motive.clone().apply(h.clone())?;
                let pt = motive.clone().apply(t.clone())?;
                let ih = beta_reduce(Thm::assume(pt.clone())?)?;

                let scons_ht = self.cs.scons.clone().apply(h.clone())?.apply(t.clone())?;
                let s1 = self.scons(&h, &t, &y)?;
                let lhs1 = s1.cong_arg(self.append.clone())?.cong_fn(z.clone())?;
                let t_y = ap(&t, &y)?;
                let s2 = self.scons(&h, &t_y, &z)?;
                let lhs = lhs1.trans(s2)?;
                let scons_h = self.cs.scons.clone().apply(h.clone())?;
                let mid = ih.cong_arg(scons_h)?;
                let s3 = self.scons(&h, &t, &yz)?;
                let raw = lhs.trans(mid)?.trans(s3.sym()?)?;

                beta_expand(&motive, scons_ht, raw)?
                    .imp_intro(&pt)?
                    .imp_intro(&ph)?
            };

            let by_x = self
                .cs
                .induct(&motive, vec![case_atom, case_nil, case_cons])?;
            by_x.all_intro("z", tau.clone())?.all_intro("y", tau)
        }
    }

    /// **S0 gate (the induction instance):** a genuine structural-
    /// induction theorem on the ACL2 carrier — `aappend` associativity,
    /// closed, with the exact statement.
    #[test]
    fn t_induct_instance() {
        let ap_th = Append::build().unwrap();
        let thm = ap_th.assoc().unwrap(); // ⊢ ∀y z x. …
        assert!(thm.hyps().is_empty(), "aappend assoc must be closed");
        let (x, y, z) = (avar("x0"), avar("y0"), avar("z0"));
        let inst = thm
            .all_elim(y.clone())
            .unwrap()
            .all_elim(z.clone())
            .unwrap()
            .all_elim(x.clone())
            .unwrap();
        let inst = beta_reduce(inst).unwrap();
        let ap = |a: &Term, b: &Term| {
            ap_th
                .append
                .clone()
                .apply(a.clone())
                .unwrap()
                .apply(b.clone())
                .unwrap()
        };
        let lhs = ap(&ap(&x, &y), &z);
        let rhs = ap(&x, &ap(&y, &z));
        assert_eq!(inst.concl(), &lhs.equals(rhs).unwrap());
    }
}
