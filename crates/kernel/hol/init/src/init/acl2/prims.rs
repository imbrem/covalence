//! **S1 — ACL2 model primitives + completion axioms over the S0 carrier.**
//!
//! Every ACL2 primitive is a total HOL function over the carrier `A`
//! ([`super::carrier`]), `Thm::define`d — no postulates anywhere. ACL2
//! predicates return **`A`-valued booleans** (`t` / `nil`), since they
//! occur *inside* terms:
//!
//! ```text
//!   t        := asym ⌜"T"⌝                                    ("acl2.t")
//!   (nil      = the carrier anil — representation note below)
//!   aconsp   := prec [λl. nil, nil, λh t _ _. t]              : A → A
//!   aatomp   := prec [λl. t, t, λh t _ _. nil]                : A → A
//!   aendp    := aatomp                                        ("acl2.endp")
//!   asymbolp := prec [λl. case (λi. nil) (λs. t) l, t, …nil]  : A → A
//!   aintp    := prec [λl. case (λi. t) (λs. nil) l, nil, …nil]: A → A
//!   intval   := prec [λl. case (λi. i) (λs. 0) l, 0, …0]      : A → int
//!   aequal   := λx y. cond A (x = y) t nil
//!   aif      := λc y z. cond A (c = anil) z y
//!   aplus    := λx y. aint (intAdd (intval x) (intval y))
//!   atimes   := λx y. aint (intMul (intval x) (intval y))
//!   aneg     := λx.   aint (intNeg (intval x))
//!   aminus   := λx y. aplus x (aneg y)          (ACL2 `(- x y)` macro shape)
//!   alt      := λx y. cond A (intLt (intval x) (intval y)) t nil
//!   ale      := λx y. aif (alt y x) anil t      (ACL2 `(<= x y)` macro shape)
//! ```
//!
//! ACL2's **completion axioms** are *proved theorems* here: `car`/`cdr` of
//! any non-cons is `anil` (the carved `proj_leaf` laws lifted through the
//! payload constructors), and non-numbers coerce to `0` in arithmetic
//! (the `intval` catamorphism — `intval (asym s) = intval anil =
//! intval (acons h t) = 0`). Arithmetic **lifts from the fully-proved
//! [`crate::init::int`] ordered-ring theory** through the single seam
//! `intval_int : ⊢ ∀i. intval (aint i) = i` — no bytes/encoding proofs
//! anywhere ([`plus_comm`](Prims::plus_comm) / [`plus_assoc`](Prims::plus_assoc)
//! are the S1 demonstration set; further axioms lift the same way on demand).
//!
//! **Representation contract (honesty):** ACL2's `nil` is modelled by the
//! datatype leaf `anil`, *not* by `asym "NIL"`; `t` is `asym "T"`.
//! `asymbolp anil = t` (nil *is* a symbol in ACL2). A front-end translator
//! must never emit `asym "NIL"` — it would be a junk value distinct from
//! `anil` (enforced at the S11 translator, recorded here).
//!
//! `aequal` is genuinely **total on `A × A`**: it is `cond` on the HOL
//! equation `x = y` (total by definition of HOL equality), with
//! [`equal_refl`](Prims::equal_refl) / [`equal_ne`](Prims::equal_ne) /
//! [`equal_holds`](Prims::equal_holds) tying its `t`/`nil` answers to
//! genuine (dis)equality — the design's alternative to a structural
//! catamorphism.
//!
//! The [`PrimRow`] table is the single data structure S2's `eval` dispatch
//! and S3's congruence/computation clauses are driven from (design §8).

use std::sync::LazyLock;

use covalence_core::{Error, Result, Term, Type, subst};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::derived::DerivedRules;
use covalence_hol_eval::{fal_from_lit, fal_to_lit, mk_bool, mk_int};
use covalence_types::Bytes;

use crate::init::acl2::carrier::{Acl2, acl2, acl2_payload};
use crate::init::cond::{collapse_conds, cond};
use crate::init::coprod::{case_inl, case_inr, coprod_case, inl, inr};
use crate::init::ext::{TermExt, ThmExt};
use crate::init::inductive::carved::{LeafKind, apply_def};
use crate::init::int;

/// A `Thm::define`d catamorphism bundle: the constant, its defining
/// equation, the recursor step terms (identical to define time — the
/// computation laws re-derive `prec_eq` against them), the result type,
/// and — when the atom step dispatches on the payload — the two
/// `coprod_case` arms.
struct Cata {
    con: Term,
    def_eq: Thm,
    steps: [Term; 3],
    beta: Type,
    /// `(cf : int → β, cg : bytes → β)` when `steps[0] = λl. case cf cg l`.
    cases: Option<(Term, Term)>,
}

/// One row of the ACL2 primitive table (design §8): the surface symbol,
/// its arity, and the total model function over `A`. Drives S2's `eval`
/// dispatch spine and S3's congruence + computation clauses. `IF` and
/// `QUOTE` are special forms (handled before the table); `ATOM`/`ENDP`,
/// `<=` and binary `-` are ACL2 *defuns/macros*, not table rows. Since
/// S4, user `defun` rows are appended to the same table (S4+S6 design
/// §1–§2): `sym` is a `SmolStr` so admitted names need not be static.
#[derive(Clone)]
pub struct PrimRow {
    /// The ACL2 surface symbol, e.g. `"BINARY-+"`.
    pub sym: smol_str::SmolStr,
    /// Number of arguments.
    pub arity: usize,
    /// The model function (an `A → … → A` constant).
    pub model: Term,
}

/// The S1 primitive theory over the ACL2 carrier. Built exactly once
/// ([`prims`]).
pub struct Prims {
    /// The S0 carrier theory.
    pub th: &'static Acl2,
    /// `t : A` — ACL2 true, `Thm::define`d as `asym ⌜"T"⌝`.
    pub t: Term,
    t_eq: Thm,
    /// `aconsp : A → A`.
    pub consp: Term,
    /// `aatomp : A → A` (ACL2 `atom`, the complement of `consp`).
    pub atomp: Term,
    /// `aendp : A → A` — defined equal to [`Prims::atomp`].
    pub endp: Term,
    endp_eq: Thm,
    /// `asymbolp : A → A` (`t` on symbol atoms *and* `anil`).
    pub symbolp: Term,
    /// `aintp : A → A` (ACL2 `integerp`).
    pub intp: Term,
    /// `intval : A → int` — the arithmetic-completion catamorphism
    /// (non-numbers read as `0`); THE lifting seam.
    pub intval: Term,
    /// `aequal : A → A → A`.
    pub equal: Term,
    equal_eq: Thm,
    /// `aif : A → A → A → A` (strict; ACL2's logic is total).
    pub aif: Term,
    aif_eq: Thm,
    /// `aplus : A → A → A` (ACL2 `BINARY-+`).
    pub plus: Term,
    plus_eq: Thm,
    /// `atimes : A → A → A` (ACL2 `BINARY-*`).
    pub times: Term,
    times_eq: Thm,
    /// `aneg : A → A` (ACL2 `UNARY--`).
    pub neg: Term,
    neg_eq: Thm,
    /// `aminus : A → A → A` — `aplus x (aneg y)` (the `(- x y)` macro shape).
    pub minus: Term,
    minus_eq: Thm,
    /// `alt : A → A → A` (ACL2 `<`).
    pub lt: Term,
    /// `ale : A → A → A` — `aif (alt y x) anil t` (the `(<= x y)` macro shape).
    pub le: Term,

    consp_cata: Cata,
    atomp_cata: Cata,
    symbolp_cata: Cata,
    intp_cata: Cata,
    intval_cata: Cata,
}

/// The process-global S1 primitive theory.
pub fn prims() -> Result<&'static Prims> {
    static PRIMS: LazyLock<std::result::Result<Prims, String>> =
        LazyLock::new(|| Prims::build().map_err(|e| e.to_string()));
    PRIMS
        .as_ref()
        .map_err(|e| Error::ConnectiveRule(format!("acl2 prims build failed: {e}")))
}

/// Split a `⊢ C = body` definition into `(C, the equation)`.
fn defined(name: &str, body: Term) -> Result<(Term, Thm)> {
    let eq = Thm::define(name, body)?;
    let c = eq.concl().as_eq().ok_or(Error::NotAnEquation)?.0.clone();
    Ok((c, eq))
}

/// A bytes literal `⌜s⌝`.
fn blob(s: &[u8]) -> Term {
    covalence_hol_eval::mk_blob(Bytes::from(s.to_vec()))
}

/// `⊢ P = ⌜F⌝` from `⊢ ¬P` (the literal-`F` mirror of `ThmExt::eqt_intro`;
/// same shape as `init/nat.rs`). Shared with [`super::term`]'s guard firing.
pub(crate) fn eqf_intro(not_p: Thm) -> Result<Thm> {
    let p = not_p
        .concl()
        .as_app()
        .ok_or_else(|| Error::ConnectiveRule("acl2 eqf_intro: not a ¬".into()))?
        .1
        .clone();
    let pf = fal_to_lit(not_p.not_elim(Thm::assume(p.clone())?)?)?; // {P} ⊢ ⌜F⌝
    let fp = Thm::assume(mk_bool(false))?.false_elim(p)?; // {⌜F⌝} ⊢ P
    pf.deduct_antisym(fp)?.sym()
}

/// `λh:A λt:A λbh:β λbt:β. v` — the constant `acons` step.
fn konst4(a: &Type, beta: &Type, v: &Term) -> Term {
    Term::abs(
        a.clone(),
        Term::abs(
            a.clone(),
            Term::abs(beta.clone(), Term::abs(beta.clone(), v.clone())),
        ),
    )
}

/// `λl:P. coprod_case cf cg l` — a payload-dispatching atom step.
fn case_sa(beta: &Type, cf: &Term, cg: &Term) -> Result<Term> {
    let l = Term::free("__l", acl2_payload());
    let body = coprod_case(Type::int(), Type::bytes(), beta.clone())
        .apply(cf.clone())?
        .apply(cg.clone())?
        .apply(l)?;
    Ok(Term::abs(acl2_payload(), subst::close(&body, "__l")))
}

impl Prims {
    fn build() -> Result<Prims> {
        let th = acl2()?;
        let a = th.ty.clone();
        let anil = th.nil.clone();
        let it = Type::int();
        let bt = Type::bytes();

        // t := asym ⌜"T"⌝.
        let (t, t_eq) = defined("acl2.t", th.asym_lit(b"T")?)?;

        // -- the five catamorphisms --
        let mk_cata = |name: &str,
                       beta: &Type,
                       sa: Term,
                       sn: Term,
                       sc_val: &Term,
                       cases: Option<(Term, Term)>|
         -> Result<Cata> {
            let steps = [sa, sn, konst4(&a, beta, sc_val)];
            let (con, def_eq) = defined(name, th.cs.prec(&steps, beta)?)?;
            Ok(Cata {
                con,
                def_eq,
                steps,
                beta: beta.clone(),
                cases,
            })
        };

        let consp_cata = mk_cata(
            "acl2.consp",
            &a,
            Term::abs(acl2_payload(), anil.clone()),
            anil.clone(),
            &t,
            None,
        )?;
        let atomp_cata = mk_cata(
            "acl2.atom",
            &a,
            Term::abs(acl2_payload(), t.clone()),
            t.clone(),
            &anil,
            None,
        )?;
        let symbolp_arms = (
            Term::abs(it.clone(), anil.clone()), // λi. nil
            Term::abs(bt.clone(), t.clone()),    // λs. t
        );
        let symbolp_cata = mk_cata(
            "acl2.symbolp",
            &a,
            case_sa(&a, &symbolp_arms.0, &symbolp_arms.1)?,
            t.clone(),
            &anil,
            Some(symbolp_arms),
        )?;
        let intp_arms = (
            Term::abs(it.clone(), t.clone()),    // λi. t
            Term::abs(bt.clone(), anil.clone()), // λs. nil
        );
        let intp_cata = mk_cata(
            "acl2.integerp",
            &a,
            case_sa(&a, &intp_arms.0, &intp_arms.1)?,
            anil.clone(),
            &anil,
            Some(intp_arms),
        )?;
        let ident_int = {
            let i = Term::free("__iv", it.clone());
            Term::abs(it.clone(), subst::close(&i, "__iv"))
        };
        let intval_arms = (
            ident_int,                           // λi. i
            Term::abs(bt.clone(), mk_int(0i64)), // λs. 0
        );
        let intval_cata = mk_cata(
            "acl2.intval",
            &it,
            case_sa(&it, &intval_arms.0, &intval_arms.1)?,
            mk_int(0i64),
            &mk_int(0i64),
            Some(intval_arms),
        )?;

        // aendp := aatomp.
        let (endp, endp_eq) = defined("acl2.endp", atomp_cata.con.clone())?;

        // aequal := λx y. cond A (x = y) t nil.
        let (equal, equal_eq) = {
            let x = Term::free("__x", a.clone());
            let y = Term::free("__y", a.clone());
            let body = cond(a.clone())
                .apply(x.clone().equals(y.clone())?)?
                .apply(t.clone())?
                .apply(anil.clone())?;
            let l_y = Term::abs(a.clone(), subst::close(&body, "__y"));
            defined(
                "acl2.equal",
                Term::abs(a.clone(), subst::close(&l_y, "__x")),
            )?
        };

        // aif := λc y z. cond A (c = anil) z y.
        let (aif, aif_eq) = {
            let c = Term::free("__c", a.clone());
            let y = Term::free("__y", a.clone());
            let z = Term::free("__z", a.clone());
            let body = cond(a.clone())
                .apply(c.clone().equals(anil.clone())?)?
                .apply(z.clone())?
                .apply(y.clone())?;
            let l_z = Term::abs(a.clone(), subst::close(&body, "__z"));
            let l_y = Term::abs(a.clone(), subst::close(&l_z, "__y"));
            defined("acl2.if", Term::abs(a.clone(), subst::close(&l_y, "__c")))?
        };

        // The arithmetic layer through the intval seam.
        let iv = |x: &Term| intval_cata.con.clone().apply(x.clone());
        let mk_arith2 = |name: &str, op: Term| -> Result<(Term, Thm)> {
            let x = Term::free("__x", a.clone());
            let y = Term::free("__y", a.clone());
            let body = th.aint_at(&op.apply(iv(&x)?)?.apply(iv(&y)?)?)?;
            let l_y = Term::abs(a.clone(), subst::close(&body, "__y"));
            defined(name, Term::abs(a.clone(), subst::close(&l_y, "__x")))
        };
        let (plus, plus_eq) = mk_arith2("acl2.binary-plus", int::int_add())?;
        let (times, times_eq) = mk_arith2("acl2.binary-times", int::int_mul())?;
        let (neg, neg_eq) = {
            let x = Term::free("__x", a.clone());
            let body = th.aint_at(&int::int_neg().apply(iv(&x)?)?)?;
            defined(
                "acl2.unary-neg",
                Term::abs(a.clone(), subst::close(&body, "__x")),
            )?
        };
        let (minus, minus_eq) = {
            let x = Term::free("__x", a.clone());
            let y = Term::free("__y", a.clone());
            let body = plus
                .clone()
                .apply(x.clone())?
                .apply(neg.clone().apply(y.clone())?)?;
            let l_y = Term::abs(a.clone(), subst::close(&body, "__y"));
            defined(
                "acl2.binary-minus",
                Term::abs(a.clone(), subst::close(&l_y, "__x")),
            )?
        };
        // alt := λx y. cond A (intLt (intval x) (intval y)) t nil.
        let (lt, _lt_eq) = {
            let x = Term::free("__x", a.clone());
            let y = Term::free("__y", a.clone());
            let body = cond(a.clone())
                .apply(int::int_lt().apply(iv(&x)?)?.apply(iv(&y)?)?)?
                .apply(t.clone())?
                .apply(anil.clone())?;
            let l_y = Term::abs(a.clone(), subst::close(&body, "__y"));
            defined("acl2.lt", Term::abs(a.clone(), subst::close(&l_y, "__x")))?
        };
        // ale := λx y. aif (alt y x) anil t  (the `(<= x y)` macro shape).
        let (le, _le_eq) = {
            let x = Term::free("__x", a.clone());
            let y = Term::free("__y", a.clone());
            let body = aif
                .clone()
                .apply(lt.clone().apply(y.clone())?.apply(x.clone())?)?
                .apply(anil.clone())?
                .apply(t.clone())?;
            let l_y = Term::abs(a.clone(), subst::close(&body, "__y"));
            defined("acl2.le", Term::abs(a.clone(), subst::close(&l_y, "__x")))?
        };

        Ok(Prims {
            th,
            t,
            t_eq,
            consp: consp_cata.con.clone(),
            atomp: atomp_cata.con.clone(),
            endp,
            endp_eq,
            symbolp: symbolp_cata.con.clone(),
            intp: intp_cata.con.clone(),
            intval: intval_cata.con.clone(),
            equal,
            equal_eq,
            aif,
            aif_eq,
            plus,
            plus_eq,
            times,
            times_eq,
            neg,
            neg_eq,
            minus,
            minus_eq,
            lt,
            le,
            consp_cata,
            atomp_cata,
            symbolp_cata,
            intp_cata,
            intval_cata,
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

    /// `⊢ t = asym ⌜"T"⌝` — the defining equation of ACL2 true.
    pub fn t_def(&self) -> Thm {
        self.t_eq.clone()
    }

    /// `⊢ aendp = aatomp` — the defining equation of `endp`.
    pub fn endp_def(&self) -> Thm {
        self.endp_eq.clone()
    }

    /// The primitive table (design §8): 11 rows. `IF`/`QUOTE` are special
    /// forms; `ATOM`, `ENDP`, `<=`, binary `-` are defun/macro layers.
    pub fn table(&self) -> Vec<PrimRow> {
        let r = |sym: &'static str, arity: usize, model: &Term| PrimRow {
            sym: smol_str::SmolStr::new_static(sym),
            arity,
            model: model.clone(),
        };
        vec![
            r("CAR", 1, &self.th.car),
            r("CDR", 1, &self.th.cdr),
            r("CONS", 2, &self.th.cons),
            r("CONSP", 1, &self.consp),
            r("INTEGERP", 1, &self.intp),
            r("SYMBOLP", 1, &self.symbolp),
            r("EQUAL", 2, &self.equal),
            r("BINARY-+", 2, &self.plus),
            r("BINARY-*", 2, &self.times),
            r("UNARY--", 1, &self.neg),
            r("<", 2, &self.lt),
        ]
    }

    // ------------------------------------------------------------------
    // Catamorphism computation laws (private plumbing)
    // ------------------------------------------------------------------

    /// `⊢ C (aatom b) = <atom-step at b, reduced>`.
    fn cata_atom(&self, c: &Cata, b: &Term) -> Result<Thm> {
        let atom_b = self.th.atom.clone().apply(b.clone())?;
        let e = c.def_eq.clone().cong_fn(atom_b)?;
        let comp = self
            .th
            .cs
            .prec_eq(&c.steps, 0, &c.beta)?
            .all_elim(b.clone())?;
        e.trans(comp)?.reduce_rhs()
    }

    /// `⊢ C anil = <nil step>`.
    fn cata_nil(&self, c: &Cata) -> Result<Thm> {
        let e = c.def_eq.clone().cong_fn(self.th.nil.clone())?;
        e.trans(self.th.cs.prec_eq(&c.steps, 1, &c.beta)?)
    }

    /// `⊢ C (acons h t) = <cons step, reduced>` (the step drops the raw
    /// arguments and recursor images, so `reduce_rhs` erases them).
    fn cata_cons(&self, c: &Cata, h: &Term, t: &Term) -> Result<Thm> {
        let ht = self.th.cons.clone().apply(h.clone())?.apply(t.clone())?;
        let e = c.def_eq.clone().cong_fn(ht)?;
        let comp = self
            .th
            .cs
            .prec_eq(&c.steps, 2, &c.beta)?
            .all_elim(h.clone())?
            .all_elim(t.clone())?;
        e.trans(comp)?.reduce_rhs()
    }

    /// `⊢ C (aint v) = <cf v, reduced>` / `⊢ C (asym v) = <cg v, reduced>` —
    /// payload dispatch through `case_inl`/`case_inr`.
    fn cata_payload(&self, c: &Cata, is_int: bool, v: &Term) -> Result<Thm> {
        let (cf, cg) = c
            .cases
            .as_ref()
            .ok_or_else(|| Error::ConnectiveRule("acl2 cata_payload: no payload arms".into()))?;
        let (it, bt) = (Type::int(), Type::bytes());
        let (unfold, wrapped) = if is_int {
            (
                self.th.int_unfold(v)?,
                inl(it.clone(), bt.clone()).apply(v.clone())?,
            )
        } else {
            (
                self.th.sym_unfold(v)?,
                inr(it.clone(), bt.clone()).apply(v.clone())?,
            )
        };
        let e1 = unfold.cong_arg(c.con.clone())?; // C (K v) = C (aatom (wrap v))
        let e2 = self.cata_atom(c, &wrapped)?; // … = coprod_case cf cg (wrap v)
        let e3 = if is_int {
            case_inl(&it, &bt, &c.beta, cf, cg, v)?
        } else {
            case_inr(&it, &bt, &c.beta, cf, cg, v)?
        };
        e1.trans(e2)?.trans(e3)?.reduce_rhs()
    }

    // ------------------------------------------------------------------
    // car/cdr: computation + ACL2 completion axioms (proved)
    // ------------------------------------------------------------------

    fn proj_cons(&self, take_cdr: bool) -> Result<Thm> {
        let (h, t) = (self.avar("h"), self.avar("t"));
        self.th
            .cs
            .proj_scons(take_cdr, &h, &t)?
            .all_intro("t", self.a())?
            .all_intro("h", self.a())
    }

    /// `⊢ ∀h t. car (acons h t) = h`.
    pub fn car_cons(&self) -> Result<Thm> {
        self.proj_cons(false)
    }

    /// `⊢ ∀h t. cdr (acons h t) = t`.
    pub fn cdr_cons(&self) -> Result<Thm> {
        self.proj_cons(true)
    }

    fn proj_atom(&self, take_cdr: bool) -> Result<Thm> {
        let b = Term::free("b", acl2_payload());
        self.th
            .cs
            .proj_leaf(take_cdr, LeafKind::Atom(&b))?
            .all_intro("b", acl2_payload())
    }

    /// `⊢ ∀b. car (aatom b) = anil` — the car completion axiom at atoms.
    pub fn car_atom(&self) -> Result<Thm> {
        self.proj_atom(false)
    }

    /// `⊢ ∀b. cdr (aatom b) = anil`.
    pub fn cdr_atom(&self) -> Result<Thm> {
        self.proj_atom(true)
    }

    /// `⊢ car anil = anil` — the car completion axiom at nil.
    pub fn car_nil(&self) -> Result<Thm> {
        self.th.cs.proj_leaf(false, LeafKind::Nil)
    }

    /// `⊢ cdr anil = anil`.
    pub fn cdr_nil(&self) -> Result<Thm> {
        self.th.cs.proj_leaf(true, LeafKind::Nil)
    }

    fn proj_payload(&self, take_cdr: bool, is_int: bool) -> Result<Thm> {
        let (name, ty) = if is_int {
            ("i", Type::int())
        } else {
            ("s", Type::bytes())
        };
        let v = Term::free(name, ty.clone());
        let (unfold, wrapped) = if is_int {
            (
                self.th.int_unfold(&v)?,
                inl(Type::int(), Type::bytes()).apply(v.clone())?,
            )
        } else {
            (
                self.th.sym_unfold(&v)?,
                inr(Type::int(), Type::bytes()).apply(v.clone())?,
            )
        };
        let proj = if take_cdr {
            self.th.cdr.clone()
        } else {
            self.th.car.clone()
        };
        unfold
            .cong_arg(proj)? // proj (K v) = proj (aatom (wrap v))
            .trans(self.th.cs.proj_leaf(take_cdr, LeafKind::Atom(&wrapped))?)?
            .all_intro(name, ty)
    }

    /// `⊢ ∀i. car (aint i) = anil` (a completion-axiom instance).
    pub fn car_int(&self) -> Result<Thm> {
        self.proj_payload(false, true)
    }

    /// `⊢ ∀i. cdr (aint i) = anil`.
    pub fn cdr_int(&self) -> Result<Thm> {
        self.proj_payload(true, true)
    }

    /// `⊢ ∀s. car (asym s) = anil`.
    pub fn car_sym(&self) -> Result<Thm> {
        self.proj_payload(false, false)
    }

    /// `⊢ ∀s. cdr (asym s) = anil`.
    pub fn cdr_sym(&self) -> Result<Thm> {
        self.proj_payload(true, false)
    }

    // ------------------------------------------------------------------
    // Recognizers
    // ------------------------------------------------------------------

    /// `⊢ ∀h t. aconsp (acons h t) = t`.
    pub fn consp_cons(&self) -> Result<Thm> {
        let (h, t) = (self.avar("h"), self.avar("t"));
        self.cata_cons(&self.consp_cata, &h, &t)?
            .all_intro("t", self.a())?
            .all_intro("h", self.a())
    }

    /// `⊢ ∀b. aconsp (aatom b) = anil`.
    pub fn consp_atom(&self) -> Result<Thm> {
        let b = Term::free("b", acl2_payload());
        self.cata_atom(&self.consp_cata, &b)?
            .all_intro("b", acl2_payload())
    }

    /// `⊢ aconsp anil = anil`.
    pub fn consp_nil(&self) -> Result<Thm> {
        self.cata_nil(&self.consp_cata)
    }

    /// `⊢ ∀h t. aatomp (acons h t) = anil`.
    pub fn atomp_cons(&self) -> Result<Thm> {
        let (h, t) = (self.avar("h"), self.avar("t"));
        self.cata_cons(&self.atomp_cata, &h, &t)?
            .all_intro("t", self.a())?
            .all_intro("h", self.a())
    }

    /// `⊢ ∀b. aatomp (aatom b) = t`.
    pub fn atomp_atom(&self) -> Result<Thm> {
        let b = Term::free("b", acl2_payload());
        self.cata_atom(&self.atomp_cata, &b)?
            .all_intro("b", acl2_payload())
    }

    /// `⊢ aatomp anil = t`.
    pub fn atomp_nil(&self) -> Result<Thm> {
        self.cata_nil(&self.atomp_cata)
    }

    /// `⊢ ∀h t. aendp (acons h t) = anil`.
    pub fn endp_cons(&self) -> Result<Thm> {
        let (h, t) = (self.avar("h"), self.avar("t"));
        let ht = self.th.cons.clone().apply(h)?.apply(t)?;
        let (h, t) = (self.avar("h"), self.avar("t"));
        self.endp_eq
            .clone()
            .cong_fn(ht)?
            .trans(self.cata_cons(&self.atomp_cata, &h, &t)?)?
            .all_intro("t", self.a())?
            .all_intro("h", self.a())
    }

    /// `⊢ aendp anil = t`.
    pub fn endp_nil(&self) -> Result<Thm> {
        self.endp_eq
            .clone()
            .cong_fn(self.th.nil.clone())?
            .trans(self.cata_nil(&self.atomp_cata)?)
    }

    /// `⊢ ∀s. asymbolp (asym s) = t`.
    pub fn symbolp_sym(&self) -> Result<Thm> {
        let s = Term::free("s", Type::bytes());
        self.cata_payload(&self.symbolp_cata, false, &s)?
            .all_intro("s", Type::bytes())
    }

    /// `⊢ asymbolp anil = t` — nil IS a symbol in ACL2.
    pub fn symbolp_nil(&self) -> Result<Thm> {
        self.cata_nil(&self.symbolp_cata)
    }

    /// `⊢ ∀i. asymbolp (aint i) = anil`.
    pub fn symbolp_int(&self) -> Result<Thm> {
        let i = Term::free("i", Type::int());
        self.cata_payload(&self.symbolp_cata, true, &i)?
            .all_intro("i", Type::int())
    }

    /// `⊢ ∀h t. asymbolp (acons h t) = anil`.
    pub fn symbolp_cons(&self) -> Result<Thm> {
        let (h, t) = (self.avar("h"), self.avar("t"));
        self.cata_cons(&self.symbolp_cata, &h, &t)?
            .all_intro("t", self.a())?
            .all_intro("h", self.a())
    }

    /// `⊢ ∀i. aintp (aint i) = t`.
    pub fn intp_int(&self) -> Result<Thm> {
        let i = Term::free("i", Type::int());
        self.cata_payload(&self.intp_cata, true, &i)?
            .all_intro("i", Type::int())
    }

    /// `⊢ ∀s. aintp (asym s) = anil`.
    pub fn intp_sym(&self) -> Result<Thm> {
        let s = Term::free("s", Type::bytes());
        self.cata_payload(&self.intp_cata, false, &s)?
            .all_intro("s", Type::bytes())
    }

    /// `⊢ aintp anil = anil`.
    pub fn intp_nil(&self) -> Result<Thm> {
        self.cata_nil(&self.intp_cata)
    }

    /// `⊢ ∀h t. aintp (acons h t) = anil`.
    pub fn intp_cons(&self) -> Result<Thm> {
        let (h, t) = (self.avar("h"), self.avar("t"));
        self.cata_cons(&self.intp_cata, &h, &t)?
            .all_intro("t", self.a())?
            .all_intro("h", self.a())
    }

    // ------------------------------------------------------------------
    // Equality (total on A × A) + the boolean carrier facts
    // ------------------------------------------------------------------

    /// `⊢ ¬(t = anil)` — the two ACL2 booleans are distinct (constructor
    /// distinctness through the `t` definition).
    pub fn t_ne_nil(&self) -> Result<Thm> {
        let s = blob(b"T");
        let inr_s = inr(Type::int(), Type::bytes()).apply(s.clone())?;
        let hyp = self.t.clone().equals(self.th.nil.clone())?;
        // {t = anil} ⊢ aatom (inr ⌜T⌝) = anil.
        let chain = self
            .th
            .sym_unfold(&s)?
            .sym()? // aatom (inr T) = asym T
            .trans(self.t_eq.clone().sym()?)? // = t
            .trans(Thm::assume(hyp.clone())?)?; // = anil
        let f = self
            .th
            .distinct(0, 1, std::slice::from_ref(&inr_s), &[])?
            .imp_elim(chain)?; // {t = anil} ⊢ F
        f.imp_intro(&hyp)?.not_intro()
    }

    /// `⊢ ∀x. aequal x x = t`.
    pub fn equal_refl(&self) -> Result<Thm> {
        let x = self.avar("x");
        let g = Thm::refl(x.clone())?.eqt_intro()?; // (x = x) = ⌜T⌝
        apply_def(&self.equal_eq, &[x.clone(), x])?
            .rhs_conv(|tm| tm.rw_all(&g))?
            .rhs_conv(collapse_conds)?
            .all_intro("x", self.a())
    }

    /// `⊢ ∀x y. ¬(x = y) ⟹ (aequal x y = anil)`.
    pub fn equal_ne(&self) -> Result<Thm> {
        let (x, y) = (self.avar("x"), self.avar("y"));
        self.equal_ne_under(&x, &y)?
            .all_intro("y", self.a())?
            .all_intro("x", self.a())
    }

    /// `⊢ ¬(x = y) ⟹ (aequal x y = anil)` at fixed `x`, `y`.
    fn equal_ne_under(&self, x: &Term, y: &Term) -> Result<Thm> {
        let ne = x.clone().equals(y.clone())?.not()?;
        let g = eqf_intro(Thm::assume(ne.clone())?)?; // {ne} ⊢ (x = y) = ⌜F⌝
        apply_def(&self.equal_eq, &[x.clone(), y.clone()])?
            .rhs_conv(|tm| tm.rw_all(&g))?
            .rhs_conv(collapse_conds)? // {ne} ⊢ aequal x y = anil
            .imp_intro(&ne)
    }

    /// `⊢ ∀x y. ¬(aequal x y = anil) ⟹ x = y` — a non-`nil` `aequal`
    /// answer certifies genuine HOL equality (totality, the other way).
    pub fn equal_holds(&self) -> Result<Thm> {
        let (x, y) = (self.avar("x"), self.avar("y"));
        let p = x.clone().equals(y.clone())?;
        let np = p.clone().not()?;
        let h = self
            .equal
            .clone()
            .apply(x.clone())?
            .apply(y.clone())?
            .equals(self.th.nil.clone())?
            .not()?; // ¬(aequal x y = anil)
        // p-branch: ⊢ p ⟹ p.
        let left = Thm::assume(p.clone())?.imp_intro(&p)?;
        // ¬p-branch: aequal x y = anil contradicts h.
        let en = self
            .equal_ne_under(&x, &y)?
            .imp_elim(Thm::assume(np.clone())?)?; // {¬p} ⊢ aequal x y = anil
        let right = Thm::assume(h.clone())?
            .not_elim(en)? // {¬p, h} ⊢ F
            .false_elim(p.clone())?
            .imp_intro(&np)?; // {h} ⊢ ¬p ⟹ p
        Thm::lem(p)?
            .or_elim(left, right)? // {h} ⊢ x = y
            .imp_intro(&h)?
            .all_intro("y", self.a())?
            .all_intro("x", self.a())
    }

    /// `⊢ ¬(aint ⌜i⌝ = aint ⌜j⌝)` for **distinct integer literals** —
    /// contrapose the carrier's `int_inj` against `reduce`'s literal
    /// disequality (the `aint` mirror of `Acl2::sym_ne`). Errors if the
    /// literals are equal.
    pub fn int_ne(&self, i: i128, j: i128) -> Result<Thm> {
        let (b1, b2) = (mk_int(i), mk_int(j));
        let ne = b1.clone().equals(b2.clone())?.reduce()?;
        match ne.concl().as_eq().and_then(|(_, r)| r.as_bool()) {
            Some(false) => {}
            _ => {
                return Err(Error::ConnectiveRule(format!(
                    "acl2 int_ne: literals did not reduce to distinct ({ne})"
                )));
            }
        }
        let eq = self.th.aint_at(&b1)?.equals(self.th.aint_at(&b2)?)?;
        let inner = self
            .th
            .int_inj(&b1, &b2)?
            .imp_elim(Thm::assume(eq.clone())?)?; // {eq} ⊢ ⌜i⌝ = ⌜j⌝
        let f = fal_from_lit(ne.eq_mp(inner)?)?; // {eq} ⊢ F
        f.imp_intro(&eq)?.not_intro()
    }

    // ------------------------------------------------------------------
    // if
    // ------------------------------------------------------------------

    /// `⊢ ∀y z. aif anil y z = z`.
    pub fn if_nil(&self) -> Result<Thm> {
        let (y, z) = (self.avar("y"), self.avar("z"));
        let g = Thm::refl(self.th.nil.clone())?.eqt_intro()?; // (anil = anil) = ⌜T⌝
        apply_def(&self.aif_eq, &[self.th.nil.clone(), y, z])?
            .rhs_conv(|tm| tm.rw_all(&g))?
            .rhs_conv(collapse_conds)?
            .all_intro("z", self.a())?
            .all_intro("y", self.a())
    }

    /// `⊢ ∀c y z. ¬(c = anil) ⟹ (aif c y z = y)`.
    pub fn if_t(&self) -> Result<Thm> {
        let (c, y, z) = (self.avar("c"), self.avar("y"), self.avar("z"));
        let ne = c.clone().equals(self.th.nil.clone())?.not()?;
        let g = eqf_intro(Thm::assume(ne.clone())?)?; // {ne} ⊢ (c = anil) = ⌜F⌝
        apply_def(&self.aif_eq, &[c, y, z])?
            .rhs_conv(|tm| tm.rw_all(&g))?
            .rhs_conv(collapse_conds)? // {ne} ⊢ aif c y z = y
            .imp_intro(&ne)?
            .all_intro("z", self.a())?
            .all_intro("y", self.a())?
            .all_intro("c", self.a())
    }

    // ------------------------------------------------------------------
    // Arithmetic: the intval seam + completion + lifted axioms
    // ------------------------------------------------------------------

    /// `⊢ intval (aint z) = z` at a fixed `int` term `z` (THE lifting law,
    /// unquantified form).
    fn intval_int_at(&self, z: &Term) -> Result<Thm> {
        self.cata_payload(&self.intval_cata, true, z)
    }

    /// `⊢ ∀i. intval (aint i) = i` — THE lifting law: every `init/int.rs`
    /// ring/order theorem transports through it.
    pub fn intval_int(&self) -> Result<Thm> {
        let i = Term::free("i", Type::int());
        self.intval_int_at(&i)?.all_intro("i", Type::int())
    }

    /// `⊢ ∀s. intval (asym s) = 0` — arithmetic completion: non-numbers
    /// read as `0`.
    pub fn intval_sym(&self) -> Result<Thm> {
        let s = Term::free("s", Type::bytes());
        self.cata_payload(&self.intval_cata, false, &s)?
            .all_intro("s", Type::bytes())
    }

    /// `⊢ intval anil = 0`.
    pub fn intval_nil(&self) -> Result<Thm> {
        self.cata_nil(&self.intval_cata)
    }

    /// `⊢ ∀h t. intval (acons h t) = 0`.
    pub fn intval_cons(&self) -> Result<Thm> {
        let (h, t) = (self.avar("h"), self.avar("t"));
        self.cata_cons(&self.intval_cata, &h, &t)?
            .all_intro("t", self.a())?
            .all_intro("h", self.a())
    }

    fn iv(&self, x: &Term) -> Result<Term> {
        self.intval.clone().apply(x.clone())
    }

    /// `⊢ intval (aplus x y) = intAdd (intval x) (intval y)` at fixed terms.
    fn intval_plus_at(&self, x: &Term, y: &Term) -> Result<Thm> {
        let z = int::int_add().apply(self.iv(x)?)?.apply(self.iv(y)?)?;
        apply_def(&self.plus_eq, &[x.clone(), y.clone()])? // aplus x y = aint z
            .cong_arg(self.intval.clone())? // intval (aplus x y) = intval (aint z)
            .trans(self.intval_int_at(&z)?)
    }

    /// `⊢ ∀x y. intval (aplus x y) = intAdd (intval x) (intval y)`.
    pub fn intval_plus(&self) -> Result<Thm> {
        let (x, y) = (self.avar("x"), self.avar("y"));
        self.intval_plus_at(&x, &y)?
            .all_intro("y", self.a())?
            .all_intro("x", self.a())
    }

    /// `⊢ ∀x y. intval (atimes x y) = intMul (intval x) (intval y)`.
    pub fn intval_times(&self) -> Result<Thm> {
        let (x, y) = (self.avar("x"), self.avar("y"));
        let z = int::int_mul().apply(self.iv(&x)?)?.apply(self.iv(&y)?)?;
        apply_def(&self.times_eq, &[x, y])?
            .cong_arg(self.intval.clone())?
            .trans(self.intval_int_at(&z)?)?
            .all_intro("y", self.a())?
            .all_intro("x", self.a())
    }

    /// `⊢ intval (aneg x) = intNeg (intval x)` at a fixed term.
    fn intval_neg_at(&self, x: &Term) -> Result<Thm> {
        let z = int::int_neg().apply(self.iv(x)?)?;
        apply_def(&self.neg_eq, std::slice::from_ref(x))?
            .cong_arg(self.intval.clone())?
            .trans(self.intval_int_at(&z)?)
    }

    /// `⊢ ∀x. intval (aneg x) = intNeg (intval x)`.
    pub fn intval_neg(&self) -> Result<Thm> {
        let x = self.avar("x");
        self.intval_neg_at(&x)?.all_intro("x", self.a())
    }

    /// `⊢ ∀x y. intval (aminus x y) = intSub (intval x) (intval y)` —
    /// through `init/int.rs`'s proved `sub_def`.
    pub fn intval_minus(&self) -> Result<Thm> {
        let (x, y) = (self.avar("x"), self.avar("y"));
        let neg_y = self.neg.clone().apply(y.clone())?;
        let c = apply_def(&self.minus_eq, &[x.clone(), y.clone()])? // aminus x y = aplus x (aneg y)
            .cong_arg(self.intval.clone())?
            .trans(self.intval_plus_at(&x, &neg_y)?)? // = intAdd (iv x) (iv (aneg y))
            .rhs_conv(|tm| tm.rw_all(&self.intval_neg_at(&y)?))?; // = intAdd (iv x) (intNeg (iv y))
        let sub = int::sub_def()
            .all_elim(self.iv(&x)?)?
            .all_elim(self.iv(&y)?)?; // intSub a b = intAdd a (intNeg b)
        c.trans(sub.sym()?)?
            .all_intro("y", self.a())?
            .all_intro("x", self.a())
    }

    /// `⊢ ∀x y. aplus x y = aplus y x` — ACL2's `+`-commutativity axiom,
    /// **lifted** from the proved `init/int.rs` ring.
    pub fn plus_comm(&self) -> Result<Thm> {
        let (x, y) = (self.avar("x"), self.avar("y"));
        let d1 = apply_def(&self.plus_eq, &[x.clone(), y.clone()])?;
        let d2 = apply_def(&self.plus_eq, &[y.clone(), x.clone()])?;
        let comm = int::add_comm()
            .all_elim(self.iv(&x)?)?
            .all_elim(self.iv(&y)?)?; // intAdd a b = intAdd b a
        d1.trans(comm.cong_arg(self.th.aint.clone())?)?
            .trans(d2.sym()?)?
            .all_intro("y", self.a())?
            .all_intro("x", self.a())
    }

    /// `⊢ ∀x y z. aplus (aplus x y) z = aplus x (aplus y z)` — lifted
    /// `+`-associativity.
    pub fn plus_assoc(&self) -> Result<Thm> {
        let (x, y, z) = (self.avar("x"), self.avar("y"), self.avar("z"));
        let (a, b, c) = (self.iv(&x)?, self.iv(&y)?, self.iv(&z)?);
        let xy = self.plus.clone().apply(x.clone())?.apply(y.clone())?;
        let yz = self.plus.clone().apply(y.clone())?.apply(z.clone())?;
        // aplus (aplus x y) z = aint (intAdd (intAdd a b) c).
        let lhs = apply_def(&self.plus_eq, &[xy, z.clone()])?
            .rhs_conv(|tm| tm.rw_all(&self.intval_plus_at(&x, &y)?))?;
        // aplus x (aplus y z) = aint (intAdd a (intAdd b c)).
        let rhs = apply_def(&self.plus_eq, &[x.clone(), yz])?
            .rhs_conv(|tm| tm.rw_all(&self.intval_plus_at(&y, &z)?))?;
        let assoc = int::add_assoc().all_elim(a)?.all_elim(b)?.all_elim(c)?; // (a+b)+c = a+(b+c)
        lhs.trans(assoc.cong_arg(self.th.aint.clone())?)?
            .trans(rhs.sym()?)?
            .all_intro("z", self.a())?
            .all_intro("y", self.a())?
            .all_intro("x", self.a())
    }

    /// `⊢ aplus (aint ⌜i⌝) (aint ⌜j⌝) = aint ⌜i+j⌝` — ground arithmetic
    /// by literal folding (the performance seam: literals fold, the
    /// numerals are never unfolded).
    pub fn plus_lit(&self, i: i128, j: i128) -> Result<Thm> {
        let (li, lj) = (mk_int(i), mk_int(j));
        let (ai, aj) = (self.th.aint_at(&li)?, self.th.aint_at(&lj)?);
        apply_def(&self.plus_eq, &[ai, aj])? // = aint (intAdd (intval (aint i)) (intval (aint j)))
            .rhs_conv(|tm| tm.rw_all(&self.intval_int_at(&li)?))?
            .rhs_conv(|tm| tm.rw_all(&self.intval_int_at(&lj)?))? // = aint (intAdd ⌜i⌝ ⌜j⌝)
            .reduce_rhs() // = aint ⌜i+j⌝
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn p() -> &'static Prims {
        prims().unwrap()
    }

    fn a() -> Type {
        p().th.ty.clone()
    }

    fn avar(n: &str) -> Term {
        Term::free(n, a())
    }

    fn acons(h: &Term, t: &Term) -> Term {
        p().th
            .cons
            .clone()
            .apply(h.clone())
            .unwrap()
            .apply(t.clone())
            .unwrap()
    }

    fn ap1(f: &Term, x: &Term) -> Term {
        f.clone().apply(x.clone()).unwrap()
    }

    fn ap2(f: &Term, x: &Term, y: &Term) -> Term {
        f.clone()
            .apply(x.clone())
            .unwrap()
            .apply(y.clone())
            .unwrap()
    }

    /// `⊢ ∀h t. <lhs h t> = <rhs h t>` expected-statement builder.
    fn q_ht(body: Term) -> Term {
        body.forall("t", a()).unwrap().forall("h", a()).unwrap()
    }

    /// Assert a closed theorem with an exact conclusion.
    fn check(thm: &Thm, expected: &Term) {
        assert!(thm.hyps().is_empty(), "must be closed: {thm}");
        assert_eq!(thm.concl(), expected);
    }

    /// The theory builds; constants have the designed types; the table has
    /// the 11 designed rows.
    #[test]
    fn t_prims_build() {
        let pr = p();
        let aa = Type::fun(a(), a());
        let aaa = Type::fun(a(), aa.clone());
        assert_eq!(pr.t.type_of().unwrap(), a());
        for c in [
            &pr.consp,
            &pr.atomp,
            &pr.endp,
            &pr.symbolp,
            &pr.intp,
            &pr.neg,
        ] {
            assert_eq!(c.type_of().unwrap(), aa);
        }
        for c in [&pr.equal, &pr.plus, &pr.times, &pr.minus, &pr.lt, &pr.le] {
            assert_eq!(c.type_of().unwrap(), aaa);
        }
        assert_eq!(pr.aif.type_of().unwrap(), Type::fun(a(), aaa.clone()));
        assert_eq!(pr.intval.type_of().unwrap(), Type::fun(a(), Type::int()));
        let table = pr.table();
        assert_eq!(table.len(), 11);
        let arities: Vec<(&str, usize)> = table.iter().map(|r| (r.sym.as_str(), r.arity)).collect();
        assert_eq!(
            arities,
            [
                ("CAR", 1),
                ("CDR", 1),
                ("CONS", 2),
                ("CONSP", 1),
                ("INTEGERP", 1),
                ("SYMBOLP", 1),
                ("EQUAL", 2),
                ("BINARY-+", 2),
                ("BINARY-*", 2),
                ("UNARY--", 1),
                ("<", 2)
            ]
        );
    }

    /// **S1 gate:** car/cdr computation + the ACL2 completion axioms as
    /// closed theorems with exact statements.
    #[test]
    fn t_car_cdr_completion() {
        let pr = p();
        let (h, t) = (avar("h"), avar("t"));
        let nil = pr.th.nil.clone();

        check(
            &pr.car_cons().unwrap(),
            &q_ht(ap1(&pr.th.car, &acons(&h, &t)).equals(h.clone()).unwrap()),
        );
        check(
            &pr.cdr_cons().unwrap(),
            &q_ht(ap1(&pr.th.cdr, &acons(&h, &t)).equals(t.clone()).unwrap()),
        );

        // Completion at atoms: ∀b. car (aatom b) = anil (and cdr).
        let b = Term::free("b", acl2_payload());
        let atom_b = ap1(&pr.th.atom, &b);
        check(
            &pr.car_atom().unwrap(),
            &ap1(&pr.th.car, &atom_b)
                .equals(nil.clone())
                .unwrap()
                .forall("b", acl2_payload())
                .unwrap(),
        );
        check(
            &pr.cdr_atom().unwrap(),
            &ap1(&pr.th.cdr, &atom_b)
                .equals(nil.clone())
                .unwrap()
                .forall("b", acl2_payload())
                .unwrap(),
        );

        // Completion at nil: car anil = anil (and cdr).
        check(
            &pr.car_nil().unwrap(),
            &ap1(&pr.th.car, &nil).equals(nil.clone()).unwrap(),
        );
        check(
            &pr.cdr_nil().unwrap(),
            &ap1(&pr.th.cdr, &nil).equals(nil.clone()).unwrap(),
        );

        // Payload instances: ∀i. car (aint i) = anil, ∀s. car (asym s) = anil.
        let i = Term::free("i", Type::int());
        let s = Term::free("s", Type::bytes());
        let aint_i = pr.th.aint_at(&i).unwrap();
        let asym_s = pr.th.asym_at(&s).unwrap();
        check(
            &pr.car_int().unwrap(),
            &ap1(&pr.th.car, &aint_i)
                .equals(nil.clone())
                .unwrap()
                .forall("i", Type::int())
                .unwrap(),
        );
        check(
            &pr.cdr_int().unwrap(),
            &ap1(&pr.th.cdr, &aint_i)
                .equals(nil.clone())
                .unwrap()
                .forall("i", Type::int())
                .unwrap(),
        );
        check(
            &pr.car_sym().unwrap(),
            &ap1(&pr.th.car, &asym_s)
                .equals(nil.clone())
                .unwrap()
                .forall("s", Type::bytes())
                .unwrap(),
        );
        check(
            &pr.cdr_sym().unwrap(),
            &ap1(&pr.th.cdr, &asym_s)
                .equals(nil.clone())
                .unwrap()
                .forall("s", Type::bytes())
                .unwrap(),
        );
    }

    /// **S1 gate:** the recognizers compute to `t`/`anil` exactly as
    /// designed (including `asymbolp anil = t`).
    #[test]
    fn t_recognizers() {
        let pr = p();
        let (h, t) = (avar("h"), avar("t"));
        let nil = pr.th.nil.clone();
        let b = Term::free("b", acl2_payload());
        let atom_b = ap1(&pr.th.atom, &b);
        let i = Term::free("i", Type::int());
        let s = Term::free("s", Type::bytes());
        let aint_i = pr.th.aint_at(&i).unwrap();
        let asym_s = pr.th.asym_at(&s).unwrap();
        let q_b = |tm: Term| tm.forall("b", acl2_payload()).unwrap();
        let q_i = |tm: Term| tm.forall("i", Type::int()).unwrap();
        let q_s = |tm: Term| tm.forall("s", Type::bytes()).unwrap();

        // consp.
        check(
            &pr.consp_cons().unwrap(),
            &q_ht(ap1(&pr.consp, &acons(&h, &t)).equals(pr.t.clone()).unwrap()),
        );
        check(
            &pr.consp_atom().unwrap(),
            &q_b(ap1(&pr.consp, &atom_b).equals(nil.clone()).unwrap()),
        );
        check(
            &pr.consp_nil().unwrap(),
            &ap1(&pr.consp, &nil).equals(nil.clone()).unwrap(),
        );

        // atom / endp (the complements).
        check(
            &pr.atomp_cons().unwrap(),
            &q_ht(ap1(&pr.atomp, &acons(&h, &t)).equals(nil.clone()).unwrap()),
        );
        check(
            &pr.atomp_atom().unwrap(),
            &q_b(ap1(&pr.atomp, &atom_b).equals(pr.t.clone()).unwrap()),
        );
        check(
            &pr.atomp_nil().unwrap(),
            &ap1(&pr.atomp, &nil).equals(pr.t.clone()).unwrap(),
        );
        check(
            &pr.endp_cons().unwrap(),
            &q_ht(ap1(&pr.endp, &acons(&h, &t)).equals(nil.clone()).unwrap()),
        );
        check(
            &pr.endp_nil().unwrap(),
            &ap1(&pr.endp, &nil).equals(pr.t.clone()).unwrap(),
        );

        // symbolp — note asymbolp anil = t (nil IS a symbol).
        check(
            &pr.symbolp_sym().unwrap(),
            &q_s(ap1(&pr.symbolp, &asym_s).equals(pr.t.clone()).unwrap()),
        );
        check(
            &pr.symbolp_nil().unwrap(),
            &ap1(&pr.symbolp, &nil).equals(pr.t.clone()).unwrap(),
        );
        check(
            &pr.symbolp_int().unwrap(),
            &q_i(ap1(&pr.symbolp, &aint_i).equals(nil.clone()).unwrap()),
        );
        check(
            &pr.symbolp_cons().unwrap(),
            &q_ht(
                ap1(&pr.symbolp, &acons(&h, &t))
                    .equals(nil.clone())
                    .unwrap(),
            ),
        );

        // integerp.
        check(
            &pr.intp_int().unwrap(),
            &q_i(ap1(&pr.intp, &aint_i).equals(pr.t.clone()).unwrap()),
        );
        check(
            &pr.intp_sym().unwrap(),
            &q_s(ap1(&pr.intp, &asym_s).equals(nil.clone()).unwrap()),
        );
        check(
            &pr.intp_nil().unwrap(),
            &ap1(&pr.intp, &nil).equals(nil.clone()).unwrap(),
        );
        check(
            &pr.intp_cons().unwrap(),
            &q_ht(ap1(&pr.intp, &acons(&h, &t)).equals(nil.clone()).unwrap()),
        );
    }

    /// **S1 gate:** `aequal` totality — refl / disequality / converse,
    /// the boolean distinctness, and ground instances both ways (with the
    /// equal-literal negative control).
    #[test]
    fn t_equal() {
        let pr = p();
        let (x, y) = (avar("x"), avar("y"));
        let nil = pr.th.nil.clone();
        let q_xy = |tm: Term| tm.forall("y", a()).unwrap().forall("x", a()).unwrap();

        // ⊢ ¬(t = anil).
        check(
            &pr.t_ne_nil().unwrap(),
            &pr.t.clone().equals(nil.clone()).unwrap().not().unwrap(),
        );

        // ⊢ ∀x. aequal x x = t.
        check(
            &pr.equal_refl().unwrap(),
            &ap2(&pr.equal, &x, &x)
                .equals(pr.t.clone())
                .unwrap()
                .forall("x", a())
                .unwrap(),
        );

        // ⊢ ∀x y. ¬(x = y) ⟹ (aequal x y = anil).
        check(
            &pr.equal_ne().unwrap(),
            &q_xy(
                x.clone()
                    .equals(y.clone())
                    .unwrap()
                    .not()
                    .unwrap()
                    .imp(ap2(&pr.equal, &x, &y).equals(nil.clone()).unwrap())
                    .unwrap(),
            ),
        );

        // ⊢ ∀x y. ¬(aequal x y = anil) ⟹ x = y.
        check(
            &pr.equal_holds().unwrap(),
            &q_xy(
                ap2(&pr.equal, &x, &y)
                    .equals(nil.clone())
                    .unwrap()
                    .not()
                    .unwrap()
                    .imp(x.clone().equals(y.clone()).unwrap())
                    .unwrap(),
            ),
        );

        // Ground positive: ⊢ aequal (asym "X") (asym "X") = t.
        let sx = pr.th.asym_lit(b"X").unwrap();
        let pos = pr.equal_refl().unwrap().all_elim(sx.clone()).unwrap();
        check(
            &pos,
            &ap2(&pr.equal, &sx, &sx).equals(pr.t.clone()).unwrap(),
        );

        // Ground negative: ⊢ aequal (aint 1) (aint 2) = anil via int_ne.
        let a1 = pr.th.aint_at(&mk_int(1i64)).unwrap();
        let a2 = pr.th.aint_at(&mk_int(2i64)).unwrap();
        let neg = pr
            .equal_ne()
            .unwrap()
            .all_elim(a1.clone())
            .unwrap()
            .all_elim(a2.clone())
            .unwrap()
            .imp_elim(pr.int_ne(1, 2).unwrap())
            .unwrap();
        check(&neg, &ap2(&pr.equal, &a1, &a2).equals(nil.clone()).unwrap());

        // Negative control: equal literals must NOT produce a "theorem".
        assert!(pr.int_ne(3, 3).is_err());
    }

    /// **S1 gate:** the strict-`if` semantics, plus a ground composition
    /// (`aif t … = then-branch` through `t_ne_nil`).
    #[test]
    fn t_if() {
        let pr = p();
        let (c, y, z) = (avar("c"), avar("y"), avar("z"));
        let nil = pr.th.nil.clone();

        // ⊢ ∀y z. aif anil y z = z.
        let aif_nil = pr
            .aif
            .clone()
            .apply(nil.clone())
            .unwrap()
            .apply(y.clone())
            .unwrap()
            .apply(z.clone())
            .unwrap();
        check(
            &pr.if_nil().unwrap(),
            &aif_nil
                .equals(z.clone())
                .unwrap()
                .forall("z", a())
                .unwrap()
                .forall("y", a())
                .unwrap(),
        );

        // ⊢ ∀c y z. ¬(c = anil) ⟹ (aif c y z = y).
        let aif_c = pr
            .aif
            .clone()
            .apply(c.clone())
            .unwrap()
            .apply(y.clone())
            .unwrap()
            .apply(z.clone())
            .unwrap();
        check(
            &pr.if_t().unwrap(),
            &c.clone()
                .equals(nil.clone())
                .unwrap()
                .not()
                .unwrap()
                .imp(aif_c.equals(y.clone()).unwrap())
                .unwrap()
                .forall("z", a())
                .unwrap()
                .forall("y", a())
                .unwrap()
                .forall("c", a())
                .unwrap(),
        );

        // Ground: ⊢ aif t (aint 1) (aint 2) = aint 1.
        let a1 = pr.th.aint_at(&mk_int(1i64)).unwrap();
        let a2 = pr.th.aint_at(&mk_int(2i64)).unwrap();
        let ground = pr
            .if_t()
            .unwrap()
            .all_elim(pr.t.clone())
            .unwrap()
            .all_elim(a1.clone())
            .unwrap()
            .all_elim(a2.clone())
            .unwrap()
            .imp_elim(pr.t_ne_nil().unwrap())
            .unwrap();
        let aif_t = pr
            .aif
            .clone()
            .apply(pr.t.clone())
            .unwrap()
            .apply(a1.clone())
            .unwrap()
            .apply(a2)
            .unwrap();
        check(&ground, &aif_t.equals(a1).unwrap());
    }

    /// **S1 gate:** the `intval` seam — the lifting law and the ACL2
    /// arithmetic-completion behaviour (non-numbers read as `0`), plus the
    /// per-op seam laws.
    #[test]
    fn t_intval() {
        let pr = p();
        let zero = mk_int(0i64);
        let (h, t) = (avar("h"), avar("t"));
        let (x, y) = (avar("x"), avar("y"));
        let i = Term::free("i", Type::int());
        let s = Term::free("s", Type::bytes());
        let iv = |tm: &Term| ap1(&pr.intval, tm);
        let q_xy = |tm: Term| tm.forall("y", a()).unwrap().forall("x", a()).unwrap();

        // THE lifting law: ⊢ ∀i. intval (aint i) = i.
        check(
            &pr.intval_int().unwrap(),
            &iv(&pr.th.aint_at(&i).unwrap())
                .equals(i.clone())
                .unwrap()
                .forall("i", Type::int())
                .unwrap(),
        );

        // Completion: symbols, nil, conses all read as 0.
        check(
            &pr.intval_sym().unwrap(),
            &iv(&pr.th.asym_at(&s).unwrap())
                .equals(zero.clone())
                .unwrap()
                .forall("s", Type::bytes())
                .unwrap(),
        );
        check(
            &pr.intval_nil().unwrap(),
            &iv(&pr.th.nil).equals(zero.clone()).unwrap(),
        );
        check(
            &pr.intval_cons().unwrap(),
            &q_ht(iv(&acons(&h, &t)).equals(zero.clone()).unwrap()),
        );

        // Per-op seam laws.
        let add = int::int_add().apply(iv(&x)).unwrap().apply(iv(&y)).unwrap();
        check(
            &pr.intval_plus().unwrap(),
            &q_xy(iv(&ap2(&pr.plus, &x, &y)).equals(add).unwrap()),
        );
        let mul = int::int_mul().apply(iv(&x)).unwrap().apply(iv(&y)).unwrap();
        check(
            &pr.intval_times().unwrap(),
            &q_xy(iv(&ap2(&pr.times, &x, &y)).equals(mul).unwrap()),
        );
        let negx = int::int_neg().apply(iv(&x)).unwrap();
        check(
            &pr.intval_neg().unwrap(),
            &iv(&ap1(&pr.neg, &x))
                .equals(negx)
                .unwrap()
                .forall("x", a())
                .unwrap(),
        );
        let sub = int::int_sub().apply(iv(&x)).unwrap().apply(iv(&y)).unwrap();
        check(
            &pr.intval_minus().unwrap(),
            &q_xy(iv(&ap2(&pr.minus, &x, &y)).equals(sub).unwrap()),
        );
    }

    /// **S1 gate:** the lifted ACL2 arithmetic axioms — `+`-commutativity
    /// and `+`-associativity transported from the proved `init/int.rs` ring.
    #[test]
    fn t_lifted_arithmetic() {
        let pr = p();
        let (x, y, z) = (avar("x"), avar("y"), avar("z"));

        check(
            &pr.plus_comm().unwrap(),
            &ap2(&pr.plus, &x, &y)
                .equals(ap2(&pr.plus, &y, &x))
                .unwrap()
                .forall("y", a())
                .unwrap()
                .forall("x", a())
                .unwrap(),
        );

        check(
            &pr.plus_assoc().unwrap(),
            &ap2(&pr.plus, &ap2(&pr.plus, &x, &y), &z)
                .equals(ap2(&pr.plus, &x, &ap2(&pr.plus, &y, &z)))
                .unwrap()
                .forall("z", a())
                .unwrap()
                .forall("y", a())
                .unwrap()
                .forall("x", a())
                .unwrap(),
        );
    }

    /// **S1 gate (the ground instance):** `⊢ aplus (aint 2) (aint 2) =
    /// aint 4` computed through `intval_int` + literal folding.
    #[test]
    fn t_plus_ground_gate() {
        let pr = p();
        let thm = pr.plus_lit(2, 2).unwrap();
        let a2 = pr.th.aint_at(&mk_int(2i64)).unwrap();
        let a4 = pr.th.aint_at(&mk_int(4i64)).unwrap();
        check(&thm, &ap2(&pr.plus, &a2, &a2).equals(a4).unwrap());
    }
}
