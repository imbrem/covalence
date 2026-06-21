//! The `nat/unary` model's carrier-specific content: the four `Nat`-addition
//! axioms over `list unit` + append, and the `m.induct` handler that realizes
//! abstract `Nat` induction as `list_induct` (with the head fixed to
//! `unit.nil` via `Thm::unit_eq`).
//!
//! This is the genuinely NEW content the second model forces (`nat/self`
//! reuses the existing kernel `nat` theorems wholesale). Everything here is a
//! real, hypothesis- and oracle-free kernel `Thm`; the axiom proofs cross the
//! `unit` singleton exactly where the abstraction predicted.
//!
//! ## The encoding
//!
//! `0 ↦ nil[unit]`, `succ ↦ cons[unit] unit.nil`, `+ ↦ list.cat[unit]`. The
//! four axioms:
//! - `zero.add` (`0 + a = a`)   — `cat_nil`   @ `unit`              (definitional)
//! - `add.zero` (`a + 0 = a`)   — `cat_nil_r` @ `unit`              (a list.cov theorem)
//! - `succ.add` (`S a + b = S(a+b)`) — `cat_cons` @ `unit`, head `unit.nil`
//! - `add.succ` (`a + S b = S(a+b)`) — NEW: induction on `a` + `unit_eq`
//!   (false for general lists; holds for `list unit` because every head is
//!   `unit.nil`).

use std::sync::Arc;

use async_trait::async_trait;
use covalence_core::{Term, Thm, Type, defs, subst};
use covalence_sexp::SExpr;

use crate::init::ext::{TermExt, ThmExt};
use crate::script::tactic::prove_with;
use crate::script::{Hyp, Interp, ScriptError, Tactic};

/// The carrier type `list unit`.
pub(super) fn carrier() -> Type {
    defs::list(Type::unit())
}

/// `unit.nil : unit` — the canonical (and, by `unit_eq`, *only*) inhabitant of
/// `unit`, the head every unary `succ` prepends.
fn u() -> Term {
    defs::unit_nil()
}

/// `nil : list unit` — the unary zero.
pub(super) fn zero() -> Term {
    defs::nil(Type::unit())
}

/// `cons[unit] : unit → list unit → list unit` — `succ` is `cons unit.nil`.
fn cons_op() -> Term {
    defs::cons(Type::unit())
}

/// `succ : list unit → list unit` ≡ `cons unit.nil` (the unary successor).
pub(super) fn succ_op() -> Term {
    // η-long would need a binder; the abstract proof only ever applies it, so
    // the partially-applied `cons unit.nil` is the right unapplied operator.
    Term::app(cons_op(), u())
}

/// `succ t = cons unit.nil t`.
fn succ(t: Term) -> Term {
    Term::app(succ_op(), t)
}

/// `cat[unit] : list unit → list unit → list unit` — the unary addition.
pub(super) fn add_op() -> Term {
    defs::list_cat(Type::unit())
}

/// `cat a b`.
fn cat(a: Term, b: Term) -> Term {
    Term::app(Term::app(add_op(), a), b)
}

// ============================================================================
// The four axioms.
// ============================================================================

/// `⊢ ∀a. cat nil a = a` — the left unit (`0 + a = a`), `cat_nil` at `unit`.
pub(super) fn zero_add() -> Result<Thm, covalence_core::Error> {
    Ok(crate::init::list::cov::cat_nil_cov().inst_tfree("a", Type::unit())?)
}

/// `⊢ ∀a. cat a nil = a` — the right unit (`a + 0 = a`), `cat_nil_r` at `unit`.
pub(super) fn add_zero() -> Result<Thm, covalence_core::Error> {
    Ok(crate::init::list::cov::cat_nil_r_cov().inst_tfree("a", Type::unit())?)
}

/// `⊢ ∀a b. cat (succ a) b = succ (cat a b)` — `S a + b = S(a + b)`.
/// Directly `cat_cons` at `unit` with head `unit.nil` (`succ = cons unit.nil`):
/// `cat (cons unit.nil a) b = cons unit.nil (cat a b)`.
pub(super) fn succ_add() -> Result<Thm, covalence_core::Error> {
    let a = Term::free("a", carrier());
    let b = Term::free("b", carrier());
    // cat_cons @ unit @ unit.nil @ a @ b : cat (cons u a) b = cons u (cat a b).
    let cc = crate::init::list::cov::cat_cons_cov()
        .inst_tfree("a", Type::unit())?
        .all_elim(u())?
        .all_elim(a.clone())?
        .all_elim(b.clone())?;
    // `cons u a = succ a` and `cons u (cat a b) = succ (cat a b)` definitionally
    // (succ ≡ cons unit.nil), so this IS the `succ.add` shape already.
    cc.all_intro("b", carrier())?
        .all_intro("a", carrier())
        .map_err(Into::into)
}

/// `⊢ ∀a b. cat a (succ b) = succ (cat a b)` — `a + S b = S(a + b)`.
///
/// The NEW axiom: false for general lists, true for `list unit`. By
/// `list_induct` on `a`, with `unit_eq` collapsing the head in the cons case.
pub(super) fn add_succ() -> Result<Thm, covalence_core::Error> {
    let alpha = Type::unit();
    let la = carrier();

    // Motive  P a ≔ ∀b. cat a (succ b) = succ (cat a b).
    let a = Term::free("a", la.clone());
    let body_at = |t: &Term| -> Result<Term, covalence_core::Error> {
        let bb = Term::free("b", la.clone());
        let eq = cat(t.clone(), succ(bb.clone())).equals(succ(cat(t.clone(), bb.clone())))?;
        Ok(eq.forall("b", la.clone())?)
    };
    let p = Term::abs(la.clone(), subst::close(&body_at(&a)?, "a"));

    // base: P nil ≔ ∀b. cat nil (succ b) = succ (cat nil b).
    let nil = zero();
    let base = {
        let b = Term::free("b", la.clone());
        // cat nil (succ b) = succ b           (cat_nil @ (succ b))
        let l = zero_add()?.all_elim(succ(b.clone()))?;
        // succ (cat nil b) = succ b           (cat_nil @ b, under succ)
        let r = zero_add()?.all_elim(b.clone())?.cong_arg(succ_op())?;
        // ⊢ cat nil (succ b) = succ (cat nil b)
        let eq = l.trans(r.sym()?)?.all_intro("b", la.clone())?;
        // bridge to applied motive `(λa.P) nil`.
        beta_expand(&p, nil.clone(), eq)?
    };

    // cons case: ⊢ ∀x xs. (λa.P) xs ⟹ (λa.P)(cons x xs).
    let cons_case = {
        let x = Term::free("x", alpha.clone());
        let xs = Term::free("xs", la.clone());
        let b = Term::free("b", la.clone());

        // IH (applied form, β-reduced): P xs ≔ ∀b. cat xs (succ b) = succ (cat xs b).
        let ih_body = body_at(&xs)?;
        let ih = Thm::assume(ih_body.clone())?;

        // Goal body at `cons x xs`: ∀b. cat (cons x xs)(succ b) = succ (cat (cons x xs) b).
        // First the `x = unit.nil` collapse: cons x = cons unit.nil (= succ_op).
        let x_eq_u = Thm::unit_eq(x.clone(), u())?; // ⊢ x = unit.nil
        // cons x xs = cons unit.nil xs (cong on `λx. cons x xs`).
        let consx_eq = Thm::refl(cons_op())?
            .mk_comb(x_eq_u.clone())?
            .mk_comb(Thm::refl(xs.clone())?)?; // ⊢ cons x xs = cons u xs

        // Prove the body at `cons u xs` first, then rewrite to `cons x xs`.
        // cat (cons u xs)(succ b)
        //   = cons u (cat xs (succ b))     (cat_cons @ u @ xs @ (succ b))
        //   = cons u (succ (cat xs b))     (IH @ b, under cons u)
        // succ (cat (cons u xs) b)
        //   = succ (cons u (cat xs b))     (cat_cons @ u @ xs @ b, under succ)
        //   = cons u (cons u (cat xs b))   (succ ≡ cons u, definitional)
        // and cons u (succ (cat xs b)) = cons u (cons u (cat xs b)) likewise.
        let cat_cons_u = |p: Term, q: Term| -> Result<Thm, covalence_core::Error> {
            // cat (cons u p) q = cons u (cat p q).
            Ok(crate::init::list::cov::cat_cons_cov()
                .inst_tfree("a", Type::unit())?
                .all_elim(u())?
                .all_elim(p)?
                .all_elim(q)?)
        };
        // LHS chain.
        let l1 = cat_cons_u(xs.clone(), succ(b.clone()))?; // cat (cons u xs)(succ b) = cons u (cat xs (succ b))
        let ih_b = ih.clone().all_elim(b.clone())?; // cat xs (succ b) = succ (cat xs b)
        let l2 = ih_b.cong_arg(succ_op())?; // cons u (cat xs (succ b)) = cons u (succ (cat xs b))
        let lhs = l1.trans(l2)?; // cat (cons u xs)(succ b) = cons u (succ (cat xs b))
        // RHS chain.
        let r1 = cat_cons_u(xs.clone(), b.clone())?.cong_arg(succ_op())?; // succ (cat (cons u xs) b) = succ (cons u (cat xs b))
        // succ (cons u t) ≡ cons u (cons u t) and cons u (succ t) ≡ cons u (cons u t)
        // are the SAME term (succ_op = cons u), so refl bridges.
        let rhs = r1; // succ (cat (cons u xs) b) = cons u (cons u (cat xs b)) ≡ cons u (succ (cat xs b))
        let eq_at_u = lhs.trans(rhs.sym()?)?; // {P xs} ⊢ cat (cons u xs)(succ b) = succ (cat (cons u xs) b)
        let eq_at_u = eq_at_u.all_intro("b", la.clone())?; // {P xs} ⊢ P (cons u xs) (body form)

        // Rewrite `cons u xs ↦ cons x xs` everywhere via `consx_eq` (reversed):
        // motive holds at `cons x xs`.
        let body_consx = body_at(&Term::app(Term::app(cons_op(), x.clone()), xs.clone()))?;
        // (λa.P)(cons x xs) — build by congruence: refl-rewrite cons x xs = cons u xs.
        let p_consx = beta_expand_eq(&p, &consx_eq, eq_at_u)?; // {P xs} ⊢ (λa.P)(cons x xs)
        let _ = body_consx;

        // (λa.P) xs ⟹ (λa.P)(cons x xs), then ∀-close.
        let ante = Term::app(p.clone(), xs.clone());
        let pl_xs_eq = Thm::beta_conv(ante.clone())?; // (λa.P) xs = P xs (body)
        // discharge the IH from the applied antecedent.
        let p_consx = p_consx.imp_intro(&ih_body)?; // ⊢ P xs ⟹ (λa.P)(cons x xs)
        let p_consx = pl_xs_eq.sym()?.mk_comb_imp(&p_consx)?; // ⊢ (λa.P) xs ⟹ (λa.P)(cons x xs)
        p_consx
            .all_intro("xs", la.clone())?
            .all_intro("x", alpha.clone())?
    };

    let ind = crate::init::list::list_induct(&alpha, &p, base, cons_case)?; // ⊢ ∀a. (λa.P) a
    // β-normalise the applied-motive body back to `∀a. ∀b. …`.
    let nf = crate::proofs::rewrite::beta_nf(ind.concl().clone());
    Ok(nf.eq_mp(ind)?)
}

// ============================================================================
// Small congruence helpers (over the kernel rules).
// ============================================================================

/// From `⊢ motive arg = body'` … actually: given a motive `λx. M` and a proof
/// `⊢ body[arg]` (the β-reduced motive body at `arg`), return `⊢ motive arg`
/// (the un-reduced applied form). Mirrors `init::eq::beta_expand`.
fn beta_expand(motive: &Term, arg: Term, body: Thm) -> Result<Thm, covalence_core::Error> {
    let applied = Term::app(motive.clone(), arg);
    let beta = Thm::beta_conv(applied)?; // ⊢ (λx.M) arg = body
    Ok(beta.sym()?.eq_mp(body)?)
}

/// Given `arg_eq : ⊢ s = t`, a `motive = λx.M`, and `proof : ⊢ motive t`
/// (applied form), return `⊢ motive s` (applied form): rewrite the argument
/// backwards through `arg_eq`. Here `proof` is supplied as `⊢ body[t]` (the
/// β-reduced form `P (cons u xs)`), and we want `⊢ motive (cons x xs)`.
fn beta_expand_eq(
    motive: &Term,
    arg_eq: &Thm,
    proof_body: Thm,
) -> Result<Thm, covalence_core::Error> {
    // arg_eq : ⊢ (cons x xs) = (cons u xs).  proof_body : ⊢ body[cons u xs].
    let (lhs, rhs) = arg_eq
        .concl()
        .as_eq()
        .ok_or(covalence_core::Error::NotAnEquation)?;
    // motive lhs = motive rhs (congruence).
    let cong = Thm::refl(motive.clone())?.mk_comb(arg_eq.clone())?; // ⊢ motive lhs = motive rhs
    // proof_body is body[rhs]; lift to applied `motive rhs`, then rewrite BACK
    // to `motive lhs` (cong reversed: motive rhs = motive lhs).
    let p_rhs = beta_expand(motive, rhs.clone(), proof_body)?; // ⊢ motive rhs
    let _ = lhs;
    cong.sym()?.eq_mp(p_rhs).map_err(Into::into) // ⊢ motive lhs
}

/// `⊢ a ⟹ c` from `eq : ⊢ a = a'` and `imp : ⊢ a' ⟹ c` — rewrite an
/// implication's antecedent backwards. Used to convert the β-reduced
/// antecedent `P xs` into the applied `(λa.P) xs`.
trait MkCombImp {
    fn mk_comb_imp(self, imp: &Thm) -> Result<Thm, covalence_core::Error>;
}
impl MkCombImp for Thm {
    fn mk_comb_imp(self, imp: &Thm) -> Result<Thm, covalence_core::Error> {
        // self : ⊢ a = a'.  imp : ⊢ a' ⟹ c.  Want ⊢ a ⟹ c.
        let cong = Thm::refl(defs::imp())?.mk_comb(self)?; // ⊢ (a ⟹) = (a' ⟹) … partial
        // cong : ⊢ imp a = imp a' (as functions `_ ⟹`); apply to the conseq.
        let (_, conseq) = imp
            .concl()
            .as_app()
            .ok_or(covalence_core::Error::NotAnEquation)?;
        let full = cong.mk_comb(Thm::refl(conseq.clone())?)?; // ⊢ (a ⟹ c) = (a' ⟹ c)
        full.eq_mp(imp.clone()).map_err(Into::into)
    }
}

// ============================================================================
// The induction handler.
// ============================================================================

/// `(m.induct VAR BASE STEP)` for the `nat/unary` model: realize abstract
/// `Nat` induction as `list_induct` over `list unit`, with the head fixed to
/// `unit.nil` (so the step's successor is `succ VAR = cons unit.nil VAR`).
///
/// `BASE` proves `P m.zero` (= `P nil`); `STEP` proves `P (m.succ VAR)`
/// (= `P (cons unit.nil VAR)`) under the IH `P VAR`. The surface is identical
/// to the `nat/self` `m.induct`; only this realization differs — the
/// model-dispatched handler.
pub(super) struct UnaryInduct;

#[async_trait]
impl Tactic for UnaryInduct {
    async fn apply(
        &self,
        s: &[SExpr],
        rest: &[SExpr],
        it: &mut Interp,
    ) -> Result<Thm, ScriptError> {
        crate::script::syntax::arity(s, 4, "m.induct")?;
        expect_done(rest)?;
        let env = it.env().clone();
        let var = crate::script::syntax::sym(&s[1], "m.induct variable")?.to_string();

        let alpha = Type::unit();
        let la = carrier();
        let (ty, body) = dest_forall(it.goal()).ok_or_else(|| {
            ScriptError::Syntax(format!("m.induct: goal is not a `∀`: {}", it.goal()))
        })?;
        if ty != la {
            return Err(ScriptError::Syntax(format!(
                "m.induct (nat/unary): goal quantifies over {ty}, not list unit"
            )));
        }
        let p = Term::abs(la.clone(), body.clone()); // motive λl. body

        // base: prove body[nil], bridge to `(λl.body) nil`.
        let nil = zero();
        let base_body =
            prove_with(&subst::open(&body, &nil), &s[2], it.scope_mut(), &[], &env).await?;
        let pl_nil = Thm::beta_conv(Term::app(p.clone(), nil.clone()))?
            .sym()?
            .eq_mp(base_body)?; // ⊢ (λl.body) nil

        // step: under `VAR : list unit`, IH `body[VAR]`, prove `body[succ VAR]`
        // (= `body[cons unit.nil VAR]`).
        let v = Term::free(var.as_str(), la.clone());
        let ih = subst::open(&body, &v);
        let sv = succ(v.clone()); // cons unit.nil VAR
        let step_hyps = vec![(ih.clone(), Hyp::Assumed)];
        it.scope_mut().open();
        it.scope_mut().define(var.clone(), la.clone());
        let step_body = prove_with(
            &subst::open(&body, &sv),
            &s[3],
            it.scope_mut(),
            &step_hyps,
            &env,
        )
        .await;
        it.scope_mut().close();
        let step_body = step_body?; // {body[VAR]} ⊢ body[cons unit.nil VAR]

        // `list_induct`'s cons case is over an ARBITRARY head `x : unit`. Use
        // `unit_eq` to collapse `cons x VAR = cons unit.nil VAR = succ VAR`, so
        // the step we proved at the fixed head transfers to the generic one.
        let x = Term::free("x", alpha.clone());
        let consed = Term::app(Term::app(cons_op(), x.clone()), v.clone()); // cons x VAR
        let x_eq_u = Thm::unit_eq(x.clone(), u())?; // ⊢ x = unit.nil
        let consx_eq = Thm::refl(cons_op())?
            .mk_comb(x_eq_u)?
            .mk_comb(Thm::refl(v.clone())?)?; // ⊢ cons x VAR = succ VAR  (cons unit.nil VAR)

        // body[cons x VAR] = body[succ VAR], so lift `step_body` (at succ VAR =
        // cons unit.nil VAR) BACK to `cons x VAR` (reverse the equation).
        let body_eq = body_subst_cong(&body, &var, &la, &consx_eq)?; // ⊢ body[cons x VAR] = body[succ VAR]
        let step_consx = body_eq.sym()?.eq_mp(step_body)?; // {body[VAR]} ⊢ body[cons x VAR]

        // Bridge both sides to applied-motive form for `list_induct`, ∀-close.
        let ea = Thm::beta_conv(Term::app(p.clone(), v.clone()))?; // (λl.body) VAR = body[VAR]
        let eb = Thm::beta_conv(Term::app(p.clone(), consed.clone()))?; // (λl.body)(cons x VAR) = body[cons x VAR]
        let step_imp = step_consx.imp_intro(&ih)?; // ⊢ body[VAR] ⟹ body[cons x VAR]
        let cons_case = Thm::refl(defs::imp())?
            .mk_comb(ea.sym()?)?
            .mk_comb(eb.sym()?)?
            .eq_mp(step_imp)? // ⊢ (λl.body) VAR ⟹ (λl.body)(cons x VAR)
            .all_intro(var.as_str(), la.clone())?
            .all_intro("x", alpha.clone())?; // ⊢ ∀x VAR. …

        let ind = crate::init::list::list_induct(&alpha, &p, pl_nil, cons_case)
            .map_err(ScriptError::Kernel)?; // ⊢ ∀l. (λl.body) l
        let nf = crate::proofs::rewrite::beta_nf(ind.concl().clone());
        Ok(nf.eq_mp(ind)?)
    }
}

/// `⊢ body[s'] = body[s]` from `arg_eq : ⊢ s' = s`, with `body` the open
/// induction body (locally-nameless, `var` the induction variable bound at de
/// Bruijn 0) and `la` its type: build `(λvar.body) s' = (λvar.body) s` by
/// congruence and β-reduce both sides.
fn body_subst_cong(
    body: &Term,
    _var: &str,
    la: &Type,
    arg_eq: &Thm,
) -> Result<Thm, covalence_core::Error> {
    // `body` is already a locally-nameless body under the goal's `∀var` binder,
    // so `λvar.body` is `Term::abs(la, body)`.
    let motive = Term::abs(la.clone(), body.clone());
    let cong = Thm::refl(motive.clone())?.mk_comb(arg_eq.clone())?; // (λvar.body) s' = (λvar.body) s
    let (l, r) = cong
        .concl()
        .as_eq()
        .ok_or(covalence_core::Error::NotAnEquation)?;
    let bl = Thm::beta_conv(l.clone())?; // (λvar.body) s' = body[s']
    let br = Thm::beta_conv(r.clone())?; // (λvar.body) s  = body[s]
    bl.sym()?.trans(cong)?.trans(br).map_err(Into::into) // body[s'] = body[s]
}

/// The unary model's induction handler as a registry object.
pub(super) fn induct_tactic() -> Arc<dyn Tactic> {
    Arc::new(UnaryInduct)
}

/// A **prelude env** for the declarative `#model nat/unary` / `#models …
/// (from unary)` path: the interpretation terms (as consts `unary.zero` /
/// `unary.succ` / `unary.add`), the induction handler (`unary.induct`), and the
/// four `Nat`-addition axioms proved at `list unit` (under their theory names
/// `zero.add` / `add.zero` / `succ.add` / `add.succ`). A `.cov` script `#open`s
/// this to *declare* `nat/unary` from data and certify it `(from unary)`,
/// keeping `unary.rs`'s heavy Rust proofs in place (not ported to `.cov`).
pub fn prelude() -> Result<crate::script::Env, covalence_core::Error> {
    use crate::script::{ConstDef, Env};
    let mut e = Env::empty();
    e.define_const("unary.zero", ConstDef::Op(zero()));
    e.define_const("unary.succ", ConstDef::Op(succ_op()));
    e.define_const("unary.add", ConstDef::Op(add_op()));
    e.register_tactic("unary.induct", induct_tactic());
    e.define_lemma("zero.add", zero_add()?);
    e.define_lemma("add.zero", add_zero()?);
    e.define_lemma("succ.add", succ_add()?);
    e.define_lemma("add.succ", add_succ()?);
    Ok(e)
}

// ============================================================================
// Helpers shared with the script tactic layer.
// ============================================================================

fn expect_done(rest: &[SExpr]) -> Result<(), ScriptError> {
    if rest.is_empty() {
        Ok(())
    } else {
        Err(ScriptError::Syntax(
            "m.induct: the goal is closed, but more tactics follow".into(),
        ))
    }
}

fn dest_forall(t: &Term) -> Option<(Type, Term)> {
    let covalence_core::TermKind::App(h, abs) = t.kind() else {
        return None;
    };
    let covalence_core::TermKind::Abs(ty, body) = abs.kind() else {
        return None;
    };
    (*h == defs::forall(ty.clone())).then(|| (ty.clone(), body.clone()))
}
