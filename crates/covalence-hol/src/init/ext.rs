//! Untrusted convenience extension traits over the kernel's [`Term`]
//! and [`Thm`].
//!
//! These are the **insulation layer**. Proof code in `covalence-hol`
//! should reach for these high-level methods instead of raw
//! `covalence-core` constructors, so that when the kernel's surface
//! shifts we re-point the trait impls here rather than rewriting every
//! call site. Nothing here can widen the TCB — every method bottoms
//! out in a `covalence-core` constructor or rule.
//!
//! ## Result-by-default
//!
//! Every method that can fail returns [`Result`] — the intended
//! workflow is `term.and(q)?` / `thm.eqt_intro()?`, threading errors
//! with `?`. We deliberately avoid panicking convenience wrappers:
//! they encourage swallowing genuine logical failures. The one place
//! that panics is the `init` / lazy-static proofs themselves, which
//! `expect` on these `Result`s because a failure there is a build-time
//! bug, not a runtime condition.
//!
//! ## The kernel rules are the primitives — call them directly
//!
//! The kernel already exposes the full HOL-Light rule set on [`Thm`]
//! as `Result`-returning constructors. **Treat these as the
//! primitives and call them directly** (with `?`); `ThmExt` does not
//! re-wrap them:
//!
//! - equality: [`Thm::refl`], [`Thm::sym`], [`Thm::trans`],
//!   [`Thm::cong_app`], [`Thm::cong_abs`], [`Thm::beta_conv`],
//!   [`Thm::eta_conv`];
//! - logical framework: [`Thm::assume`], [`Thm::eq_mp`],
//!   [`Thm::deduct_antisym`], [`Thm::imp_intro`], [`Thm::imp_elim`],
//!   [`Thm::all_intro`], [`Thm::all_elim`];
//! - connectives: [`Thm::and_intro`], [`Thm::and_elim_l`],
//!   [`Thm::and_elim_r`], [`Thm::or_intro_l`], [`Thm::or_intro_r`],
//!   [`Thm::or_elim`], [`Thm::not_intro`], [`Thm::not_elim`];
//! - substitution / structural: [`Thm::inst`], [`Thm::inst_tfree`],
//!   [`Thm::weaken`], [`Thm::false_elim`], [`Thm::nat_induct`];
//! - reduction: [`Thm::reduce_prim`], [`Thm::unfold_term_spec`].
//!
//! `ThmExt` only adds derived steps the kernel doesn't ship: the two
//! congruence specialisations, the `p ⟺ (p = T)` bridge, conjunction
//! splitting, whole-conclusion rewriting / δ-unfolding, one-sided
//! conversion of an equation, and reduction.
//!
//! ## Reduction is weak — we don't reduce under binders
//!
//! The δ / ι / β *reduction* conversions here
//! ([`TermExt::delta_all`], [`reduce_consts`](TermExt::reduce_consts),
//! [`reduce`](TermExt::reduce)) are **weak**: they walk the
//! application spine and its arguments but stop at every `λ`, never
//! opening a binder. This keeps evaluation predictable and matches the
//! HOL discipline of stripping binders explicitly
//! ([`Thm::all_intro`] / [`Thm::all_elim`]) before working on a body.
//! The strong (under-binder) β-normaliser
//! [`beta_nf`](crate::init::eq::beta_nf) is the deliberate exception,
//! kept for the connective derivations.
//!
//! *Rewriting* with a supplied equation
//! ([`rw_all`](TermExt::rw_all)) is **not** reduction — it replaces a
//! named subterm rather than evaluating — so it *does* traverse under
//! binders, capture-avoiding with a fresh witness.

use covalence_core::defs::Symbol;
use covalence_core::{Error, Result, Term, Thm, Type, subst};

use crate::HolLightCtx;

/// Untrusted term builders and the rewriting conversion on [`Term`].
///
/// The builders validate their result — every method returns
/// [`Err`](Result) rather than producing an ill-typed term — so a
/// successful return is always a well-typed term.
pub trait TermExt: Sized {
    /// Application `self arg`. Errors if the application is ill-typed.
    fn apply(self, arg: Term) -> Result<Term>;

    /// HOL equality `self = rhs : bool`. Errors unless `self` and
    /// `rhs` share a type.
    fn equals(self, rhs: Term) -> Result<Term>;

    /// HOL implication `self ⟹ q`. Errors unless both are `bool`.
    fn imp(self, q: Term) -> Result<Term>;

    /// HOL conjunction `self ∧ q`. Errors unless both are `bool`.
    fn and(self, q: Term) -> Result<Term>;

    /// HOL disjunction `self ∨ q`. Errors unless both are `bool`.
    fn or(self, q: Term) -> Result<Term>;

    /// HOL negation `¬ self`. Errors unless `self` is `bool`.
    fn not(self) -> Result<Term>;

    /// HOL biconditional `self ⟺ q`. Errors unless both are `bool`.
    fn iff(self, q: Term) -> Result<Term>;

    /// HOL universal `∀name:ty. self`, closing free occurrences of
    /// `Free(name, ty)` in `self`. Errors unless `self` is `bool`.
    fn forall(self, name: &str, ty: Type) -> Result<Term>;

    /// HOL existential `∃name:ty. self`, closing free occurrences of
    /// `Free(name, ty)` in `self`. Errors unless `self` is `bool`.
    fn exists(self, name: &str, ty: Type) -> Result<Term>;

    /// Build `⊢ self = self'`, where `self'` is `self` with **every**
    /// occurrence of `eq`'s LHS replaced by its RHS, given
    /// `eq : ⊢ a = b`. See the trait method docs for the conversion's
    /// spec. Unlike the builders above this returns a [`Thm`], not a
    /// `Term` — it is a proof step, not term construction.
    fn rw_all(&self, eq: &Thm) -> Result<Thm>;

    /// δ-reduction of a single definition: if `self` is a let-style
    /// defined-constant `Spec` leaf (e.g. `nat.add`, `∧`), return its
    /// defining equation `⊢ self = body`.
    ///
    /// Thin Result wrapper over [`Thm::unfold_term_spec`] — errors if
    /// `self` is not a `Spec` leaf, or is a def-style (Hilbert-ε
    /// selector) / declaration-only spec with no let-body. It unfolds
    /// the constant *itself*; to fold the body into surrounding
    /// arguments, follow with a β step ([`Thm::beta_conv`] /
    /// [`beta_nf`](crate::init::eq::beta_nf)).
    fn delta(&self) -> Result<Thm>;

    /// δ-reduction of a particular symbol: build `⊢ self = self'`,
    /// unfolding every occurrence in `self`'s **spine** of a defined
    /// constant whose [`Symbol`] matches `symbol` (compared by
    /// [`label`](Symbol::label)) to its definition body. Non-matching
    /// leaves and the surrounding application structure are preserved
    /// by congruence.
    ///
    /// **Weak — does not descend under λ** (see the [module docs](self)
    /// on binders). An occurrence of `symbol` that sits inside an
    /// abstraction body is left untouched; strip the binder first
    /// ([`Thm::all_intro`] / [`Thm::all_elim`]) if you need it.
    ///
    /// Each matching leaf is unfolded once by its own
    /// [`Thm::unfold_term_spec`] equation (so different type-arg
    /// instantiations of the same polymorphic constant each unfold
    /// correctly). It does **not** recurse into the substituted bodies,
    /// so unfolding `imp` — whose body mentions `∧` — leaves those
    /// `∧`s in place; call `delta_all` again with the next symbol.
    /// Errors if a matching leaf is not let-style unfoldable. Result is
    /// always hypothesis-free.
    fn delta_all(&self, symbol: &dyn Symbol) -> Result<Thm>;

    /// **Constant folding** — build `⊢ self = self'`, evaluating every
    /// closed primitive application in `self`'s spine via
    /// [`Thm::reduce_prim`] (`nat`/`int`/`bytes`/`bool` arithmetic,
    /// `succ`/`pred`, literal `=`), innermost-first and repeatedly.
    ///
    /// **Weak — does not descend under λ.** This is ι/prim reduction
    /// only: no β, no δ. It folds closed primitive applications in
    /// argument position — `(λx. x) (2 + 3)` becomes `(λx. x) 5` (the
    /// argument is evaluated; the β-redex is *not* fired) — but leaves
    /// anything inside a λ body untouched, so `λx. (2 + 3)` is returned
    /// unchanged.
    fn reduce_consts(&self) -> Result<Thm>;

    /// **βι reduction** — build `⊢ self = self'`, combining β
    /// ([`Thm::beta_conv`]) and constant folding
    /// ([`Thm::reduce_prim`]) to weak-normal form: fire spine redexes
    /// and evaluate closed primitive applications, innermost-first and
    /// repeatedly.
    ///
    /// **Weak — does not descend under λ.** It reduces the spine and
    /// the arguments but never opens a binder, so `(λx. x + 1)` is
    /// irreducible while `(λx. x + 1) 4` evaluates to `5`. For δ, fold
    /// definitions in first with [`delta_all`](TermExt::delta_all); for
    /// reduction under binders use the strong normaliser
    /// [`beta_nf`](crate::init::eq::beta_nf).
    fn reduce(&self) -> Result<Thm>;

    /// Prove `⊢ self` by evaluation: [`reduce`](TermExt::reduce) `self`
    /// to weak-normal form and, if it lands on the `T` literal,
    /// conclude `⊢ self` (via the `p = T ⟹ p` bridge). Errors if `self`
    /// does not reduce to `T`. The workhorse for closed decidable goals
    /// (`⊢ 2 + 2 = 4`, `⊢ ¬(0 = 1)` after folding `¬`, …).
    fn prove_true(&self) -> Result<Thm>;
}

/// Validate a freshly built term, returning it only if well-typed.
fn checked(t: Term) -> Result<Term> {
    t.type_of()?;
    Ok(t)
}

impl TermExt for Term {
    fn apply(self, arg: Term) -> Result<Term> {
        checked(Term::app(self, arg))
    }

    fn equals(self, rhs: Term) -> Result<Term> {
        // `mk_eq` checks `self` is well-typed; `checked` then catches a
        // `rhs` whose type differs from `self`'s.
        checked(HolLightCtx::new().mk_eq(self, rhs)?)
    }

    fn imp(self, q: Term) -> Result<Term> {
        checked(HolLightCtx::new().mk_imp(self, q))
    }

    fn and(self, q: Term) -> Result<Term> {
        checked(HolLightCtx::new().mk_and(self, q))
    }

    fn or(self, q: Term) -> Result<Term> {
        checked(HolLightCtx::new().mk_or(self, q))
    }

    fn not(self) -> Result<Term> {
        checked(HolLightCtx::new().mk_not(self))
    }

    fn iff(self, q: Term) -> Result<Term> {
        checked(HolLightCtx::new().mk_iff(self, q))
    }

    fn forall(self, name: &str, ty: Type) -> Result<Term> {
        checked(HolLightCtx::new().mk_forall(name, ty, self))
    }

    fn exists(self, name: &str, ty: Type) -> Result<Term> {
        checked(HolLightCtx::new().mk_exists(name, ty, self))
    }

    fn rw_all(&self, eq: &Thm) -> Result<Thm> {
        let (lhs, _rhs) = eq.concl().as_eq().ok_or(Error::NotAnEquation)?;
        match rw_all_opt(self, lhs, eq)? {
            Some(thm) => Ok(thm),
            None => Thm::refl(self.clone()),
        }
    }

    fn delta(&self) -> Result<Thm> {
        Thm::unfold_term_spec(self.clone())
    }

    fn delta_all(&self, symbol: &dyn Symbol) -> Result<Thm> {
        delta_all_conv(self, symbol)
    }

    fn reduce_consts(&self) -> Result<Thm> {
        reduce_conv(self, false)
    }

    fn reduce(&self) -> Result<Thm> {
        reduce_conv(self, true)
    }

    fn prove_true(&self) -> Result<Thm> {
        let conv = self.reduce()?; // ⊢ self = v
        let v = conv.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
        if v.as_bool() == Some(true) {
            // conv : ⊢ self = T ; the bridge gives ⊢ self.
            conv.eqt_elim()
        } else {
            Err(Error::ConnectiveRule(format!(
                "prove_true: reduced to `{v}`, not `T`"
            )))
        }
    }
}

/// `⊢ t = t'` replacing every occurrence of `lhs` (the LHS of `eq`)
/// with `eq`'s RHS — a congruence-closure conversion. Returns `None`
/// when `lhs` does not occur in `t` (so `t` is unchanged), and `Some(eq')`
/// otherwise — the **sharing-preserving** form.
///
/// This `None` short-circuit is the whole performance story: descending
/// every node and building `refl(f).cong_app(refl(x))` (a no-op `⊢ f x =
/// f x`) for untouched subtrees costs one `Thm` allocation *per node*,
/// per rewrite. By returning `None` for an unchanged subtree we allocate
/// congruence proofs only along the spine from the root to the actual
/// rewrite sites, and never enter the (expensive) `Abs` open/re-abstract
/// path for a binder whose body `lhs` doesn't touch.
///
/// Descends through `App` (congruence on both sides) and under `Abs`
/// (open with a fresh variable, rewrite, re-abstract), bottoming out at a
/// node equal to `lhs` (return `eq` itself). `lhs` is treated as a closed
/// pattern: the fresh variable under each binder avoids the free
/// variables of the body and of `eq`, so a closed rewrite never captures.
/// Rewriting with an `lhs` that mentions a bound variable is out of scope.
fn rw_all_opt(t: &Term, lhs: &Term, eq: &Thm) -> Result<Option<Thm>> {
    if t == lhs {
        return Ok(Some(eq.clone()));
    }
    if let Some((f, x)) = t.as_app() {
        let f_eq = rw_all_opt(f, lhs, eq)?;
        let x_eq = rw_all_opt(x, lhs, eq)?;
        if f_eq.is_none() && x_eq.is_none() {
            return Ok(None); // neither side changed — reuse `t`
        }
        let f_eq = match f_eq {
            Some(e) => e,
            None => Thm::refl(f.clone())?,
        };
        let x_eq = match x_eq {
            Some(e) => e,
            None => Thm::refl(x.clone())?,
        };
        return f_eq.cong_app(x_eq).map(Some);
    }
    if let Some((ty, body)) = t.as_abs() {
        // The witness must avoid the body's frees and `eq`'s frees so
        // the re-abstraction can't capture (and `Thm::abs`'s side
        // condition holds).
        let fresh = fresh_for(|n| {
            subst::has_free_var(body, n)
                || subst::has_free_var(eq.concl(), n)
                || eq.hyps().iter().any(|h| subst::has_free_var(h, n))
        });
        let wit = Term::free(fresh.as_str(), ty.clone());
        let opened = subst::open(body, &wit);
        return match rw_all_opt(&opened, lhs, eq)? {
            None => Ok(None), // body unchanged — reuse `t`
            Some(body_eq) => body_eq.abs(fresh.as_str(), ty.clone()).map(Some),
        };
    }
    Ok(None)
}

/// `⊢ t = t'` δ-unfolding every spine occurrence of a `symbol`-named
/// defined constant in `t`. **Weak — stops at `Abs`.** See
/// [`TermExt::delta_all`] for the spec.
fn delta_all_conv(t: &Term, symbol: &dyn Symbol) -> Result<Thm> {
    // A matching `Spec` leaf — unfold it to its defining body. We do
    // not recurse into the result, so the symbol is removed exactly
    // once per original occurrence.
    if let Some((spec, _args)) = t.as_spec()
        && spec.symbol().label() == symbol.label()
    {
        return Thm::unfold_term_spec(t.clone());
    }
    // Descend the application spine, but never under a binder.
    if let Some((f, x)) = t.as_app() {
        let f_eq = delta_all_conv(f, symbol)?;
        let x_eq = delta_all_conv(x, symbol)?;
        return f_eq.cong_app(x_eq);
    }
    Thm::refl(t.clone())
}

/// `⊢ t = t'` weak-reducing `t`: descend the application spine (args
/// innermost-first), then fire a redex at the current node — β
/// ([`Thm::beta_conv`]) when `with_beta` and the head is a λ, else ι
/// ([`Thm::reduce_prim`]) on a closed primitive application — and keep
/// reducing the result. **Never descends under `Abs`.**
fn reduce_conv(t: &Term, with_beta: bool) -> Result<Thm> {
    let Some((f, x)) = t.as_app() else {
        // Leaf or abstraction: irreducible at this layer.
        return Thm::refl(t.clone());
    };
    let f_eq = reduce_conv(f, with_beta)?;
    let x_eq = reduce_conv(x, with_beta)?;
    let cong = f_eq.cong_app(x_eq)?; // ⊢ t = f' x'
    let fx = cong
        .concl()
        .as_eq()
        .expect("cong yields an equation")
        .1
        .clone();

    // β: if the reduced head is a λ, contract and keep reducing.
    if with_beta
        && let Some((head, _)) = fx.as_app()
        && head.as_abs().is_some()
    {
        let beta = Thm::beta_conv(fx.clone())?; // ⊢ f' x' = body[x'/0]
        let body = beta
            .concl()
            .as_eq()
            .expect("beta yields an equation")
            .1
            .clone();
        let body_eq = reduce_conv(&body, with_beta)?;
        return cong.trans(beta)?.trans(body_eq);
    }

    // ι: evaluate a closed primitive application. `reduce_prim` returns
    // a canonical literal (terminal), so no further pass is needed.
    match Thm::reduce_prim(fx) {
        Ok(step) => cong.trans(step),
        Err(_) => Ok(cong),
    }
}

/// Smallest `_rw{i}` name for which `occurs` is `false`.
fn fresh_for(occurs: impl Fn(&str) -> bool) -> String {
    let mut i = 0usize;
    loop {
        let name = format!("_rw{i}");
        if !occurs(&name) {
            return name;
        }
        i += 1;
    }
}

/// Untrusted derived proof steps on [`Thm`]. See the [module
/// docs](self) — the kernel rules are the primitives; this trait only
/// adds what they don't ship.
pub trait ThmExt: Sized {
    /// `⊢ f = g` → `⊢ f a = g a`, for a fixed argument `a`
    /// (congruence with a reflexive argument side).
    fn cong_fn(self, arg: Term) -> Result<Thm>;

    /// `⊢ x = y` → `⊢ f x = f y`, for a fixed function `f`
    /// (congruence with a reflexive function side).
    fn cong_arg(self, f: Term) -> Result<Thm>;

    /// `⊢ p` → `⊢ p = T` (HOL Light's `EQT_INTRO`). Via
    /// [`Thm::deduct_antisym`] against [`truth`](crate::init::logic::truth).
    fn eqt_intro(self) -> Result<Thm>;

    /// `⊢ p = T` → `⊢ p` (HOL Light's `EQT_ELIM`). Via [`Thm::eq_mp`]
    /// of the symmetric equation against
    /// [`truth`](crate::init::logic::truth).
    fn eqt_elim(self) -> Result<Thm>;

    /// Split `⊢ p ∧ q` into `(⊢ p, ⊢ q)`. Errors if the conclusion is
    /// not a conjunction.
    fn conjuncts(self) -> Result<(Thm, Thm)>;

    /// Split `Γ ⊢ c₁ ∧ c₂ ∧ … ∧ c_N` (a right-nested `∧`) into
    /// `[Γ ⊢ c₁, …, Γ ⊢ c_N]`; a non-conjunction yields the singleton `[self]`.
    /// Iterated `and_elim_l`/`and_elim_r` — O(N) now that each `and_elim` is
    /// O(1) (`Thm::build` reads cached types), so this no longer needs to be a
    /// kernel primitive.
    fn into_conjuncts(self) -> Vec<Thm>;

    /// Rewrite every occurrence of `eq`'s LHS in `self`'s conclusion
    /// with `eq`'s RHS, given `eq : ⊢ a = b`. Given `Γ ⊢ φ` and
    /// `Δ ⊢ a = b`, returns `Γ ∪ Δ ⊢ φ'`. Built from
    /// [`TermExt::rw_all`] + [`Thm::eq_mp`].
    fn rewrite(self, eq: &Thm) -> Result<Thm>;

    /// δ-unfold every spine occurrence of `symbol` in `self`'s
    /// conclusion (see [`TermExt::delta_all`]). Given `Γ ⊢ φ`, returns
    /// `Γ ⊢ φ'`.
    fn delta_all(self, symbol: &dyn Symbol) -> Result<Thm>;

    /// Transform the **left** side of an equational conclusion: given
    /// `Γ ⊢ a = b` and a conversion `conv` producing `⊢ a = a'`, return
    /// `Γ ⊢ a' = b`. `conv` is any `Term → ⊢ that = …` builder (e.g. a
    /// closure calling [`TermExt::reduce`] / [`rw_all`](TermExt::rw_all)).
    fn lhs_conv(self, conv: impl FnOnce(&Term) -> Result<Thm>) -> Result<Thm>;

    /// Transform the **right** side of an equational conclusion: given
    /// `Γ ⊢ a = b` and a conversion `conv` producing `⊢ b = b'`, return
    /// `Γ ⊢ a = b'`.
    fn rhs_conv(self, conv: impl FnOnce(&Term) -> Result<Thm>) -> Result<Thm>;

    /// [`reduce`](TermExt::reduce) the left side of an equational
    /// conclusion: `Γ ⊢ a = b` → `Γ ⊢ a' = b`.
    fn reduce_lhs(self) -> Result<Thm>;

    /// [`reduce`](TermExt::reduce) the right side of an equational
    /// conclusion: `Γ ⊢ a = b` → `Γ ⊢ a = b'`.
    fn reduce_rhs(self) -> Result<Thm>;
}

impl ThmExt for Thm {
    fn cong_fn(self, arg: Term) -> Result<Thm> {
        self.cong_app(Thm::refl(arg)?)
    }

    fn cong_arg(self, f: Term) -> Result<Thm> {
        Thm::refl(f)?.cong_app(self)
    }

    fn eqt_intro(self) -> Result<Thm> {
        self.deduct_antisym(crate::init::logic::truth())
    }

    fn eqt_elim(self) -> Result<Thm> {
        self.sym()?.eq_mp(crate::init::logic::truth())
    }

    fn conjuncts(self) -> Result<(Thm, Thm)> {
        let l = self.clone().and_elim_l()?;
        let r = self.and_elim_r()?;
        Ok((l, r))
    }

    fn into_conjuncts(self) -> Vec<Thm> {
        // Peel c₁ ∧ (c₂ ∧ …) with CONJUNCT1/CONJUNCT2 until the head is not a
        // conjunction. Each `and_elim` is O(1) (cached-type `build`), so this is
        // O(N) — no kernel primitive needed.
        let mut out = Vec::new();
        let mut cur = self;
        loop {
            match cur.clone().and_elim_l() {
                Ok(head) => {
                    out.push(head);
                    cur = cur
                        .and_elim_r()
                        .expect("and_elim_r must succeed when and_elim_l did");
                }
                Err(_) => {
                    out.push(cur);
                    break;
                }
            }
        }
        out
    }

    fn rewrite(self, eq: &Thm) -> Result<Thm> {
        let conv = self.concl().rw_all(eq)?;
        conv.eq_mp(self)
    }

    fn delta_all(self, symbol: &dyn Symbol) -> Result<Thm> {
        let conv = self.concl().delta_all(symbol)?;
        conv.eq_mp(self)
    }

    fn lhs_conv(self, conv: impl FnOnce(&Term) -> Result<Thm>) -> Result<Thm> {
        // self : ⊢ a = b ; step : ⊢ a = a' ; sym + trans → ⊢ a' = b.
        let a = self.concl().as_eq().ok_or(Error::NotAnEquation)?.0.clone();
        let step = conv(&a)?;
        step.sym()?.trans(self)
    }

    fn rhs_conv(self, conv: impl FnOnce(&Term) -> Result<Thm>) -> Result<Thm> {
        // self : ⊢ a = b ; step : ⊢ b = b' ; trans → ⊢ a = b'.
        let b = self.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
        let step = conv(&b)?;
        self.trans(step)
    }

    fn reduce_lhs(self) -> Result<Thm> {
        self.lhs_conv(|t| t.reduce())
    }

    fn reduce_rhs(self) -> Result<Thm> {
        self.rhs_conv(|t| t.reduce())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn b() -> Type {
        Type::bool()
    }

    #[test]
    fn term_ext_builds_well_typed_connectives() {
        let p = Term::free("p", b());
        let q = Term::free("q", b());

        for t in [
            p.clone().and(q.clone()).unwrap(),
            p.clone().or(q.clone()).unwrap(),
            p.clone().imp(q.clone()).unwrap(),
            p.clone().iff(q.clone()).unwrap(),
            p.clone().not().unwrap(),
            p.clone().equals(q.clone()).unwrap(),
            p.clone().forall("p", b()).unwrap(),
            p.exists("p", b()).unwrap(),
        ] {
            assert_eq!(t.type_of().unwrap(), b());
        }
    }

    #[test]
    fn term_ext_rejects_ill_typed() {
        let p = Term::free("p", b());
        let n = Term::free("n", Type::nat());
        // `bool ∧ nat` and `bool = nat` must be refused, not built.
        assert!(p.clone().and(n.clone()).is_err());
        assert!(p.equals(n).is_err());
    }

    #[test]
    fn eqt_intro_then_elim_round_trips() {
        let truth = crate::init::logic::truth();
        let as_eq = truth.clone().eqt_intro().unwrap();
        assert!(
            as_eq.concl().as_eq().is_some(),
            "eqt_intro yields an equation"
        );
        let back = as_eq.eqt_elim().unwrap();
        assert_eq!(back.concl(), truth.concl());
        assert!(back.hyps().is_empty());
    }

    #[test]
    fn conjuncts_splits_a_conjunction() {
        let p = Thm::assume(Term::bool_lit(true)).unwrap();
        let q = Thm::assume(Term::bool_lit(false)).unwrap();
        let conj = p.clone().and_intro(q.clone()).unwrap();
        let (l, r) = conj.conjuncts().unwrap();
        assert_eq!(l.concl(), p.concl());
        assert_eq!(r.concl(), q.concl());
    }

    #[test]
    fn into_conjuncts_splits_a_chain() {
        // p ∧ (q ∧ r) → [⊢ p, ⊢ q, ⊢ r]; a non-conjunction → singleton.
        let p = Term::free("p", Type::bool());
        let q = Term::free("q", Type::bool());
        let r = Term::free("r", Type::bool());
        let qr = Thm::assume(q.clone())
            .unwrap()
            .and_intro(Thm::assume(r.clone()).unwrap())
            .unwrap();
        let pqr = Thm::assume(p.clone()).unwrap().and_intro(qr).unwrap();
        let parts = pqr.into_conjuncts();
        assert_eq!(parts.len(), 3);
        assert_eq!(parts[0].concl(), &p);
        assert_eq!(parts[1].concl(), &q);
        assert_eq!(parts[2].concl(), &r);

        let single = Thm::assume(p.clone()).unwrap().into_conjuncts();
        assert_eq!(single.len(), 1);
        assert_eq!(single[0].concl(), &p);
    }

    #[test]
    fn cong_fn_and_cong_arg() {
        let nat = Type::nat();
        let a = Term::free("a", nat.clone());
        let bb = Term::free("b", nat.clone());
        let f = Term::free("f", Type::fun(nat.clone(), nat.clone()));
        let ab = Thm::assume(a.clone().equals(bb.clone()).unwrap()).unwrap();

        // a = b  ⊢  f a = f b
        let by_arg = ab.clone().cong_arg(f.clone()).unwrap();
        let (l, r) = by_arg.concl().as_eq().unwrap();
        assert_eq!(l, &f.clone().apply(a.clone()).unwrap());
        assert_eq!(r, &f.apply(bb).unwrap());

        // f = f  ⊢  f a = f a   (reflexive fn side, fixed arg a)
        let ff = Thm::refl(Term::free("g", Type::fun(nat.clone(), nat))).unwrap();
        let by_fn = ff.cong_fn(a).unwrap();
        assert!(by_fn.concl().as_eq().is_some());
    }

    #[test]
    fn rw_all_via_term_ext() {
        let nat = Type::nat();
        let a = Term::free("a", nat.clone());
        let bb = Term::free("b", nat.clone());
        let f = Term::free("f", Type::fun(nat.clone(), Type::fun(nat.clone(), nat)));
        let eq = Thm::assume(a.clone().equals(bb.clone()).unwrap()).unwrap();

        // f a a  rewrites to  f b b
        let t = f
            .clone()
            .apply(a.clone())
            .unwrap()
            .apply(a.clone())
            .unwrap();
        let conv = t.rw_all(&eq).unwrap();
        let (lhs, rhs) = conv.concl().as_eq().unwrap();
        assert_eq!(lhs, &t);
        assert_eq!(rhs, &f.apply(bb.clone()).unwrap().apply(bb).unwrap());
    }

    // ---- δ-reduction ----

    fn nat_lit(n: u32) -> Term {
        Term::nat_lit(covalence_types::Nat::from_inner(n.into()))
    }

    fn add(x: Term, y: Term) -> Term {
        covalence_core::defs::nat_add()
            .apply(x)
            .unwrap()
            .apply(y)
            .unwrap()
    }

    #[test]
    fn delta_unfolds_a_single_definition() {
        let eq = covalence_core::defs::and().delta().unwrap(); // ⊢ ∧ = body
        let (lhs, rhs) = eq.concl().as_eq().unwrap();
        assert_eq!(lhs, &covalence_core::defs::and());
        assert_ne!(rhs, lhs);
        assert!(eq.hyps().is_empty());
    }

    #[test]
    fn delta_errors_on_non_spec_leaf() {
        assert!(Term::free("x", b()).delta().is_err());
    }

    #[test]
    fn delta_all_unfolds_spine_occurrences() {
        let a = Term::free("a", b());
        let bb = Term::free("b", b());
        let t = a.and(bb).unwrap(); // a ∧ b
        let spec = covalence_core::defs::and_spec();
        let conv = t.delta_all(spec.symbol()).unwrap();
        let (lhs, rhs) = conv.concl().as_eq().unwrap();
        assert_eq!(lhs, &t);
        assert_ne!(rhs, lhs, "the ∧ head must be unfolded");
    }

    #[test]
    fn delta_all_is_symbol_scoped_and_weak() {
        let a = Term::free("a", b());
        let bb = Term::free("b", b());
        let conj = a.and(bb).unwrap();

        // `or` does not occur → identity conversion.
        let or_spec = covalence_core::defs::or_spec();
        let noop = conj.delta_all(or_spec.symbol()).unwrap();
        let (l, r) = noop.concl().as_eq().unwrap();
        assert_eq!(l, r);

        // A matching symbol *under a binder* is left alone (weak).
        let under = Term::abs(b(), conj); // λ_. (a ∧ b)
        let and_spec = covalence_core::defs::and_spec();
        let weak = under.delta_all(and_spec.symbol()).unwrap();
        let (l2, r2) = weak.concl().as_eq().unwrap();
        assert_eq!(l2, r2, "delta_all must not unfold under λ");
    }

    #[test]
    fn thm_delta_all_unfolds_in_conclusion() {
        let tt = Term::bool_lit(true).and(Term::bool_lit(true)).unwrap();
        let thm = Thm::assume(tt.clone()).unwrap();
        let and_spec = covalence_core::defs::and_spec();
        let out = thm.delta_all(and_spec.symbol()).unwrap();
        assert_ne!(out.concl(), &tt, "conclusion's ∧ must be unfolded");
        assert!(out.hyps().iter().any(|h| h == &tt), "hyp kept");
    }

    // ---- weak reduction ----

    #[test]
    fn reduce_consts_folds_arithmetic_in_the_spine() {
        // nat.add (nat.add 1 1) 1  →  3
        let t = add(add(nat_lit(1), nat_lit(1)), nat_lit(1));
        let conv = t.reduce_consts().unwrap();
        assert_eq!(conv.concl().as_eq().unwrap().1, &nat_lit(3));
    }

    #[test]
    fn reduce_consts_is_weak() {
        // λ_:nat. (1 + 1)  is unchanged — the redex is under the binder.
        let lam = Term::abs(Type::nat(), add(nat_lit(1), nat_lit(1)));
        let conv = lam.reduce_consts().unwrap();
        let (l, r) = conv.concl().as_eq().unwrap();
        assert_eq!(l, r, "reduce_consts must not reduce under λ");
    }

    #[test]
    fn reduce_does_beta_then_consts() {
        // (λx:nat. x + 1) 4  →  5
        let nat = Type::nat();
        let x = Term::free("x", nat.clone());
        let body = add(x, nat_lit(1));
        let f = Term::abs(nat, covalence_core::subst::close(&body, "x"));
        let t = f.apply(nat_lit(4)).unwrap();
        let conv = t.reduce().unwrap();
        assert_eq!(conv.concl().as_eq().unwrap().1, &nat_lit(5));
    }

    #[test]
    fn prove_true_decides_a_closed_goal() {
        // ⊢ (2 + 2) = 4   by reducing the bool expression to T.
        let goal = add(nat_lit(2), nat_lit(2)).equals(nat_lit(4)).unwrap();
        let thm = goal.prove_true().unwrap();
        assert_eq!(thm.concl(), &goal);
        assert!(thm.hyps().is_empty());

        // A false goal does not reduce to T → Err, no Thm minted.
        let bad = add(nat_lit(2), nat_lit(2)).equals(nat_lit(5)).unwrap();
        assert!(bad.prove_true().is_err());
    }

    #[test]
    fn reduce_rhs_evaluates_the_right_side() {
        // {x = 1+1} ⊢ x = 1+1   →   {…} ⊢ x = 2
        let x = Term::free("x", Type::nat());
        let eq = Thm::assume(x.clone().equals(add(nat_lit(1), nat_lit(1))).unwrap()).unwrap();
        let out = eq.reduce_rhs().unwrap();
        let (l, r) = out.concl().as_eq().unwrap();
        assert_eq!(l, &x);
        assert_eq!(r, &nat_lit(2));
    }
}
