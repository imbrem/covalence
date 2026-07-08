//! The certificate [`Thm<L, P>`], the equality proposition [`Eqn<A, B>`], and the
//! equality calculus.
//!
//! [`Thm<L, P>`] (`P: Expr<Ty = bool>`) is THE certificate: "the proposition `P`
//! holds in language value `lang: L`" (the LCF `thm`). Its fields are **private
//! with no public constructor** — the unforgeability gate; the sole mint is the
//! `pub(crate)` [`Thm::new`], and *every* call site is audited (they are exactly:
//! this module's calculus + gated injectors incl. `eq_mp`, the [`crate::prop`]
//! bool theory, [`crate::matching`]'s `apply_rewrite`, and [`crate::rel`]'s
//! `execute` (gated) + `Thm::transpose` (ungated-but-trusted)).
//!
//! [`Eqn<A, B>`] is the equality **proposition** `A = B` — a freely-constructible
//! [`Expr`] of sort `bool`. Building one proves nothing; it also serves as the
//! "candidate equation" a [`Rule`] may take as input. A **proven** equality is
//! [`ThmEqn<L, A, B>`] = [`Thm<L, Eqn<A, B>>`], on which the congruence calculus
//! lives.

use std::any::TypeId;

use crate::expr::{App, Expr, Ref, TrustedDeref, Val};
use crate::lang::{CanonRule, Language, Rule};
use crate::sealed;

/// Errors from the gated minting paths and `trans`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    /// `lang.admits(rule)` returned `false`.
    NotAdmitted(TypeId),
    /// `into.extends(parent)` returned `false` (lift target is not a child).
    NotExtended(TypeId),
    /// `trans` middle terms were not `Eq`-equal.
    TransMismatch,
    /// Two language values could not be combined (`union`/`extends` mismatch).
    LangMismatch,
    /// `semidecide` could not prove equality (`a != b` under untrusted `Eq`).
    Undecided,
    /// A pattern/decision rule inspected its input and declined to fire (no match).
    NoMatch,
    /// A [`Rule::decide`](crate::Rule::decide) failed.
    RuleFailed(String),
}

/// The equality **proposition** `A = B` (same sort) — an [`Expr`] of sort `bool`.
/// Freely constructible (public fields); building one proves *nothing*. Doubles as
/// the "candidate equation" a [`Rule`] can validate. A *proven* equality is
/// [`ThmEqn`] = [`Thm<L, Eqn<A, B>>`]. Replaces the old `EqOp` and `Cand`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Eqn<A, B>(pub A, pub B);

impl<A: Expr, B: Expr<Ty = A::Ty>> sealed::Sealed for Eqn<A, B> {}
impl<A: Expr, B: Expr<Ty = A::Ty>> Expr for Eqn<A, B> {
    type Ty = bool;
}

/// The unforgeable certificate: "the proposition `prop: P` holds in language value
/// `lang: L`" (the LCF `thm`). Private fields, no public constructor. The `L` value
/// carries the hypotheses/axioms in scope, so combining two theorems requires
/// combining their `lang`s (`Language::union`).
#[derive(Clone, Debug)]
pub struct Thm<L, P> {
    lang: L,
    prop: P,
}

/// A **proven** equality `⊢ A = B`, the home of the congruence calculus.
pub type ThmEqn<L, A, B> = Thm<L, Eqn<A, B>>;

impl<L, P: Expr<Ty = bool>> Thm<L, P> {
    /// The sole constructor — the minting gate. `pub(crate)` so the calculus here
    /// (incl. `eq_mp`), the [`crate::prop`] bool theory, and [`crate::matching`]'s
    /// `apply_rewrite` (the only minting sites, all audited) can use it; never
    /// exposed outside the crate. The `P: Expr<Ty = bool>` bound
    /// guarantees every certificate proposition is a boolean.
    pub(crate) fn new(lang: L, prop: P) -> Self {
        Thm { lang, prop }
    }
}

impl<L, P> Thm<L, P> {
    /// Owned destructure into `(lang, prop)` — `pub(crate)`, for the calculus to
    /// move parts into a freshly-minted theorem. Forgets the proof (the parts
    /// cannot be recombined without `new`).
    pub(crate) fn into_parts(self) -> (L, P) {
        (self.lang, self.prop)
    }

    /// The proposition this theorem proves (read-only; reading never mints).
    pub fn prop(&self) -> &P {
        &self.prop
    }
    /// The language value this theorem was proved in.
    pub fn lang(&self) -> &L {
        &self.lang
    }
}

// Convenience accessors on a proven equality.
impl<L, A, B> Thm<L, Eqn<A, B>> {
    /// The left-hand side of the proven equality.
    pub fn lhs(&self) -> &A {
        &self.prop.0
    }
    /// The right-hand side of the proven equality.
    pub fn rhs(&self) -> &B {
        &self.prop.1
    }
}

// ---- Ungated: the universal equality calculus (sound in every L) ----

impl<L, A: Expr + Clone> Thm<L, Eqn<A, A>> {
    /// Reflexivity: `⊢ a = a`, built by duplicating `a` via [`Clone`]. `Clone` is
    /// **not trusted** as an external fact here: together with `of_eq`'s [`Eq`] it is
    /// one of the two rules that *define* leaf equality (a sort's `Clone` is what
    /// "the same value" means). A distinguishing step needs an *admitted* rule, so an
    /// unusual `Clone` is inert in `()`. See the crate-root trust surface.
    pub fn refl(e: A, lang: L) -> Self {
        Thm::new(lang, Eqn(e.clone(), e))
    }
}

impl<L, A, B> Thm<L, Eqn<A, B>>
where
    A: Expr,
    B: Expr<Ty = A::Ty>,
{
    /// Symmetry: from `⊢ a = b` get `⊢ b = a`.
    pub fn sym(self) -> Thm<L, Eqn<B, A>> {
        let (lang, Eqn(a, b)) = self.into_parts();
        Thm::new(lang, Eqn(b, a))
    }
}

impl<L: Language, A, B> Thm<L, Eqn<A, B>>
where
    A: Expr,
    B: Expr<Ty = A::Ty>,
{
    /// Transitivity: from `⊢ a = b` and `⊢ b' = c`, where the middle terms `b`/`b'`
    /// match (`B: Eq`, stdlib `==` on the `derive(Eq)` structural equality), get
    /// `⊢ a = c` under the **union** of the two contexts. `Err` if the middles
    /// differ or the contexts cannot be combined.
    pub fn trans<C>(self, other: Thm<L, Eqn<B, C>>) -> Result<Thm<L, Eqn<A, C>>, Error>
    where
        B: Eq,
        C: Expr<Ty = A::Ty>,
    {
        let (l1, Eqn(a, b)) = self.into_parts();
        let (l2, Eqn(b2, c)) = other.into_parts();
        if b != b2 {
            return Err(Error::TransMismatch);
        }
        let lang = l1.union(l2).ok_or(Error::LangMismatch)?;
        Ok(Thm::new(lang, Eqn(a, c)))
    }
}

impl<L: Language, P: Expr<Ty = bool> + Eq> Thm<L, P> {
    /// Equality modus ponens: from `⊢ P` and `⊢ P = Q` (both `bool`-sorted), get
    /// `⊢ Q`, under the **union** of the two contexts. `None` if the equation's
    /// left-hand side does not match this theorem's proposition (`P: Eq`, the same
    /// structural middle-match [`trans`](Self::trans) uses) or the contexts cannot
    /// be combined. The equality-calculus mirror of [`mp`](Self::mp).
    ///
    /// Soundness: Leibniz on the definitional equality — `⊢ P = Q` certifies that
    /// `P` and `Q` denote the same boolean, so if `P` holds then `Q` holds. This is
    /// the same class of ungated, sound-in-every-`L` step as [`trans`](Self::trans)
    /// (transport along a proven equation, matched by structural `Eq`); it
    /// introduces no new equalities and no new evaluation, only re-labels a proven
    /// proposition by an already-proven equation.
    pub fn eq_mp<Q: Expr<Ty = bool>>(self, eq: Thm<L, Eqn<P, Q>>) -> Option<Thm<L, Q>> {
        let (l1, p) = self.into_parts();
        let (l2, Eqn(p2, q)) = eq.into_parts();
        // NB `!(p == p2)`, not `p != p2`: `ne` is independently overridable on
        // `PartialEq`; the trusted match must be the same `eq` the calculus uses.
        if !(p == p2) {
            return None;
        }
        let lang = l1.union(l2)?;
        Some(Thm::new(lang, q))
    }
}

impl<L, A, A2> Thm<L, Eqn<A, A2>> {
    /// Congruence in the ARGUMENT, under any op `F` (ops denote functions). There
    /// is deliberately no congruence in the *operator* — you cannot equate ops.
    ///
    /// `F` is duplicated via [`Clone`] onto both sides, so (as for [`refl`](Self::refl))
    /// `F::clone` *defines* op identity rather than being trusted. If `F` is
    /// uninterpreted this is inert; the only way to observe `f.clone() ≠ f` is to
    /// *admit* a [`CanonRule`] whose `clone`/`eval` disagree — a self-inflicted
    /// inconsistency in that language (like a false axiom), not a framework hole.
    pub fn cong_app<F>(self, f: F) -> Thm<L, Eqn<App<F, A>, App<F, A2>>>
    where
        F: crate::op::Op + Clone,
        A: Expr<Ty = F::In>,
        A2: Expr<Ty = F::In>,
    {
        let (lang, Eqn(a, a2)) = self.into_parts();
        Thm::new(lang, Eqn(App(f.clone(), a), App(f, a2)))
    }
}

impl<L: Language, A, A2> Thm<L, Eqn<A, A2>>
where
    A: Expr,
    A2: Expr<Ty = A::Ty>,
{
    /// Pair congruence: from `⊢ a = a2` and `⊢ b = b2` get `⊢ (a, b) = (a2, b2)`
    /// under the **union** of the two contexts. `Err` if they cannot be combined.
    pub fn cong_pair<B, B2>(
        self,
        other: Thm<L, Eqn<B, B2>>,
    ) -> Result<Thm<L, Eqn<(A, B), (A2, B2)>>, Error>
    where
        B: Expr,
        B2: Expr<Ty = B::Ty>,
    {
        let (l1, Eqn(a, a2)) = self.into_parts();
        let (l2, Eqn(b, b2)) = other.into_parts();
        let lang = l1.union(l2).ok_or(Error::LangMismatch)?;
        Ok(Thm::new(lang, Eqn((a, b), (a2, b2))))
    }
}

// ---- Pointer equality (via TrustedDeref; no `Eq` on the pointee needed) ----

impl<L: Language, A, P> Thm<L, Eqn<A, Ref<P>>>
where
    A: Expr<Ty = P::Target>,
    P: TrustedDeref,
    P::Target: Sized,
{
    /// Transitivity through a **pointer-equal** middle: from `⊢ a = Ref(p)` and
    /// `⊢ Ref(q) = c`, where `p` and `q` are the *same pointer* (address-equal), get
    /// `⊢ a = c` — no `Eq` on the pointee required. Sound: the same address is the
    /// same value.
    pub fn trans_ptr<Q, C>(self, other: Thm<L, Eqn<Ref<Q>, C>>) -> Result<Thm<L, Eqn<A, C>>, Error>
    where
        Q: TrustedDeref<Target = P::Target>,
        C: Expr<Ty = P::Target>,
    {
        let (l1, Eqn(a, p)) = self.into_parts();
        let (l2, Eqn(q, c)) = other.into_parts();
        if !std::ptr::eq(&*p.0, &*q.0) {
            return Err(Error::TransMismatch);
        }
        let lang = l1.union(l2).ok_or(Error::LangMismatch)?;
        Ok(Thm::new(lang, Eqn(a, c)))
    }
}

/// `⊢ Ref(p) = Ref(q)` when `p` and `q` are the **same pointer** (address-equal) —
/// sound without any `Eq` on the pointee. The pointer-equality seam for sharing.
pub fn of_ptr_eq<P, Q, L>(p: Ref<P>, q: Ref<Q>, lang: L) -> Option<Thm<L, Eqn<Ref<P>, Ref<Q>>>>
where
    P: TrustedDeref,
    Q: TrustedDeref<Target = P::Target>,
    P::Target: Sized,
{
    std::ptr::eq(&*p.0, &*q.0).then(|| Thm::new(lang, Eqn(p, q)))
}

// ---- Lift: weaken the language one layer (sound: tree(L2) ⊆ tree(L)) ----

impl<L2: Language, P: Expr<Ty = bool>> Thm<L2, P> {
    /// Re-home this theorem into a language `into` that **directly extends** `L2`.
    /// Runtime-checks `into.extends(TypeId::of::<L2>())` before minting; sound
    /// because `extends` guarantees `tree(L2) ⊆ tree(into)`.
    pub fn lift<L: Language>(self, into: L) -> Result<Thm<L, P>, Error> {
        let parent = TypeId::of::<L2>();
        if !into.extends(parent) {
            return Err(Error::NotExtended(parent));
        }
        let (_, prop) = self.into_parts();
        Ok(Thm::new(into, prop))
    }
}

// ---- Ungated leaf equality (intrinsic to a sort — a sort *is* its `Eq`) ----

/// `⊢ Val(a) = Val(b)` whenever `a == b` (`C: Eq`), in an explicit language value.
/// **Ungated** — leaf equality is intrinsic to a sort, so this is sound in every
/// language (it never bridges values `Eq` calls unequal). `None` if `a != b`.
pub fn of_eq_with<C: Eq, L>(a: C, b: C, lang: L) -> Option<Thm<L, Eqn<Val<C>, Val<C>>>> {
    (a == b).then(|| Thm::new(lang, Eqn(Val(a), Val(b))))
}

/// [`of_eq_with`] in the **default** language value (`L: Default`).
pub fn of_eq<C: Eq, L: Default>(a: C, b: C) -> Option<Thm<L, Eqn<Val<C>, Val<C>>>> {
    of_eq_with(a, b, L::default())
}

/// The certificate `⊢ Val(a) = Val(b)` from `a == b` (`C: Eq`), or
/// [`Error::Undecided`] when `a != b` (plain `Eq` trusts only the `true` direction).
pub fn semidecide<C: Eq, L>(a: C, b: C, lang: L) -> Result<Thm<L, Eqn<Val<C>, Val<C>>>, Error> {
    of_eq_with(a, b, lang).ok_or(Error::Undecided)
}

// ---- Gated: anything that injects external trust (runtime `admits`) ----

/// Apply a general [`Rule`] to `input`. Gated on **`Rho`'s own `TypeId`** being
/// admitted — the gate identity is the very type whose `decide` produces the
/// conclusion, so an admitted rule cannot be impersonated. The untrusted `decide`
/// runs only *after* the gate passes; its output is unused until minted here (the
/// sole choke point).
pub fn apply<L, Rho>(lang: L, rho: Rho, input: Rho::Input) -> Result<Thm<L, Rho::Concl>, Error>
where
    L: Language,
    Rho: Rule<L>,
{
    let rule = TypeId::of::<Rho>();
    if !lang.admits(rule) {
        return Err(Error::NotAdmitted(rule));
    }
    let concl = rho.decide(input, &lang)?;
    Ok(Thm::new(lang, concl))
}

/// Convenience for a **nullary-axiom** rule (`Rule<L, Input = ()>`), so a callsite
/// need not pass a `()` explicitly.
pub fn apply0<L: Language, Rho: Rule<L, Input = ()>>(
    lang: L,
    rho: Rho,
) -> Result<Thm<L, Rho::Concl>, Error> {
    apply(lang, rho, ())
}

/// Evaluate an op to its canonical value: `⊢ App<F, Val(v)> = Val(F.eval(v))`. Gated
/// on `F`'s `TypeId` (the op-as-rule). Sound: the equation holds by literal
/// denotation, since the argument is the ground value `Val(v)`.
pub fn canon<L, F>(
    f: F,
    arg: F::In,
    lang: L,
) -> Result<Thm<L, Eqn<App<F, Val<F::In>>, Val<F::Out>>>, Error>
where
    L: Language,
    F: CanonRule,
{
    let rule = TypeId::of::<F>();
    if !lang.admits(rule) {
        return Err(Error::NotAdmitted(rule));
    }
    let out = f.eval(&arg).ok_or(Error::NoMatch)?;
    Ok(Thm::new(lang, Eqn(App(f, Val(arg)), Val(out))))
}
