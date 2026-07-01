//! The certificate [`Eqn<A, B, L>`] and the equality calculus.
//!
//! Equality is the *primitive* judgement (HOL-Light style). `Eqn<A, B, L>` says
//! `A = B` holds in language value `lang: L`. Its fields are **private with no
//! public constructor** — the unforgeability gate. The only ways to mint one are
//! the methods/functions in this module: the **ungated** equality calculus
//! (`refl`/`sym`/`trans`/`cong_*`, sound in *every* language) and the **gated**
//! injectors ([`of_teq`]/[`apply`]/[`canon`]/[`Eqn::lift`]), each of which
//! runtime-checks `lang.admits(..)`/`lang.extends(..)` *before* minting.

use std::any::TypeId;

use crate::expr::{App, Ref, TrustedDeref, Val};
use crate::lang::{CanonRule, Language, Rule};

/// Errors from the gated minting paths and `trans`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    /// `lang.admits(rule)` returned `false`.
    NotAdmitted(TypeId),
    /// `into.extends(parent)` returned `false` (lift target is not a child).
    NotExtended(TypeId),
    /// `trans` middle terms were not `Eq`-equal.
    TransMismatch,
    /// `trans` was given two different language values.
    LangMismatch,
    /// `semidecide` could not prove equality (`a != b` under untrusted `Eq`).
    Undecided,
    /// A [`Rule::conclude`] failed.
    RuleFailed(String),
}

/// `lhs` and `rhs` (expressions of the SAME sort) are equal in language value
/// `lang`. Private fields ⇒ **unforgeable**; minted only by this module's calculus
/// and admitted rules. The `L` value carries the hypotheses/axioms in scope, so
/// `trans` requires equal `lang`s (same context).
#[derive(Clone, Debug)]
pub struct Eqn<A, B, L> {
    lhs: A,
    rhs: B,
    lang: L,
}

/// A propositional theorem `⊢ P` is just equality with `⊤` (`P` holds ⟺ `P = ⊤`).
pub type Thm<P, L> = Eqn<P, True, L>;

use crate::expr::True;

impl<A, B, L> Eqn<A, B, L> {
    /// The sole constructor — the minting gate, `pub(crate)` so the calculus here
    /// and the propositional rules in [`crate::prop`] (the only two minting sites,
    /// both audited) can use it; never exposed outside the crate.
    pub(crate) fn new(lhs: A, rhs: B, lang: L) -> Self {
        Eqn { lhs, rhs, lang }
    }

    /// Owned destructure into `(lhs, rhs, lang)` — `pub(crate)`, for the
    /// propositional rules to move parts into a freshly-minted equation. Forgets
    /// the proof (the parts cannot be recombined without `new`).
    pub(crate) fn into_parts(self) -> (A, B, L) {
        (self.lhs, self.rhs, self.lang)
    }

    /// The left-hand side (read-only; reading never mints).
    pub fn lhs(&self) -> &A {
        &self.lhs
    }
    /// The right-hand side.
    pub fn rhs(&self) -> &B {
        &self.rhs
    }
    /// The language value this equation was proved in.
    pub fn lang(&self) -> &L {
        &self.lang
    }
}

// ---- Ungated: the universal equality calculus (sound in every L) ----

impl<A: Clone, L> Eqn<A, A, L> {
    /// Reflexivity: `a = a`. (`Clone` to duplicate the expression into both sides.)
    pub fn refl(e: A, lang: L) -> Self {
        Eqn::new(e.clone(), e, lang)
    }
}

impl<A, B, L> Eqn<A, B, L> {
    /// Symmetry: from `a = b` get `b = a`.
    pub fn sym(self) -> Eqn<B, A, L> {
        Eqn::new(self.rhs, self.lhs, self.lang)
    }
}

impl<A, B, L: Language> Eqn<A, B, L> {
    /// Transitivity: from `a = b` and `b' = c`, where the middle terms `b`/`b'`
    /// match (`B: Eq`, stdlib `==` on the `derive(Eq)` structural equality), get
    /// `a = c` under the **union** of the two contexts. `Err` if the middles differ
    /// or the contexts cannot be combined.
    pub fn trans<C>(self, rhs: Eqn<B, C, L>) -> Result<Eqn<A, C, L>, Error>
    where
        B: Eq,
    {
        if self.rhs != rhs.lhs {
            return Err(Error::TransMismatch);
        }
        let lang = self.lang.union(rhs.lang).ok_or(Error::LangMismatch)?;
        Ok(Eqn::new(self.lhs, rhs.rhs, lang))
    }
}

impl<A, A2, L> Eqn<A, A2, L> {
    /// Congruence in the ARGUMENT, under any op `F` (ops denote functions). There
    /// is deliberately no congruence in the *operator* — you cannot equate ops.
    pub fn cong_app<F>(self, f: F) -> Eqn<App<F, A>, App<F, A2>, L>
    where
        F: crate::op::Op + Clone,
    {
        Eqn::new(App(f.clone(), self.lhs), App(f, self.rhs), self.lang)
    }
}

impl<A, A2, L: Language> Eqn<A, A2, L> {
    /// Pair congruence: from `a = a2` and `b = b2` get `(a, b) = (a2, b2)` under the
    /// **union** of the two contexts. `Err` if they cannot be combined.
    pub fn cong_pair<B, B2>(self, other: Eqn<B, B2, L>) -> Result<Eqn<(A, B), (A2, B2), L>, Error> {
        let lang = self.lang.union(other.lang).ok_or(Error::LangMismatch)?;
        Ok(Eqn::new((self.lhs, other.lhs), (self.rhs, other.rhs), lang))
    }
}

// ---- Pointer equality (via TrustedDeref; no `Eq` on the pointee needed) ----

impl<A, P, L: Language> Eqn<A, Ref<P>, L>
where
    P: TrustedDeref,
    P::Target: Sized,
{
    /// Transitivity through a **pointer-equal** middle: from `a = Ref(p)` and
    /// `Ref(q) = c`, where `p` and `q` are the *same pointer* (address-equal), get
    /// `a = c` — no `Eq` on the pointee required. Sound: the same address is the
    /// same value.
    pub fn trans_ptr<Q, C>(self, rhs: Eqn<Ref<Q>, C, L>) -> Result<Eqn<A, C, L>, Error>
    where
        Q: TrustedDeref<Target = P::Target>,
    {
        let (a, p, l1) = self.into_parts();
        let (q, c, l2) = rhs.into_parts();
        if !std::ptr::eq(&*p.0, &*q.0) {
            return Err(Error::TransMismatch);
        }
        let lang = l1.union(l2).ok_or(Error::LangMismatch)?;
        Ok(Eqn::new(a, c, lang))
    }
}

/// `Ref(p) = Ref(q)` when `p` and `q` are the **same pointer** (address-equal) —
/// sound without any `Eq` on the pointee. The pointer-equality seam for sharing.
pub fn of_ptr_eq<P, Q, L>(p: Ref<P>, q: Ref<Q>, lang: L) -> Option<Eqn<Ref<P>, Ref<Q>, L>>
where
    P: TrustedDeref,
    Q: TrustedDeref<Target = P::Target>,
    P::Target: Sized,
{
    std::ptr::eq(&*p.0, &*q.0).then(|| Eqn::new(p, q, lang))
}

// ---- Lift: weaken the language one layer (sound: tree(L2) ⊆ tree(L)) ----

impl<A, B, L2: Language> Eqn<A, B, L2> {
    /// Re-home this equation into a language `into` that **directly extends** `L2`.
    /// Runtime-checks `into.extends(TypeId::of::<L2>())` before minting; sound
    /// because `extends` guarantees `tree(L2) ⊆ tree(into)`.
    pub fn lift<L: Language>(self, into: L) -> Result<Eqn<A, B, L>, Error> {
        let parent = TypeId::of::<L2>();
        if !into.extends(parent) {
            return Err(Error::NotExtended(parent));
        }
        Ok(Eqn::new(self.lhs, self.rhs, into))
    }
}

/// `Val(a) = Val(b)` whenever `a == b` (`C: Eq`). **Ungated** — leaf equality is
/// intrinsic to a sort (a sort *is* its `Eq`), so this is sound in every language;
/// it is just a typed convenience over `refl` (it never bridges values `Eq` calls
/// unequal). `None` if `a != b`.
pub fn of_eq<C: Eq, L>(a: C, b: C, lang: L) -> Option<Eqn<Val<C>, Val<C>, L>> {
    (a == b).then(|| Eqn::new(Val(a), Val(b), lang))
}

// ---- Gated: anything that injects external trust (runtime `admits`) ----

/// Apply a general [`Rule`] (premises ride inside `rho`). Gated on **`Rho`'s own
/// `TypeId`** being admitted — the gate identity is the very type whose `conclude`
/// produces the equation, so an admitted rule cannot be impersonated.
pub fn apply<L, Rho>(lang: L, rho: Rho) -> Result<Eqn<Rho::Lhs, Rho::Rhs, L>, Error>
where
    L: Language,
    Rho: Rule<L>,
{
    let rule = TypeId::of::<Rho>();
    if !lang.admits(rule) {
        return Err(Error::NotAdmitted(rule));
    }
    let (lhs, rhs) = rho.conclude()?;
    Ok(Eqn::new(lhs, rhs, lang))
}

/// Evaluate an op to its canonical value: `App<F, Val(v)> = Val(F.eval(v))`. Gated
/// on `F`'s `TypeId` (the op-as-rule). Sound: the equation holds by literal
/// denotation, since the argument is the ground value `Val(v)`.
pub fn canon<L, F>(
    f: F,
    arg: F::In,
    lang: L,
) -> Result<Eqn<App<F, Val<F::In>>, Val<F::Out>, L>, Error>
where
    L: Language,
    F: CanonRule,
{
    let rule = TypeId::of::<F>();
    if !lang.admits(rule) {
        return Err(Error::NotAdmitted(rule));
    }
    let out = Val(f.eval(&arg));
    Ok(Eqn::new(App(f, Val(arg)), out, lang))
}
