//! **Bool theory** — part of every language's equational core.
//!
//! The propositional connectives (`And`/`Or`/`Imp`/`Not`) and equality-as-a-bool
//! (`EqOp`) are ops; their logic is **ungated builtin methods** on `Eqn`/`Thm`
//! (sound in *every* language, like the equality calculus — propositional logic is
//! valid in any model). So "P holds" (`Thm<P, L> = Eqn<P, True, L>`) supports:
//! deconstructing an `And`, injecting into an `Or`, modus ponens for `Imp`, and
//! reflecting between an equality certificate `Eqn<A,B,L>` and the bool proposition
//! `A = B` (`EqOp`).
//!
//! These are the second minting site (besides the [`crate::eqn`] calculus); both
//! go through the `pub(crate)` `Eqn::new`.

use std::fmt;
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;

use crate::eqn::Eqn;
use crate::expr::{App, Expr, True};
use crate::lang::Language;
use crate::op::Op;

// ---- The propositional vocabulary (ops) ----

macro_rules! conn {
    ($(#[$m:meta])* $name:ident, $in:ty) => {
        $(#[$m])*
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        pub struct $name;
        impl Op for $name { type In = $in; type Out = bool; }
    };
}

conn!(/// Conjunction `(bool, bool) → bool`.
    And, (bool, bool));
conn!(/// Disjunction `(bool, bool) → bool`.
    Or, (bool, bool));
conn!(/// Implication `(bool, bool) → bool`.
    Imp, (bool, bool));
conn!(/// Negation `bool → bool`.
    Not, bool);

/// Equality at sort `S`, internalized as a `bool`-valued op: `App<EqOp<S>, (a, b)>`
/// is the proposition "`a = b`". A ZST marker (its `Clone`/`Eq`/… are unconditional
/// in `S`, so `App<EqOp<S>, _>` is `Eq` whenever its argument is).
pub struct EqOp<S>(PhantomData<fn() -> S>);

impl<S> EqOp<S> {
    pub(crate) fn new() -> Self {
        EqOp(PhantomData)
    }
}
impl<S> Clone for EqOp<S> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<S> Copy for EqOp<S> {}
impl<S> PartialEq for EqOp<S> {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}
impl<S> Eq for EqOp<S> {}
impl<S> Hash for EqOp<S> {
    fn hash<H: Hasher>(&self, _: &mut H) {}
}
impl<S> fmt::Debug for EqOp<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("EqOp")
    }
}
impl<S> Op for EqOp<S> {
    type In = (S, S);
    type Out = bool;
}

// ---- Builtin propositional logic (ungated; sound in every language) ----

impl<P, L: Language> Eqn<P, True, L> {
    /// ∧-introduction: from `⊢ P` and `⊢ Q` get `⊢ P ∧ Q`, under the **union** of
    /// the two contexts. `None` if the contexts cannot be combined.
    pub fn and_intro<Q>(self, other: Eqn<Q, True, L>) -> Option<Eqn<App<And, (P, Q)>, True, L>>
    where
        P: Expr<Ty = bool>,
        Q: Expr<Ty = bool>,
    {
        let (p, _, l1) = self.into_parts();
        let (q, _, l2) = other.into_parts();
        let lang = l1.union(l2)?;
        Some(Eqn::new(App(And, (p, q)), True, lang))
    }
}

impl<P: Expr<Ty = bool>, L> Eqn<P, True, L> {
    /// ∨-introduction (left): from `⊢ P` get `⊢ P ∨ Q` for any `Q` (you supply the
    /// other disjunct expression).
    pub fn or_inl<Q: Expr<Ty = bool>>(self, q: Q) -> Eqn<App<Or, (P, Q)>, True, L> {
        let (p, _, lang) = self.into_parts();
        Eqn::new(App(Or, (p, q)), True, lang)
    }
    /// ∨-introduction (right): from `⊢ P` get `⊢ Q ∨ P`.
    pub fn or_inr<Q: Expr<Ty = bool>>(self, q: Q) -> Eqn<App<Or, (Q, P)>, True, L> {
        let (p, _, lang) = self.into_parts();
        Eqn::new(App(Or, (q, p)), True, lang)
    }
}

impl<P, Q, L: Clone> Eqn<App<And, (P, Q)>, True, L> {
    /// ∧-elimination: deconstruct `⊢ P ∧ Q` into `⊢ P` and `⊢ Q`.
    pub fn and_elim(self) -> (Eqn<P, True, L>, Eqn<Q, True, L>) {
        let (App(_, (p, q)), _, lang) = self.into_parts();
        (Eqn::new(p, True, lang.clone()), Eqn::new(q, True, lang))
    }
}

impl<P: Eq, Q, L: Language> Eqn<App<Imp, (P, Q)>, True, L> {
    /// Modus ponens: from `⊢ P ⟹ Q` and `⊢ P` get `⊢ Q`, under the **union** of the
    /// contexts. `None` if the antecedent does not match (`P: Eq`) or the contexts
    /// cannot be combined.
    pub fn mp(self, p: Eqn<P, True, L>) -> Option<Eqn<Q, True, L>> {
        let (App(_, (ante, q)), _, l1) = self.into_parts();
        let (p_val, _, l2) = p.into_parts();
        if ante != p_val {
            return None;
        }
        let lang = l1.union(l2)?;
        Some(Eqn::new(q, True, lang))
    }
}

impl<A: Expr, B: Expr<Ty = A::Ty>, L> Eqn<A, B, L> {
    /// **Internalize** an equality certificate into a bool proposition: `a = b`
    /// becomes `⊢ (a =_S b)` (`App<EqOp<S>, (a, b)> = ⊤`).
    pub fn internalize(self) -> Eqn<App<EqOp<A::Ty>, (A, B)>, True, L> {
        let (a, b, lang) = self.into_parts();
        Eqn::new(App(EqOp::new(), (a, b)), True, lang)
    }
}

impl<S, A, B, L> Eqn<App<EqOp<S>, (A, B)>, True, L> {
    /// **Reflect** a bool equality proposition back to a certificate: `⊢ (a =_S b)`
    /// recovers `a = b`.
    pub fn reflect(self) -> Eqn<A, B, L> {
        let (App(_, (a, b)), _, lang) = self.into_parts();
        Eqn::new(a, b, lang)
    }
}
