//! **Bool theory** — part of every language's equational core.
//!
//! The propositional connectives (`And`/`Or`/`Imp`/`Not`) are ops; their logic is
//! **ungated builtin methods** on [`Thm`] (sound in *every* language, like the
//! equality calculus — propositional logic is valid in any model). A theorem
//! `Thm<L, P>` (`P: Expr<Ty = bool>`) supports: deconstructing an `And`, injecting
//! into an `Or`, and modus ponens for `Imp`.
//!
//! These methods are a minting site (besides the [`crate::eqn`] calculus, the
//! [`crate::eq`] `decide`, and [`crate::matching`] `apply_rewrite`); all go through
//! the `pub(crate)` [`Thm::new`].

use crate::eqn::Thm;
use crate::expr::{App, Expr};
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

// ---- Builtin propositional logic (ungated; sound in every language) ----

impl<L: Language, P: Expr<Ty = bool>> Thm<L, P> {
    /// ∧-introduction: from `⊢ P` and `⊢ Q` get `⊢ P ∧ Q`, under the **union** of
    /// the two contexts. `None` if the contexts cannot be combined.
    pub fn and_intro<Q: Expr<Ty = bool>>(
        self,
        other: Thm<L, Q>,
    ) -> Option<Thm<L, App<And, (P, Q)>>> {
        let (l1, p) = self.into_parts();
        let (l2, q) = other.into_parts();
        let lang = l1.union(l2)?;
        Some(Thm::new(lang, App(And, (p, q))))
    }
}

impl<L, P: Expr<Ty = bool>> Thm<L, P> {
    /// ∨-introduction (left): from `⊢ P` get `⊢ P ∨ Q` for any `Q` (you supply the
    /// other disjunct expression).
    pub fn or_inl<Q: Expr<Ty = bool>>(self, q: Q) -> Thm<L, App<Or, (P, Q)>> {
        let (lang, p) = self.into_parts();
        Thm::new(lang, App(Or, (p, q)))
    }
    /// ∨-introduction (right): from `⊢ P` get `⊢ Q ∨ P`.
    pub fn or_inr<Q: Expr<Ty = bool>>(self, q: Q) -> Thm<L, App<Or, (Q, P)>> {
        let (lang, p) = self.into_parts();
        Thm::new(lang, App(Or, (q, p)))
    }
}

impl<L: Clone, P: Expr<Ty = bool>, Q: Expr<Ty = bool>> Thm<L, App<And, (P, Q)>> {
    /// ∧-elimination: deconstruct `⊢ P ∧ Q` into `⊢ P` and `⊢ Q`.
    pub fn and_elim(self) -> (Thm<L, P>, Thm<L, Q>) {
        let (lang, App(_, (p, q))) = self.into_parts();
        (Thm::new(lang.clone(), p), Thm::new(lang, q))
    }
}

impl<L: Language, P: Expr<Ty = bool> + Eq, Q: Expr<Ty = bool>> Thm<L, App<Imp, (P, Q)>> {
    /// Modus ponens: from `⊢ P ⟹ Q` and `⊢ P` get `⊢ Q`, under the **union** of the
    /// contexts. `None` if the antecedent does not match (`P: Eq`) or the contexts
    /// cannot be combined.
    pub fn mp(self, p: Thm<L, P>) -> Option<Thm<L, Q>> {
        let (l1, App(_, (ante, q))) = self.into_parts();
        let (l2, p_val) = p.into_parts();
        if ante != p_val {
            return None;
        }
        let lang = l1.union(l2)?;
        Some(Thm::new(lang, q))
    }
}
