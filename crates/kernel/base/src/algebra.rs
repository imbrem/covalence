//! # `covalence_pure::algebra` — the certificate algebra, abstracted (SKETCH)
//!
//! A non-invasive trait capturing **what any base implementation must
//! provide** to host the kernel tower above it: an unforgeable certificate
//! type plus three capability groups —
//!
//! 1. **mint-by-admitted-rule** ([`CertificateAlgebra::apply`]/
//!    [`apply0`](CertificateAlgebra::apply0)/[`canon`](CertificateAlgebra::canon)):
//!    the only way outside trust enters, gated on [`Language::admits`];
//! 2. **equality transport** ([`refl`](CertificateAlgebra::refl)/
//!    [`sym`](CertificateAlgebra::sym)/[`trans`](CertificateAlgebra::trans)/
//!    [`eq_mp`](CertificateAlgebra::eq_mp)/[`cong_app`](CertificateAlgebra::cong_app)/
//!    [`cong_pair`](CertificateAlgebra::cong_pair)/[`lift`](CertificateAlgebra::lift)):
//!    the ungated calculus, sound in every language;
//! 3. **positive relation facts** ([`execute`](CertificateAlgebra::execute)/
//!    [`transpose`](CertificateAlgebra::transpose)/
//!    [`compose`](CertificateAlgebra::compose)): observed graph membership and
//!    its recombination — never negation.
//!
//! The trait is **generic over the certificate** (the GAT
//! [`CertificateAlgebra::Thm`]) but shares the proposition *vocabulary*
//! ([`Expr`]/[`Op`]/[`App`]/[`Val`]/[`Eqn`] and the sealed grammar) and the
//! trust *enumeration* ([`Language`]/[`Rule`]/[`CanonRule`]) with the concrete
//! base: those are the narrow waist the whole tower states its propositions
//! in, not an implementation detail of this base (see the CONTRACT in
//! [`crate::api`]).
//!
//! **Status: sketch.** Implemented for [`EqnKernel`] (the current closed-world
//! equality kernel — every method a one-line delegation, so the impl is
//! trivially faithful) and exercised by `tests/algebra.rs`. It is NOT yet
//! consumed by `covalence-core`: migrating core's mint macro / seam onto the
//! trait is deliberately deferred until the in-flight core work merges
//! (`notes/vibes/base-abstraction.md` §4).
//!
//! ## How the future relations base implements this same trait
//!
//! The planned refactor (`notes/vibes/base-relcalc-holomega-design.md`,
//! roadmap Fronts D/E) makes **untrusted relation evaluation the only
//! computation** and axioms **simple propositions** of the shape
//! `Computation(i, o) ⟹ SomeRelation(i, o)`. A `RelKernel: CertificateAlgebra`
//! would provide:
//!
//! - `Thm<L, P>` — the same unforgeable-certificate role; its sole primitive
//!   mint is [`execute`](crate::execute)-style **positive graph membership**
//!   (`rel.rs`: run the untrusted `f`, observe `(a, b)`, mint
//!   `⊢ (a, b) ∈ Rel(f)` — sound for *any* `f`, even nondeterministic).
//! - `apply` — instantiation of an **admitted axiom schema** (Front E): the
//!   rule's conclusion is produced by instantiating a schematic proposition
//!   admitted in `tree(L)`, rather than by a trusted `decide` body. Same
//!   gate (`admits` on the rule's own `TypeId`), same signature.
//! - `canon` — **derived, not primitive**: wrap the op as an untrusted
//!   function (`LiftFn<F: CanonRule>`, roadmap Front D Part 1), `execute` it
//!   to get `⊢ (a, b) ∈ Rel(LiftFn(f))`, then discharge the admitted
//!   functionality axiom `∀ i o. Rel(LiftFn(f))(i, o) ⟹ (f(i) = o)` via
//!   instantiate + `mp` to land the same `Eqn` conclusion this trait's
//!   signature promises. The axiom's soundness (that `f` really is a
//!   function) is the language author's declared burden — exactly the shape
//!   "axioms statable as simple propositions involving these relations".
//! - transport — unchanged: `refl`/`sym`/`trans`/`eq_mp`/`cong` are sound in
//!   every model and independent of where mints come from.
//! - `execute`/`transpose`/`compose` — the primitives, verbatim.
//!
//! Consequence: a consumer written against `CertificateAlgebra` (plus the
//! shared vocabulary) cannot observe which base it is on — which is the
//! abstraction the severe refactor needs.

// Same rationale as the trusted crate root: certificate signatures are
// inherently rich; aliasing them would obscure the algebra, not clarify it.
#![allow(clippy::type_complexity)]

use std::sync::Arc;

use covalence_pure_trusted::{
    App, CanonRule, Compose, Eqn, Error, Expr, Language, Op, Ref, Rel, Rule, Thm, Transpose,
    UntrustedFn, Val,
};

/// The certificate algebra any base must provide. See the module docs for the
/// three capability groups and the relations-base implementation story.
///
/// `Self` is a **carrier marker** for the implementation (a ZST naming "which
/// base"), not a value with state: all methods are associated functions, so a
/// consumer names the base once (`B::apply(..)`) and is otherwise generic.
pub trait CertificateAlgebra {
    /// The unforgeable certificate `⊢ P` in language `L`. The implementor
    /// guarantees: no public constructor, every mint audited, and every value
    /// of this type derivable from `tree(L)` + the universal calculus.
    type Thm<L: Language, P: Expr<Ty = bool>>;

    /// The (non-trust-bearing) failure type of gated mints and transport.
    type Error;

    // ---- Group 1: mint-by-admitted-rule (gated) ----

    /// Apply a general [`Rule`], gated on the rule's own `TypeId` being
    /// admitted by `lang`. The sole path by which per-language trust mints.
    fn apply<L: Language, Rho: Rule<L>>(
        lang: L,
        rho: Rho,
        input: Rho::Input,
    ) -> Result<Self::Thm<L, Rho::Concl>, Self::Error>;

    /// [`apply`](Self::apply) for a nullary-axiom rule.
    fn apply0<L: Language, Rho: Rule<L, Input = ()>>(
        lang: L,
        rho: Rho,
    ) -> Result<Self::Thm<L, Rho::Concl>, Self::Error> {
        Self::apply(lang, rho, ())
    }

    /// Evaluate an op to its canonical value: `⊢ f(a) = eval(f, a)`, gated on
    /// `F`'s `TypeId`. In the current base this is a primitive; in the
    /// relations base it becomes *derived* (execute + admitted functionality
    /// axiom — see the module docs), behind the same signature.
    fn canon<L: Language, F: CanonRule>(
        f: F,
        arg: F::In,
        lang: L,
    ) -> Result<Self::Thm<L, Eqn<App<F, Val<F::In>>, Val<F::Out>>>, Self::Error>;

    // ---- Group 2: equality transport (ungated; sound in every language) ----

    /// Read the proven proposition (reading never mints).
    fn prop<L: Language, P: Expr<Ty = bool>>(t: &Self::Thm<L, P>) -> &P;

    /// Reflexivity `⊢ a = a` (leaf equality is defined by `Clone`/`Eq`).
    fn refl<L: Language, A: Expr + Clone>(e: A, lang: L) -> Self::Thm<L, Eqn<A, A>>;

    /// Symmetry: `⊢ a = b` gives `⊢ b = a`.
    fn sym<L: Language, A: Expr, B: Expr<Ty = A::Ty>>(
        t: Self::Thm<L, Eqn<A, B>>,
    ) -> Self::Thm<L, Eqn<B, A>>;

    /// Transitivity through a structurally-`Eq` middle, under the union of
    /// contexts.
    fn trans<L: Language, A, B, C>(
        ab: Self::Thm<L, Eqn<A, B>>,
        bc: Self::Thm<L, Eqn<B, C>>,
    ) -> Result<Self::Thm<L, Eqn<A, C>>, Self::Error>
    where
        A: Expr,
        B: Expr<Ty = A::Ty> + Eq,
        C: Expr<Ty = A::Ty>;

    /// Equality modus ponens (Leibniz): `⊢ P` and `⊢ P = Q` give `⊢ Q`.
    fn eq_mp<L: Language, P: Expr<Ty = bool> + Eq, Q: Expr<Ty = bool>>(
        p: Self::Thm<L, P>,
        eq: Self::Thm<L, Eqn<P, Q>>,
    ) -> Option<Self::Thm<L, Q>>;

    /// Congruence in the argument under any op `F`.
    fn cong_app<L: Language, F, A, A2>(
        t: Self::Thm<L, Eqn<A, A2>>,
        f: F,
    ) -> Self::Thm<L, Eqn<App<F, A>, App<F, A2>>>
    where
        F: Op + Clone,
        A: Expr<Ty = F::In>,
        A2: Expr<Ty = F::In>;

    /// Pair congruence, under the union of contexts.
    fn cong_pair<L: Language, A, A2, B, B2>(
        ab: Self::Thm<L, Eqn<A, A2>>,
        cd: Self::Thm<L, Eqn<B, B2>>,
    ) -> Result<Self::Thm<L, Eqn<(A, B), (A2, B2)>>, Self::Error>
    where
        A: Expr,
        A2: Expr<Ty = A::Ty>,
        B: Expr,
        B2: Expr<Ty = B::Ty>;

    /// Re-home a theorem into a language that directly `extends` its own
    /// (`tree(L2) ⊆ tree(L)` — weakening, adds no strength).
    fn lift<L2: Language, L: Language, P: Expr<Ty = bool>>(
        t: Self::Thm<L2, P>,
        into: L,
    ) -> Result<Self::Thm<L, P>, Self::Error>;

    // ---- Group 3: positive relation facts (the relations-base primitives) ----

    /// Run the untrusted relation and mint the **observed** positive
    /// membership `⊢ (a, b) ∈ Rel(f)`, gated on `Rel<F>`'s `TypeId`. Sound for
    /// any `f`; can never mint `¬(a R b)` (the standing positive-only
    /// invariant — see `rel.rs` and the base SKELETONS).
    fn execute<L: Language, F: UntrustedFn>(
        rel: Rel<F>,
        a: F::In,
        lang: L,
    ) -> Result<Self::Thm<L, App<Rel<F>, (Ref<Arc<F::In>>, Ref<Arc<F::Out>>)>>, Self::Error>
    where
        F::In: 'static,
        F::Out: 'static;

    /// Transpose a positive membership: `⊢ a R b` gives `⊢ b R° a` (ungated,
    /// recombination only).
    fn transpose<L: Language, R, A, B, X, Y>(
        t: Self::Thm<L, App<R, (A, B)>>,
    ) -> Self::Thm<L, App<Transpose<R>, (B, A)>>
    where
        R: Op<In = (X, Y), Out = bool>,
        A: Expr<Ty = X>,
        B: Expr<Ty = Y>,
        X: 'static,
        Y: 'static;

    /// Compose positive memberships through an `Eq`-matched middle:
    /// `⊢ a R b` and `⊢ b S c` give `⊢ a (R;S) c` (ungated, recombination
    /// only), under the union of contexts.
    fn compose<L: Language, R, S, A, B, C, X, Y, Z>(
        ab: Self::Thm<L, App<R, (A, B)>>,
        bc: Self::Thm<L, App<S, (B, C)>>,
    ) -> Result<Self::Thm<L, App<Compose<R, S>, (A, C)>>, Self::Error>
    where
        R: Op<In = (X, Y), Out = bool>,
        S: Op<In = (Y, Z), Out = bool>,
        A: Expr<Ty = X>,
        B: Expr<Ty = Y> + Eq,
        C: Expr<Ty = Z>,
        X: 'static,
        Y: 'static,
        Z: 'static;
}

/// The current base: the closed-world **equality kernel**
/// (`covalence-pure-trusted`). Every method is a one-line delegation to the
/// audited concrete operation, so this impl adds no trust surface — the
/// trait lives in the untrusted facade crate and cannot reach `Thm::new`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct EqnKernel;

impl CertificateAlgebra for EqnKernel {
    type Thm<L: Language, P: Expr<Ty = bool>> = Thm<L, P>;
    type Error = Error;

    fn apply<L: Language, Rho: Rule<L>>(
        lang: L,
        rho: Rho,
        input: Rho::Input,
    ) -> Result<Thm<L, Rho::Concl>, Error> {
        covalence_pure_trusted::apply(lang, rho, input)
    }

    fn canon<L: Language, F: CanonRule>(
        f: F,
        arg: F::In,
        lang: L,
    ) -> Result<Thm<L, Eqn<App<F, Val<F::In>>, Val<F::Out>>>, Error> {
        covalence_pure_trusted::canon(f, arg, lang)
    }

    fn prop<L: Language, P: Expr<Ty = bool>>(t: &Thm<L, P>) -> &P {
        t.prop()
    }

    fn refl<L: Language, A: Expr + Clone>(e: A, lang: L) -> Thm<L, Eqn<A, A>> {
        Thm::refl(e, lang)
    }

    fn sym<L: Language, A: Expr, B: Expr<Ty = A::Ty>>(t: Thm<L, Eqn<A, B>>) -> Thm<L, Eqn<B, A>> {
        t.sym()
    }

    fn trans<L: Language, A, B, C>(
        ab: Thm<L, Eqn<A, B>>,
        bc: Thm<L, Eqn<B, C>>,
    ) -> Result<Thm<L, Eqn<A, C>>, Error>
    where
        A: Expr,
        B: Expr<Ty = A::Ty> + Eq,
        C: Expr<Ty = A::Ty>,
    {
        ab.trans(bc)
    }

    fn eq_mp<L: Language, P: Expr<Ty = bool> + Eq, Q: Expr<Ty = bool>>(
        p: Thm<L, P>,
        eq: Thm<L, Eqn<P, Q>>,
    ) -> Option<Thm<L, Q>> {
        p.eq_mp(eq)
    }

    fn cong_app<L: Language, F, A, A2>(
        t: Thm<L, Eqn<A, A2>>,
        f: F,
    ) -> Thm<L, Eqn<App<F, A>, App<F, A2>>>
    where
        F: Op + Clone,
        A: Expr<Ty = F::In>,
        A2: Expr<Ty = F::In>,
    {
        t.cong_app(f)
    }

    fn cong_pair<L: Language, A, A2, B, B2>(
        ab: Thm<L, Eqn<A, A2>>,
        cd: Thm<L, Eqn<B, B2>>,
    ) -> Result<Thm<L, Eqn<(A, B), (A2, B2)>>, Error>
    where
        A: Expr,
        A2: Expr<Ty = A::Ty>,
        B: Expr,
        B2: Expr<Ty = B::Ty>,
    {
        ab.cong_pair(cd)
    }

    fn lift<L2: Language, L: Language, P: Expr<Ty = bool>>(
        t: Thm<L2, P>,
        into: L,
    ) -> Result<Thm<L, P>, Error> {
        t.lift(into)
    }

    fn execute<L: Language, F: UntrustedFn>(
        rel: Rel<F>,
        a: F::In,
        lang: L,
    ) -> Result<Thm<L, App<Rel<F>, (Ref<Arc<F::In>>, Ref<Arc<F::Out>>)>>, Error>
    where
        F::In: 'static,
        F::Out: 'static,
    {
        covalence_pure_trusted::execute(rel, a, lang)
    }

    fn transpose<L: Language, R, A, B, X, Y>(
        t: Thm<L, App<R, (A, B)>>,
    ) -> Thm<L, App<Transpose<R>, (B, A)>>
    where
        R: Op<In = (X, Y), Out = bool>,
        A: Expr<Ty = X>,
        B: Expr<Ty = Y>,
        X: 'static,
        Y: 'static,
    {
        t.transpose()
    }

    fn compose<L: Language, R, S, A, B, C, X, Y, Z>(
        ab: Thm<L, App<R, (A, B)>>,
        bc: Thm<L, App<S, (B, C)>>,
    ) -> Result<Thm<L, App<Compose<R, S>, (A, C)>>, Error>
    where
        R: Op<In = (X, Y), Out = bool>,
        S: Op<In = (Y, Z), Out = bool>,
        A: Expr<Ty = X>,
        B: Expr<Ty = Y> + Eq,
        C: Expr<Ty = Z>,
        X: 'static,
        Y: 'static,
        Z: 'static,
    {
        ab.compose(bc)
    }
}
