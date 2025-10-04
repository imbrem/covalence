use crate::term::{Bv, GNode, Import, ULvl};

/// A trait implemented by a datastore that can manipulate hash-consed terms and universe levels
pub trait TermStore<C, T> {
    /// Insert a term into the store, returning a handle to it
    fn add(&mut self, ctx: C, term: GNode<C, T>) -> T;

    /// Get the node corresponding to a term
    fn node(&self, ctx: C, term: T) -> &GNode<C, T>;

    /// Lookup a term in the store
    ///
    /// Canonicalizes the term's children if found
    fn lookup(&self, ctx: C, term: &mut GNode<C, T>) -> Option<T>;

    /// Get the head variable of a context, if any
    fn head(&self, ctx: C) -> Option<T>;

    /// Get the successor of a given universe level
    fn succ(&mut self, level: ULvl) -> ULvl;

    /// Get the maximum of two universe levels
    fn umax(&mut self, lhs: ULvl, rhs: ULvl) -> ULvl;

    /// Get the impredicatibe maximum of two universe levels
    fn imax(&mut self, lhs: ULvl, rhs: ULvl) -> ULvl;
}

/// A trait implemented by a datastore that can read facts about terms in a context.
pub trait ReadFacts<C, T> {
    // == Syntax information ==
    /// Get a bound on the de-Bruijn indices visible in `tm`
    fn bvi(&self, ctx: C, tm: T) -> Bv;

    // == Context information ==
    /// Check whether `lo` is a prefix of `hi`
    fn ctx_prefix(&self, lo: C, hi: C) -> bool;

    // == Predicates ==
    /// Check whether the term `tm` is well-formed in `ctx`
    /// Corresponds to `Ctx.KIsWf` in `gt3-lean`
    fn is_wf(&self, ctx: C, tm: T) -> bool;

    /// Check whether the term `tm` is a type in the context `ctx`
    ///
    /// Corresponds to `Ctx.KIsTy` in `gt3-lean`
    fn is_ty(&self, ctx: C, tm: T) -> bool;

    /// Check whether the term `tm` is an inhabited type in the context `ctx`
    ///
    /// Corresponds to `Ctx.KIsInhab` in `gt3-lean`
    fn is_inhab(&self, ctx: C, tm: T) -> bool;

    /// Check whether the term `tm` is a proposition in the context `ctx`
    ///
    /// Corresponds to `Ctx.KIsProp` in `gt3-lean`
    fn is_prop(&self, ctx: C, tm: T) -> bool;

    // == Relations ==
    /// Check whether the term `lhs` in `lctx` is _syntactically_ equal to the term `rhs` in `rctx`
    fn syn_eq(&self, lctx: C, lhs: T, rctx: C, rhs: T) -> bool;

    /// Check whether the term `lhs` is equal to the term `rhs` in `ctx`
    ///
    /// Corresponds to `Ctx.KEq` in `gt3-lean`
    fn eq_in(&self, ctx: C, lhs: T, rhs: T) -> bool;

    /// Check whether the term `tm` has type `ty` in `ctx`
    ///
    /// Corresponds to `Ctx.KHasTy` in `gt3-lean`
    fn has_ty(&self, ctx: C, tm: T, ty: T) -> bool;

    /// Check whether the term `tm` is a valid type in `ctx` under a binder `binder`
    ///
    /// Corresponds to `Ctx.KIsTyUnder` in `gt3-lean`
    fn is_ty_under(&self, ctx: C, binder: T, tm: T) -> bool;

    /// Check whether the term `tm` has type `ty` in `ctx` under a binder `binder`
    ///
    /// Corresponds to `Ctx.KHasTyUnder` in `gt3-lean`
    fn has_ty_under(&self, ctx: C, binder: T, tm: T, ty: T) -> bool;

    // == Universe levels ==
    /// Check whether one universe is less than or equal to another
    fn u_le(&self, lo: ULvl, hi: ULvl) -> bool;

    /// Check whether one universe is strictly less than another
    fn u_lt(&self, lo: ULvl, hi: ULvl) -> bool;

    /// Check whether the impredicative maximum of two universes is less than or equal to another
    fn imax_le(&self, lo_lhs: ULvl, lo_rhs: ULvl, hi: ULvl) -> bool;
}

/// A trait implemented by a mutable datastore that can hold _unchecked_ facts about terms in a
/// context.
pub trait WriteFacts<C, T> {
    // == Predicates ==
    /// Mark a term as well-formed
    fn set_is_wf_unchecked(&mut self, ctx: C, tm: T);

    /// Mark a term as a type
    fn set_is_ty_unchecked(&mut self, ctx: C, tm: T);

    /// Mark a term as an inhabited type
    fn set_is_inhab_unchecked(&mut self, ctx: C, tm: T);

    /// Mark a term as a proposition
    fn set_is_prop_unchecked(&mut self, ctx: C, tm: T);

    // == Relations ==
    /// Set two terms as equal in a given context
    fn set_eq_unchecked(&mut self, ctx: C, lhs: T, rhs: T);

    /// Set the type of a term
    fn set_ty_unchecked(&mut self, ctx: C, tm: T, ty: T);

    /// Mark a term as a valid type under a binder
    fn set_is_ty_under_unchecked(&mut self, ctx: C, binder: T, tm: T);

    /// Set the type of a term under a binder
    fn set_ty_under_unchecked(&mut self, ctx: C, binder: T, tm: T, ty: T);
}

/// A typing derivation in a given context
pub struct HasTyIn<T> {
    pub tm: T,
    pub ty: T,
}

/// A typing derivation in a given context under a binder
pub struct HasTyUnderIn<T> {
    pub binder: T,
    pub tm: T,
    pub ty: T,
}

/// A statement of well-formedness
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct IsWf<C, T> {
    pub ctx: C,
    pub tm: T,
}

/// A term is a valid type
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct IsTy<C, T> {
    pub ctx: C,
    pub tm: T,
}

/// A term is an inhabited type
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct IsInhab<C, T> {
    pub ctx: C,
    pub tm: T,
}

/// A term is a proposition
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct IsProp<C, T> {
    pub ctx: C,
    pub tm: T,
}

/// A typing derivation
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct HasTy<C, T> {
    pub ctx: C,
    pub tm: T,
    pub ty: T,
}

/// A term is a type under a binder
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct IsTyUnder<C, T> {
    pub ctx: C,
    pub binder: T,
    pub tm: T,
}

/// A typing derivation under a binder
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct HasTyUnder<C, T> {
    pub ctx: C,
    pub binder: T,
    pub tm: T,
    pub ty: T,
}

/// Equality in a context
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct EqIn<C, T> {
    pub ctx: C,
    pub lhs: T,
    pub rhs: T,
}

/// A goal for a strategy
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub enum Goal<C, T> {
    IsWf(IsWf<C, T>),
    IsTy(IsTy<C, T>),
    IsInhab(IsInhab<C, T>),
    IsProp(IsProp<C, T>),
    HasTy(HasTy<C, T>),
    IsTyUnder(IsTyUnder<C, T>),
    HasTyUnder(HasTyUnder<C, T>),
    EqIn(EqIn<C, T>),
}

impl<C, T> From<IsWf<C, T>> for Goal<C, T> {
    fn from(g: IsWf<C, T>) -> Self {
        Goal::IsWf(g)
    }
}

impl<C, T> From<IsTy<C, T>> for Goal<C, T> {
    fn from(g: IsTy<C, T>) -> Self {
        Goal::IsTy(g)
    }
}

impl<C, T> From<IsInhab<C, T>> for Goal<C, T> {
    fn from(g: IsInhab<C, T>) -> Self {
        Goal::IsInhab(g)
    }
}

impl<C, T> From<IsProp<C, T>> for Goal<C, T> {
    fn from(g: IsProp<C, T>) -> Self {
        Goal::IsProp(g)
    }
}

impl<C, T> From<HasTy<C, T>> for Goal<C, T> {
    fn from(g: HasTy<C, T>) -> Self {
        Goal::HasTy(g)
    }
}

impl<C, T> From<IsTyUnder<C, T>> for Goal<C, T> {
    fn from(g: IsTyUnder<C, T>) -> Self {
        Goal::IsTyUnder(g)
    }
}

impl<C, T> From<HasTyUnder<C, T>> for Goal<C, T> {
    fn from(g: HasTyUnder<C, T>) -> Self {
        Goal::HasTyUnder(g)
    }
}

impl<C, T> From<EqIn<C, T>> for Goal<C, T> {
    fn from(g: EqIn<C, T>) -> Self {
        Goal::EqIn(g)
    }
}

impl<C, T> Goal<C, T> {
    /// Check whether this goal is true
    pub fn check(self, ker: &impl ReadFacts<C, T>) -> bool {
        match self {
            Goal::IsWf(g) => ker.is_wf(g.ctx, g.tm),
            Goal::IsTy(g) => ker.is_ty(g.ctx, g.tm),
            Goal::IsInhab(g) => ker.is_inhab(g.ctx, g.tm),
            Goal::IsProp(g) => ker.is_prop(g.ctx, g.tm),
            Goal::HasTy(g) => ker.has_ty(g.ctx, g.tm, g.ty),
            Goal::IsTyUnder(g) => ker.is_ty_under(g.ctx, g.binder, g.tm),
            Goal::HasTyUnder(g) => ker.has_ty_under(g.ctx, g.binder, g.tm, g.ty),
            Goal::EqIn(g) => ker.eq_in(g.ctx, g.lhs, g.rhs),
        }
    }
}

/// A strategy tells a kernel how to derive facts about terms in a context
pub trait Strategy<C, T, K> {
    /// The type returned by the strategy on failure
    type Fail;

    /// Attempt to prove a goal
    fn prove_goal(
        &mut self,
        ker: &mut K,
        goal: Goal<C, T>,
        msg: &'static str,
        attempt_no: usize,
    ) -> Result<(), Self::Fail>;

    /// Called when the top goal in the stack has failed
    ///
    /// This is usually called by returning an `Err` from `prove_has_ty`, but might be called on
    /// continue due to a wrapping strategy triggering the failure.
    fn on_failure(&mut self, _goal: Goal<C, T>, _err: Option<&mut Self::Fail>) {}

    /// Called when the top goal in the stack has succeeded
    fn on_success(&mut self, _goal: Goal<C, T>) {}

    /// An irrecoverable failure from a derivation
    fn fail(msg: &'static str) -> Self::Fail;
}

impl<C, T, K> Strategy<C, T, K> for () {
    type Fail = ();

    fn prove_goal(
        &mut self,
        _ker: &mut K,
        _goal: Goal<C, T>,
        _msg: &'static str,
        _attempt_no: usize,
    ) -> Result<(), Self::Fail> {
        Err(())
    }

    fn fail(_msg: &'static str) -> Self::Fail {
        ()
    }
}

pub trait Ensure<C: Copy, T: Copy>: Sized + ReadFacts<C, T> {
    /// Attempt to prove a goal
    fn ensure_goal<S>(
        &mut self,
        goal: Goal<C, T>,
        strategy: &mut S,
        msg: &'static str,
    ) -> Result<(), S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        let mut attempt_no = 0;
        while !goal.check(self) {
            strategy
                .prove_goal(self, goal, msg, attempt_no)
                .map_err(|mut err| {
                    strategy.on_failure(goal, Some(&mut err));
                    err
                })?;
            attempt_no += 1;
        }
        strategy.on_success(goal);
        Ok(())
    }

    /// Attempt to prove that a term is well-formed in a context
    fn ensure_is_wf<S>(
        &mut self,
        ctx: C,
        tm: T,
        strategy: &mut S,
        msg: &'static str,
    ) -> Result<(), S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        self.ensure_goal(IsWf { ctx, tm }.into(), strategy, msg)
    }

    /// Attempt to prove that a term is a type in a context
    fn ensure_is_ty<S>(
        &mut self,
        ctx: C,
        tm: T,
        strategy: &mut S,
        msg: &'static str,
    ) -> Result<(), S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        self.ensure_goal(IsTy { ctx, tm }.into(), strategy, msg)
    }

    /// Attempt to prove that a term is an inhabited type in a context
    fn ensure_is_inhab<S>(
        &mut self,
        ctx: C,
        tm: T,
        strategy: &mut S,
        msg: &'static str,
    ) -> Result<(), S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        self.ensure_goal(IsInhab { ctx, tm }.into(), strategy, msg)
    }

    /// Attempt to prove that a term is a proposition in a context
    fn ensure_is_prop<S>(
        &mut self,
        ctx: C,
        tm: T,
        strategy: &mut S,
        msg: &'static str,
    ) -> Result<(), S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        self.ensure_goal(IsProp { ctx, tm }.into(), strategy, msg)
    }

    /// Attempt to prove that a term has a given type in a context
    fn ensure_has_ty<S>(
        &mut self,
        ctx: C,
        tm: T,
        ty: T,
        strategy: &mut S,
        msg: &'static str,
    ) -> Result<(), S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        self.ensure_goal(HasTy { ctx, tm, ty }.into(), strategy, msg)
    }

    /// Attempt to prove that a term is a type in a context under a binder
    fn ensure_is_ty_under<S>(
        &mut self,
        ctx: C,
        binder: T,
        tm: T,
        strategy: &mut S,
        msg: &'static str,
    ) -> Result<(), S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        self.ensure_goal(IsTyUnder { ctx, binder, tm }.into(), strategy, msg)
    }

    /// Attempt to prove that a term has a given type in a context under a binder
    fn ensure_has_ty_under<S>(
        &mut self,
        ctx: C,
        binder: T,
        tm: T,
        ty: T,
        strategy: &mut S,
        msg: &'static str,
    ) -> Result<(), S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        self.ensure_goal(
            HasTyUnder {
                ctx,
                binder,
                tm,
                ty,
            }
            .into(),
            strategy,
            msg,
        )
    }
}

impl<C, T, K> Ensure<C, T> for K
where
    C: Copy,
    T: Copy,
    K: ReadFacts<C, T> + Sized,
{
}

/// Typing rules for deriving facts about terms from those already in the datastore
pub trait Derive<C, T>: Sized {
    /// Compute the substitution of a term
    ///
    /// Given terms `bound` and `body`
    /// - If `body` is locally-closed, return it unchanged
    /// - Otherwise, `let bound in body`
    fn lazy_subst(&mut self, ctx: C, bound: T, body: T) -> T;

    /// Typecheck a variable
    ///
    /// Corresponds to the rule
    /// ```text
    /// Γ ok
    /// Γ(x) = A
    /// ===
    /// Γ ⊢ x : A
    /// ```
    /// or, in Lean,
    /// ```lean
    /// theorem Ctx.KHasTy.fv {Γ x A} (hΓ : Ok Γ) (hA : Lookup Γ x A) : KHasTy Γ A.erase (.fv x)
    /// ```
    fn derive_fv<S>(&mut self, ctx: C, var: C) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Typecheck a typing universe
    ///
    /// Corresponds to the rule
    /// ```text
    /// Γ ok
    /// ===
    /// Γ ⊢ U_ℓ : U_(ℓ + 1)
    /// ```
    /// or, in Lean,
    /// ```lean
    /// theorem Ctx.KHasTy.univ {Γ ℓ} (h : Ok Γ) : KHasTy Γ (.univ (ℓ + 1)) (.univ ℓ)
    /// ```
    fn derive_univ(&mut self, ctx: C, lvl: ULvl) -> HasTyIn<T>;

    /// Typecheck the unit type
    ///
    /// Corresponds to the rule
    /// ```text
    /// Γ ok
    /// ===
    /// Γ ⊢ 1 : U_ℓ
    /// ```
    /// or, in Lean,
    /// ```lean
    /// theorem Ctx.KHasTy.unit {Γ ℓ} (h : Ok Γ) : KHasTy Γ (.univ ℓ) .unit
    /// ```
    fn derive_unit(&mut self, ctx: C, lvl: ULvl) -> HasTyIn<T>;

    /// Typecheck the unique value of the unit type
    ///
    /// Corresponds to the rule
    /// ```text
    /// Γ ok
    /// ===
    /// Γ ⊢ * : 1
    /// ```
    /// or, in Lean,
    /// ```lean
    /// theorem Ctx.KHasTy.null {Γ} (h : Ok Γ) : KHasTy Γ .unit .null
    /// ```
    fn derive_nil(&mut self, ctx: C) -> HasTyIn<T>;

    /// Typecheck the unit type
    ///
    /// Corresponds to the rule
    /// ```text
    /// Γ ok
    /// ===
    /// Γ ⊢ 0 : U_ℓ
    /// ```
    /// or, in Lean,
    /// ```lean
    /// theorem Ctx.KHasTy.empty {Γ ℓ} (h : Ok Γ) : KHasTy Γ (.univ ℓ) .empty
    /// ```
    fn derive_empty(&mut self, ctx: C, lvl: ULvl) -> HasTyIn<T>;

    /// Typecheck an equation between terms
    ///
    /// Corresponds to the rule
    /// ```text
    /// Γ ⊢ a : A
    /// Γ ⊢ b : A
    /// ===
    /// Γ ⊢ a = b : 2
    /// ```
    /// or, in Lean,
    /// ```lean
    /// theorem Ctx.KHasTy.eqn
    ///   {Γ A a b} (ha : KHasTy Γ A a) (hb : KHasTy Γ A b)
    ///   : KHasTy Γ (.univ 0) (.eqn a b)
    /// ```
    fn derive_eqn<S>(
        &mut self,
        ctx: C,
        ty: T,
        lhs: T,
        rhs: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Typecheck a pi type
    ///
    /// Corresponds to the rule
    /// ```text
    /// Γ ⊢ A : U_m
    /// ∀x ∉ L . Γ , x : A ⊢ B^x : U_n
    /// imax(m, n) ≤ ℓ
    /// ===
    /// Γ ⊢ Π_ℓ A . B : U_ℓ
    /// ```
    /// or, in Lean,
    /// ```lean
    /// theorem Ctx.KHasTy.pi {Γ A B m n ℓ}
    ///   (hA : KHasTy Γ (.univ m) A) (hB : KHasTyUnder Γ A (.univ n) B)
    ///   (hℓ : m.imax n ≤ ℓ)
    ///   : KHasTy Γ (.univ ℓ) (.pi A B)
    /// ```
    fn derive_pi<S>(
        &mut self,
        ctx: C,
        arg_lvl: ULvl,
        res_lvl: ULvl,
        lvl: ULvl,
        arg_ty: T,
        res_ty: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Typecheck a sigma type
    ///
    /// Corresponds to the rule
    /// ```text
    /// Γ ⊢ A : U_m
    /// ∀x ∉ L . Γ , x : A ⊢ B^x : U_n
    /// m ≤ ℓ
    /// n ≤ ℓ
    /// ===
    /// Γ ⊢ Σ_ℓ A . B : U_ℓ
    /// ```
    /// or, in Lean,
    /// ```lean
    /// theorem Ctx.KHasTy.sigma' {Γ A B m n ℓ}
    ///   (hA : KHasTy Γ (.univ m) A) (hB : KHasTyUnder Γ A (.univ n) B)
    ///   (hm : m ≤ ℓ) (hn : n ≤ ℓ)
    ///   : KHasTy Γ (.univ ℓ) (.sigma A B)
    /// ```
    fn derive_sigma<S>(
        &mut self,
        ctx: C,
        arg_lvl: ULvl,
        res_lvl: ULvl,
        lvl: ULvl,
        arg_ty: T,
        res_ty: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    // TODO: pi_ty

    // TODO: sigma_ty

    /// Typecheck an abstraction
    ///
    /// Corresponds to the rule
    /// ```text
    /// ∀x ∉ L . Γ, x : A ⊢ b^x : B^x
    /// ===
    /// Γ ⊢ λ A . b : Π A . B
    /// ```
    /// or, in Lean,
    /// ```lean
    /// theorem Ctx.KHasTy.abs {Γ A B b}
    ///   (hB : KHasTyUnder Γ A B b) : KHasTy Γ (.pi A B) (.abs A b)
    /// ```
    fn derive_abs<S>(
        &mut self,
        ctx: C,
        arg_ty: T,
        body: T,
        res_ty: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Typecheck an application
    ///
    /// Corresponds to the rule
    /// ```text
    /// Γ ⊢ f : Π A . B
    /// Γ ⊢ a : A
    /// ===
    /// Γ ⊢ f a : B^a
    /// ```
    /// or, in Lean,
    /// ```lean
    /// theorem Ctx.KHasTy.app {Γ A B f a}
    ///   (hA : KHasTy Γ (.pi A B) f) (hB : KHasTy Γ A a) : KHasTy Γ (B.lst 0 a) (.app f a)
    /// ```
    fn derive_app<S>(
        &mut self,
        ctx: C,
        arg_ty: T,
        res_ty: T,
        func: T,
        arg: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Typecheck a pair
    ///
    /// Corresponds to the rule
    /// ```text
    /// ∀x ∉ L . Γ, x : A ⊢ B^x ty
    /// Γ ⊢ a : A
    /// Γ ⊢ b : B^a
    /// ===
    /// Γ ⊢ (a, b) : Σ A . B
    /// ```
    /// or, in Lean,
    /// ```lean
    /// theorem Ctx.KHasTy.pair {Γ A B a b}
    ///   (hB : KIsTyUnder Γ A B) (ha : KHasTy Γ A a) (hb : KHasTy Γ (B.lst 0 a) b)
    /// ```
    fn derive_pair<S>(
        &mut self,
        ctx: C,
        arg_ty: T,
        res_ty: T,
        fst: T,
        snd: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Typecheck the first projection of a pair
    ///
    /// Corresponds to the rule
    /// ```text
    /// Γ ⊢ p : Σ A . B
    /// ===
    /// Γ ⊢ fst p : A
    /// ```
    /// or, in Lean,
    /// ```lean
    /// theorem Ctx.KHasTy.fst {Γ A B p} (hp : KHasTy Γ (.sigma A B) p) : KHasTy Γ A (.fst p)
    /// ```
    fn derive_fst<S>(
        &mut self,
        ctx: C,
        arg_ty: T,
        res_ty: T,
        pair: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Typecheck the second projection of a pair
    ///
    /// Additionally typechecks the first projection using the rule for `fst`
    /// 
    /// Corresponds to the rule
    /// ```text
    /// Γ ⊢ p : Σ A . B
    /// ===
    /// Γ ⊢ snd p : B^(fst p)
    /// + Γ ⊢ fst p : A
    /// ```
    /// or, in Lean,
    /// ```lean
    /// theorem Ctx.KHasTy.snd {Γ A B p} (hp : KHasTy Γ (.sigma A B) p)
    ///   : KHasTy Γ (B.lst 0 (.fst p)) (.snd p)
    /// 
    /// -- Additional results:
    /// theorem Ctx.KHasTy.fst {Γ A B p} (hp : KHasTy Γ (.sigma A B) p) : KHasTy Γ A (.fst p)
    /// ```
    fn derive_snd<S>(
        &mut self,
        ctx: C,
        arg_ty: T,
        res_ty: T,
        pair: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    // TODO: dite

    // TODO: trunc

    // TODO: choose

    // TODO: smallnat

    // TODO: succ

    // TODO: natrec

    // TODO: lst

    // TODO: beta_app

    // TODO: beta_fst

    // TODO: beta_snd

    // TODO: beta_dite_tt

    // TODO: beta_dite_ff

    // TODO: beta_natrec_0

    // TODO: beta_natrec_succ

    // TODO: choose_spec

    // TODO: unit_ext

    // TODO: eqn_ext

    // TODO: pi_ext

    // TODO: sigma_ext

    // TODO: sometime later:
    // - propext
    // - subtyping for sigma
    // - optimization for conjunction
    // - optimization for implication
    // - optimization for composition
    // - sums
    // - optimizations for disjunction
    // - optimizations for negation
    // - binary applications
    // - IF SOUND: beta_dite_same; or incorporate into dite
    // - emptiness lore
    // - subsingleton lore
}

/// The `covalence` kernel
///
/// This type is parametrized by its datastore `D`
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
pub struct Kernel<D>(D);

impl<D> Kernel<D> {
    /// Get an _immutable_ reference to the underlying datastore
    pub fn data(&self) -> &D {
        &self.0
    }
}

impl<C, T, D: ReadFacts<C, T>> ReadFacts<C, T> for Kernel<D> {
    fn bvi(&self, ctx: C, tm: T) -> Bv {
        self.0.bvi(ctx, tm)
    }

    fn ctx_prefix(&self, lo: C, hi: C) -> bool {
        self.0.ctx_prefix(lo, hi)
    }

    fn is_wf(&self, ctx: C, tm: T) -> bool {
        self.0.is_wf(ctx, tm)
    }

    fn is_ty(&self, ctx: C, tm: T) -> bool {
        self.0.is_ty(ctx, tm)
    }

    fn is_inhab(&self, ctx: C, tm: T) -> bool {
        self.0.is_inhab(ctx, tm)
    }

    fn is_prop(&self, ctx: C, tm: T) -> bool {
        self.0.is_prop(ctx, tm)
    }

    fn syn_eq(&self, lctx: C, lhs: T, rctx: C, rhs: T) -> bool {
        self.0.syn_eq(lctx, lhs, rctx, rhs)
    }

    fn eq_in(&self, ctx: C, lhs: T, rhs: T) -> bool {
        self.0.eq_in(ctx, lhs, rhs)
    }

    fn has_ty(&self, ctx: C, tm: T, ty: T) -> bool {
        self.0.has_ty(ctx, tm, ty)
    }

    fn is_ty_under(&self, ctx: C, binder: T, tm: T) -> bool {
        self.0.is_ty_under(ctx, binder, tm)
    }

    fn has_ty_under(&self, ctx: C, binder: T, tm: T, ty: T) -> bool {
        self.0.has_ty_under(ctx, binder, tm, ty)
    }

    fn u_le(&self, lo: ULvl, hi: ULvl) -> bool {
        self.0.u_le(lo, hi)
    }

    fn u_lt(&self, lo: ULvl, hi: ULvl) -> bool {
        self.0.u_lt(lo, hi)
    }

    fn imax_le(&self, lo_lhs: ULvl, lo_rhs: ULvl, hi: ULvl) -> bool {
        self.0.imax_le(lo_lhs, lo_rhs, hi)
    }
}

impl<C, T, D: TermStore<C, T>> TermStore<C, T> for Kernel<D> {
    fn add(&mut self, ctx: C, term: GNode<C, T>) -> T {
        self.0.add(ctx, term)
    }

    fn node(&self, ctx: C, term: T) -> &GNode<C, T> {
        self.0.node(ctx, term)
    }

    fn lookup(&self, ctx: C, term: &mut GNode<C, T>) -> Option<T> {
        self.0.lookup(ctx, term)
    }

    fn head(&self, ctx: C) -> Option<T> {
        self.0.head(ctx)
    }

    fn succ(&mut self, level: ULvl) -> ULvl {
        self.0.succ(level)
    }

    fn umax(&mut self, lhs: ULvl, rhs: ULvl) -> ULvl {
        self.0.umax(lhs, rhs)
    }

    fn imax(&mut self, lhs: ULvl, rhs: ULvl) -> ULvl {
        self.0.imax(lhs, rhs)
    }
}

impl<C: Copy, T: Copy, D: TermStore<C, T> + ReadFacts<C, T> + WriteFacts<C, T>> Derive<C, T>
    for Kernel<D>
{
    fn lazy_subst(&mut self, ctx: C, bound: T, body: T) -> T {
        if self.bvi(ctx, body) == Bv(0) {
            return body;
        }
        self.add(ctx, GNode::Let(Bv(0), [bound, body]))
    }

    fn derive_fv<S>(&mut self, ctx: C, var: C) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        let Some(head) = self.head(var) else {
            return Err(S::fail("derive_fv: var is not a valid variable"));
        };
        if !self.ctx_prefix(var, ctx) {
            return Err(S::fail("derive_fv: variable not in context"));
        }
        debug_assert_eq!(
            self.bvi(var, head),
            Bv(0),
            "head variable should be locally-closed"
        );
        let tm = self.add(ctx, GNode::Fv(var));
        let ty = self.add(
            ctx,
            GNode::Copy(Import {
                ctx: var,
                term: head,
                bvi: Bv(0),
            }),
        );
        self.0.set_ty_unchecked(ctx, tm, ty);
        Ok(HasTyIn { tm, ty })
    }

    fn derive_univ(&mut self, ctx: C, lvl: ULvl) -> HasTyIn<T> {
        let tm = self.add(ctx, GNode::U(lvl));
        let ty_lvl = self.succ(lvl);
        let ty = self.add(ctx, GNode::U(ty_lvl));
        self.0.set_ty_unchecked(ctx, tm, ty);
        HasTyIn { tm, ty }
    }

    fn derive_unit(&mut self, ctx: C, lvl: ULvl) -> HasTyIn<T> {
        let tm = self.add(ctx, GNode::Unit);
        let ty = self.add(ctx, GNode::U(lvl));
        self.0.set_ty_unchecked(ctx, tm, ty);
        HasTyIn { tm, ty }
    }

    fn derive_nil(&mut self, ctx: C) -> HasTyIn<T> {
        let tm = self.add(ctx, GNode::Null);
        let ty = self.add(ctx, GNode::Unit);
        self.0.set_ty_unchecked(ctx, tm, ty);
        HasTyIn { tm, ty }
    }

    fn derive_empty(&mut self, ctx: C, lvl: ULvl) -> HasTyIn<T> {
        let tm = self.add(ctx, GNode::Empty);
        let ty = self.add(ctx, GNode::U(lvl));
        self.0.set_ty_unchecked(ctx, tm, ty);
        HasTyIn { tm, ty }
    }

    fn derive_eqn<S>(
        &mut self,
        ctx: C,
        ty: T,
        lhs: T,
        rhs: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        self.ensure_has_ty(ctx, lhs, ty, strategy, "derive_eqn: lhs")?;
        self.ensure_has_ty(ctx, rhs, ty, strategy, "derive_eqn: rhs")?;
        let tm = self.add(ctx, GNode::Eqn([lhs, rhs]));
        let ty = self.add(ctx, GNode::U(ULvl::PROP));
        self.0.set_ty_unchecked(ctx, tm, ty);
        Ok(HasTyIn { tm, ty })
    }

    fn derive_pi<S>(
        &mut self,
        ctx: C,
        arg_lvl: ULvl,
        res_lvl: ULvl,
        lvl: ULvl,
        arg_ty: T,
        res_ty: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        if self.imax_le(arg_lvl, res_lvl, lvl) {
            return Err(S::fail(
                "derive_pi: cannot deduce that imax(arg_lvl, res_lvl) ≤ lvl",
            ));
        }
        let arg_lvl_ty = self.add(ctx, GNode::U(arg_lvl));
        let res_lvl_ty = self.add(ctx, GNode::U(res_lvl));
        self.ensure_has_ty(ctx, arg_ty, arg_lvl_ty, strategy, "derive_pi: arg_ty")?;
        self.ensure_has_ty_under(
            ctx,
            arg_ty,
            res_ty,
            res_lvl_ty,
            strategy,
            "derive_pi: res_ty",
        )?;
        let ty = self.add(ctx, GNode::U(lvl));
        let tm = self.add(ctx, GNode::Pi([arg_ty, res_ty]));
        self.0.set_ty_unchecked(ctx, tm, ty);
        Ok(HasTyIn { tm, ty })
    }

    fn derive_sigma<S>(
        &mut self,
        ctx: C,
        arg_lvl: ULvl,
        res_lvl: ULvl,
        lvl: ULvl,
        arg_ty: T,
        res_ty: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        if !self.u_le(arg_lvl, lvl) {
            return Err(S::fail("derive_sigma: cannot deduce that arg_lvl ≤ lvl"));
        }
        if !self.u_le(res_lvl, lvl) {
            return Err(S::fail("derive_sigma: cannot deduce that res_lvl ≤ lvl"));
        }
        let arg_lvl_ty = self.add(ctx, GNode::U(arg_lvl));
        let res_lvl_ty = self.add(ctx, GNode::U(res_lvl));
        self.ensure_has_ty(ctx, arg_ty, arg_lvl_ty, strategy, "derive_sigma: arg_ty")?;
        self.ensure_has_ty_under(
            ctx,
            arg_ty,
            res_ty,
            res_lvl_ty,
            strategy,
            "derive_sigma: res_ty",
        )?;
        let ty = self.add(ctx, GNode::U(lvl));
        let tm = self.add(ctx, GNode::Sigma([arg_ty, res_ty]));
        self.0.set_ty_unchecked(ctx, tm, ty);
        Ok(HasTyIn { tm, ty })
    }

    fn derive_abs<S>(
        &mut self,
        ctx: C,
        arg_ty: T,
        body: T,
        res_ty: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        self.ensure_has_ty_under(ctx, arg_ty, body, res_ty, strategy, "derive_abs: body")?;
        let tm = self.add(ctx, GNode::Abs([arg_ty, body]));
        let ty = self.add(ctx, GNode::Pi([arg_ty, res_ty]));
        self.0.set_ty_unchecked(ctx, tm, ty);
        Ok(HasTyIn { tm, ty })
    }

    fn derive_app<S>(
        &mut self,
        ctx: C,
        arg_ty: T,
        res_ty: T,
        func: T,
        arg: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        self.ensure_has_ty(ctx, arg, arg_ty, strategy, "derive_app: arg")?;
        let pi = self.add(ctx, GNode::Pi([arg_ty, res_ty]));
        self.ensure_has_ty(ctx, func, pi, strategy, "derive_app: func")?;
        let tm = self.add(ctx, GNode::App([func, arg]));
        let ty = self.lazy_subst(ctx, arg, res_ty);
        self.0.set_ty_unchecked(ctx, tm, ty);
        Ok(HasTyIn { tm, ty })
    }

    fn derive_pair<S>(
        &mut self,
        ctx: C,
        arg_ty: T,
        res_ty: T,
        fst: T,
        snd: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        self.ensure_is_ty_under(ctx, arg_ty, res_ty, strategy, "derive_pair: res_ty")?;
        self.ensure_has_ty(ctx, fst, arg_ty, strategy, "derive_pair: fst")?;
        let snd_ty = self.lazy_subst(ctx, fst, res_ty);
        self.ensure_has_ty(ctx, snd, snd_ty, strategy, "derive_pair: snd")?;
        let tm = self.add(ctx, GNode::Pair([fst, snd]));
        let ty = self.add(ctx, GNode::Sigma([arg_ty, res_ty]));
        self.0.set_ty_unchecked(ctx, tm, ty);
        Ok(HasTyIn { tm, ty })
    }

    fn derive_fst<S>(
        &mut self,
        ctx: C,
        arg_ty: T,
        res_ty: T,
        pair: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        let sigma = self.add(ctx, GNode::Sigma([arg_ty, res_ty]));
        self.ensure_has_ty(ctx, pair, sigma, strategy, "derive_fst: pair")?;
        let tm = self.add(ctx, GNode::Fst([pair]));
        self.0.set_ty_unchecked(ctx, tm, arg_ty);
        Ok(HasTyIn { tm, ty: arg_ty })
    }

    fn derive_snd<S>(
        &mut self,
        ctx: C,
        arg_ty: T,
        res_ty: T,
        pair: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        let sigma = self.add(ctx, GNode::Sigma([arg_ty, res_ty]));
        self.ensure_has_ty(ctx, pair, sigma, strategy, "derive_snd: pair")?;
        let fst = self.add(ctx, GNode::Fst([pair]));
        self.0.set_ty_unchecked(ctx, fst, arg_ty);
        let tm = self.add(ctx, GNode::Snd([pair]));
        let ty = self.lazy_subst(ctx, fst, res_ty);
        self.0.set_ty_unchecked(ctx, tm, ty);
        Ok(HasTyIn { tm, ty })
    }
}
