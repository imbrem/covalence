use smallvec::SmallVec;

use crate::api::error::*;
use crate::api::store::*;
use crate::data::term::{Gv, ULvl};

/// A strategy tells a kernel how to derive facts about terms in a context
pub trait Strategy<C, T, K: ?Sized> {
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

    /// Begin a goal
    fn start_goal(&mut self, _goal: Goal<C, T>) -> Result<(), Self::Fail> {
        Ok(())
    }

    //TODO: register side conditions as well?

    /// Begin a derivation
    fn start_rule(&mut self, _rule: &'static str) -> Result<(), Self::Fail> {
        Ok(())
    }

    /// End a successful derivation
    fn finish_rule(&mut self, _result: Goal<C, T>) {}

    /// An irrecoverable failure of a derivation
    fn fail(&mut self, msg: &'static str) -> Self::Fail;
}

impl<C, T, K: ?Sized> Strategy<C, T, K> for () {
    type Fail = &'static str;

    fn prove_goal(
        &mut self,
        _ker: &mut K,
        _goal: Goal<C, T>,
        msg: &'static str,
        _attempt_no: usize,
    ) -> Result<(), Self::Fail> {
        Err(msg)
    }

    fn fail(&mut self, msg: &'static str) -> Self::Fail {
        msg
    }
}

pub trait Ensure<C: Copy, T: Copy + PartialEq>: ReadFacts<C, T> + TermStore<C, T> {
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
        strategy.start_goal(goal)?;
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

    /// Attempt to prove that a context is contradictory
    fn ensure_is_contr<S>(
        &mut self,
        ctx: C,
        strategy: &mut S,
        msg: &'static str,
    ) -> Result<(), S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        self.ensure_goal(Goal::IsContr(ctx), strategy, msg)
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

    /// Attempt to prove that a term is an empty type in a context
    fn ensure_is_empty<S>(
        &mut self,
        ctx: C,
        tm: T,
        strategy: &mut S,
        msg: &'static str,
    ) -> Result<(), S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        self.ensure_goal(IsEmpty { ctx, tm }.into(), strategy, msg)
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

    /// Attempt to prove that a term is always inhabited in a context under a binder
    fn ensure_forall_inhab_under<S>(
        &mut self,
        ctx: C,
        binder: T,
        ty: T,
        strategy: &mut S,
        msg: &'static str,
    ) -> Result<(), S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        self.ensure_goal(ForallInhabUnder { ctx, binder, ty }.into(), strategy, msg)
    }

    /// Attempt to prove that there exists a value of the binder type such that the term is
    /// inhabited
    fn ensure_exists_inhab_under<S>(
        &mut self,
        ctx: C,
        binder: T,
        ty: T,
        strategy: &mut S,
        msg: &'static str,
    ) -> Result<(), S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        self.ensure_goal(ExistsInhabUnder { ctx, binder, ty }.into(), strategy, msg)
    }

    /// Attempt to prove that two terms are equal in a context
    fn ensure_eq_in<S>(
        &mut self,
        ctx: C,
        lhs: T,
        rhs: T,
        strategy: &mut S,
        msg: &'static str,
    ) -> Result<(), S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        self.ensure_goal(EqIn { ctx, lhs, rhs }.into(), strategy, msg)
    }

    /// Ensure that all assumptions in a context are valid under a binder
    fn ensure_assumptions_valid_under<S>(
        &mut self,
        ctx: C,
        binder: T,
        target: C,
        strategy: &mut S,
        msg: &'static str,
    ) -> Result<(), S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        let assumptions: SmallVec<[T; 16]> = (0..self.num_assumptions(target))
            .map(|i| self.assumption(target, i).unwrap())
            .collect();
        for &assumption in &assumptions {
            let ty = self.import(ctx, target, assumption);
            self.ensure_forall_inhab_under(ctx, binder, ty, strategy, msg)?;
        }
        // TODO: rather than checking assumptions match directly, it may make more sense to:
        // - re-collect assumptions
        // - sort and dedup both lists
        // - check equal
        //
        // This would require `T` to be `PartialOrd` (in fact, `Ord`) as well.
        //
        // In this case, it may make sense to move things to an extension trait?
        for (i, assumption) in assumptions.iter().enumerate() {
            if self.assumption(target, i) != Some(*assumption) {
                return Err(strategy.fail(kernel_error::ENSURE_ASSUMPTIONS_VALID_UNDER_CHANGED));
            }
        }
        Ok(())
    }
}

impl<C, T, K> Ensure<C, T> for K
where
    C: Copy,
    T: Copy + PartialEq,
    K: ReadFacts<C, T> + TermStore<C, T>,
{
}

/// Typing rules for deriving facts about terms from those already in the datastore
pub trait Derive<C, T> {
    /// Assume a new hypothesis in this context
    fn assume<S>(
        &mut self,
        ctx: C,
        ty: T,
        subctx: C,
        strategy: &mut S,
    ) -> Result<IsInhabIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Add a new variable to this context with the given type
    fn add_var<S>(&mut self, ctx: C, ty: T, strategy: &mut S) -> Result<Gv<C>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Insert a new context with the given parameter
    fn with_param<S>(&mut self, parent: C, param: T, strategy: &mut S) -> Result<Gv<C>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Compute the substitution of a term
    ///
    /// Given terms `bound` and `body`
    /// - If `body` is locally-closed, return it unchanged
    /// - Otherwise, `let bound in body`
    ///
    /// TODO: reference Lean
    fn subst(&mut self, ctx: C, bound: T, body: T) -> T;

    /// Compute the closure of a term
    ///
    /// Given term `tm` in context `ctx`
    /// - If `tm` does not depend on the variable `var`, return `tm`
    /// - Otherwise, return `close var tm`
    fn close(&mut self, ctx: C, var: Gv<C>, tm: T) -> T;

    /// Compute the closure of an imported term
    ///
    /// Given term `tm` in context `src`
    /// - If `src` has no parameter, or `tm` does not depend on the parameter of `src`, return the
    ///   import of `tm` into `ctx`
    /// - Otherwise, return `close src (import src tm)`
    fn close_import(&mut self, ctx: C, src: Gv<C>, tm: T) -> T;

    /// The substitution of a term is equal to its lazy substitution
    fn lazy_subst_eq(&mut self, ctx: C, bound: T, body: T) -> Eqn<T>;

    /// The closure of a term is equal to its lazy closure
    fn lazy_close_eq(&mut self, ctx: C, var: Gv<C>, tm: T) -> Eqn<T>;

    /// An
    fn lazy_import_eq(&mut self, ctx: C, src: C, tm: T) -> Eqn<T>;

    /// The closure of an imported term is equal to its lazy imported closure
    fn lazy_close_import_eq(&mut self, ctx: C, src: Gv<C>, tm: T) -> Eqn<T>;

    /// Cast by universe level
    ///
    /// TODO: reference Lean
    fn derive_u_le<S>(
        &mut self,
        ctx: C,
        tm: T,
        lo: ULvl,
        hi: ULvl,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Check a term has type `B` under a binder `A`
    ///
    /// Checks that:
    /// - `binder` is a valid type in `Γ`
    /// - `src` is a child of `ctx` with parameter `x : binder`
    /// - `tm` has type `ty` in context `src`
    ///
    /// If so, then `close x tm` has type `close x ty` under `binder` in `ctx`
    ///
    /// TODO: reference Lean
    ///
    /// # Examples
    /// ```rust
    /// # #[cfg(feature = "wrapper")] {
    /// # use covalence_kernel::kernel::*;
    /// # use covalence_kernel::error::kernel_error;
    /// # let mut ker = Kernel::new();
    /// # let ctx = ker.new_ctx();
    /// // `close x x ≡ #0` has type `empty` under binder `empty`
    /// let emp = ker.add(ctx, Node::Empty);
    /// let x = ker.with_param(ctx, emp, &mut ()).unwrap();
    /// let tm = ker.add(ctx, Node::Fv(x));
    /// let res = ker.derive_close_has_ty_under(ctx, x, tm, emp, &mut ()).unwrap();
    ///
    /// // the result is cached and valid
    /// assert!(res.check(ctx, &ker));
    /// let close_x = ker.close(ctx, x, tm);
    /// assert_eq!(res.tm, close_x);
    /// assert_eq!(res.ty, emp);
    ///
    /// // we can no longer derive this if we add another variable
    /// // (even if this variable is of inhabited type).
    /// //
    /// // we might relax this later if the closed term does not depend on
    /// // the variable.
    /// let unit_v = ker.add(x.ctx, Node::Unit);
    /// let y = ker.add_var(x.ctx, unit_v, &mut ()).unwrap();
    /// assert_eq!(
    ///     ker.derive_close_has_ty_under(ctx, x, tm, emp, &mut ()).unwrap_err(),
    ///     kernel_error::DERIVE_CLOSE_HAS_TY_UNDER_TOO_MANY_VARS
    /// );
    /// // but the result is still cached in ctx!
    /// //
    /// // which is valid since the result is about the unchanged closed term, _not_ the term in the
    /// // (imported, changed) context!
    /// assert!(res.check(ctx, &ker));
    /// # }
    /// ```
    fn derive_close_has_ty_under<S>(
        &mut self,
        ctx: C,
        src: Gv<C>,
        tm: T,
        ty: T,
        strategy: &mut S,
    ) -> Result<HasTyUnderIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

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
    fn derive_fv<S>(&mut self, ctx: C, var: Gv<C>, strategy: &mut S) -> Result<HasTyIn<T>, S::Fail>
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
        lvl: ULvl,
        arg_ty: T,
        res_ty: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

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
    ///
    /// If `p :≡ (a, b)`, also inserts the equation `Γ ⊢ fst (a, b) = a`
    /// (see: `Ctx.KIsWf.beta_fst_pair`)
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
    ///
    /// If `p :≡ (a, b)`, also inserts the equations `Γ ⊢ fst (a, b) ≡ a` and `Γ ⊢ snd (a, b) ≡ b`
    /// (see: `Ctx.KIsWf.beta_fst_pair`, `Ctx.KIsWf.beta_snd_pair`)
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

    /// Typecheck a dependent if-then-else
    ///
    /// If the condition is inhabited, equates it to the (lazy substitution of) the then-branch
    ///
    /// If the condition is known empty, equates it to the (lazy substitution of) the else-branch
    ///
    /// TODO: reference Lean
    fn derive_dite<S>(
        &mut self,
        ctx: C,
        cond: T,
        then_br: T,
        else_br: T,
        ty: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    // TODO: dite with different branch types; fusion lore

    /// Typecheck a propositional truncation
    ///
    /// Inherits inhabitance/emptiness from the underlying type
    ///
    /// TODO: reference Lean
    fn derive_trunc<S>(&mut self, ctx: C, ty: T, strategy: &mut S) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Typecheck Hilbert's ε-operator
    ///
    /// TODO: reference Lean
    fn derive_choose<S>(
        &mut self,
        ctx: C,
        ty: T,
        pred: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Typecheck the natural numbers
    ///
    /// TODO: reference Lean
    fn derive_nats<S>(
        &mut self,
        ctx: C,
        lvl: ULvl,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Typecheck a 64-bit natural number
    ///
    /// TODO: reference Lean
    fn derive_n64(&mut self, ctx: C, n: u64) -> HasTyIn<T>;

    /// Typecheck the successor function on natural numbers
    ///
    /// TODO: reference Lean
    fn derive_succ<S>(&mut self, ctx: C, n: T, strategy: &mut S) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Typecheck the recursor on natural numbers
    ///
    /// TODO: reference Lean
    fn derive_natrec<S>(
        &mut self,
        ctx: C,
        mot: T,
        z: T,
        s: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Typecheck a let-binding
    ///
    /// If the body does not have a free variable, this also equates the binding to its body.
    ///
    /// TODO: reference Lean
    fn derive_let<S>(
        &mut self,
        ctx: C,
        bound: T,
        bound_ty: T,
        body: T,
        body_ty: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Beta reduction for abstractions
    ///
    /// For well-formed `Γ ⊢ tm ≡ (λ A . b) a`, `Γ ⊢ a : A`; `Γ ⊢ tm b ≡ b^a`
    ///
    /// TODO: reference Lean
    fn derive_beta_abs<S>(
        &mut self,
        ctx: C,
        tm: T,
        arg: T,
        strategy: &mut S,
    ) -> Result<Eqn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Beta reduction for natural number recursors at zero
    ///
    /// For well-formed `Γ ⊢ tm ≡ natrec C z s`; `Γ ⊢ tm 0 = z`
    ///
    /// TODO: reference Lean
    fn derive_beta_zero<S>(&mut self, ctx: C, tm: T, strategy: &mut S) -> Result<Eqn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Beta reduction for natural number recursors at successors
    ///
    /// For well-formed `Γ ⊢ tm ≡ natrec C z s` and `Γ ⊢ n : ℕ`; `Γ ⊢ tm (succ n) = s^n (tm n)`
    ///
    /// TODO: reference Lean
    fn derive_beta_succ<S>(
        &mut self,
        ctx: C,
        tm: T,
        n: T,
        strategy: &mut S,
    ) -> Result<Eqn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Specification for choice
    ///
    /// If `∃A . φ` (encoded as Σ A . φ inhab) then `Γ ⊢ φ^(choose A φ)`
    ///
    /// TODO: reference lean
    fn derive_choose_spec<S>(
        &mut self,
        ctx: C,
        ty: T,
        pred: T,
        strategy: &mut S,
    ) -> Result<IsInhabIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Extensionality for the unit type
    ///
    /// If `Γ ⊢ a : 1` then `Γ ⊢ a ≡ * : 1`
    ///
    /// TODO: reference Lean
    fn derive_unit_ext<S>(&mut self, ctx: C, a: T, strategy: &mut S) -> Result<Eqn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Extensionality for the true proposition
    ///
    /// If `Γ ⊢ a : 2` and `Γ ⊢ a inhab` then `Γ ⊢ a ≡ 1 : 2`
    ///
    /// TODO: reference Lean
    fn derive_prop_ext_tt<S>(&mut self, ctx: C, a: T, strategy: &mut S) -> Result<Eqn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Extensionality for the false proposition
    ///
    /// If `Γ ⊢ a : 2` and `Γ ⊢ a empty` then `Γ ⊢ a ≡ 0 : 2`
    ///
    /// TODO: reference Lean
    fn derive_prop_ext_ff<S>(&mut self, ctx: C, a: T, strategy: &mut S) -> Result<Eqn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Extensionality
    ///
    /// If `Γ ⊢ a = b` then `Γ ⊢ a ≡ b`
    ///
    /// TODO: reference Lean
    fn derive_ext<S>(
        &mut self,
        ctx: C,
        lhs: T,
        rhs: T,
        strategy: &mut S,
    ) -> Result<Eqn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Eta for functions
    ///
    /// If `Γ ⊢ f : Π A . B` then `Γ ⊢ f ≡ λx. f x : Π A . B`
    ///
    /// TODO: reference Lean
    fn derive_pi_eta<S>(
        &mut self,
        ctx: C,
        ty: T,
        f: T,
        strategy: &mut S,
    ) -> Result<Eqn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Eta for pairs
    ///
    /// If `Γ ⊢ p : Σ A . B` then `Γ ⊢ p ≡ (fst p, snd p) : Σ A . B`
    ///
    /// TODO: reference Lean
    fn derive_sigma_eta<S>(
        &mut self,
        ctx: C,
        ty: T,
        p: T,
        strategy: &mut S,
    ) -> Result<Eqn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;
}
