use crate::strategy::*;
use crate::data::term::NodeT;
use crate::data::term::NodeVT;
use crate::data::term::{Fv, ULvl, Val};
use crate::fact::*;
use crate::store::*;

pub trait Ensure<C: Copy, T: Copy + PartialEq>:
    ReadTermDb<C, T> + WriteTermIndex<CtxId = C, TermId = T>
{
    /// Attempt to prove a goal
    fn ensure_goal<S>(
        &mut self,
        goal: QAtomSeq<C, Val<C, T>>,
        strategy: &mut S,
        msg: &'static str,
    ) -> Result<(), S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_goal(goal, self)?;
        let mut attempt_no = 0;
        while !goal.check(self.read()) {
            strategy.prove_goal(goal, msg, attempt_no, self)?;
            attempt_no += 1;
        }
        strategy.finish_goal(goal, self);
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
        self.ensure_goal(Seq::contr(ctx), strategy, msg)
    }

    /// Attempt to prove that a term is well-formed in a context
    fn ensure_is_wf<S>(
        &mut self,
        ctx: C,
        tm: Val<C, T>,
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
        tm: Val<C, T>,
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
        tm: Val<C, T>,
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
        tm: Val<C, T>,
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
        tm: Val<C, T>,
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
        tm: Val<C, T>,
        ty: Val<C, T>,
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
        binder: Val<C, T>,
        tm: Val<C, T>,
        strategy: &mut S,
        msg: &'static str,
    ) -> Result<(), S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        self.ensure_goal(ForallIsTy { ctx, binder, tm }.into(), strategy, msg)
    }

    /// Attempt to prove that a term has a given type in a context under a binder
    fn ensure_forall_has_ty<S>(
        &mut self,
        ctx: C,
        binder: Val<C, T>,
        tm: Val<C, T>,
        ty: Val<C, T>,
        strategy: &mut S,
        msg: &'static str,
    ) -> Result<(), S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        self.ensure_goal(
            ForallHasTy {
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

    /// Attempt to prove that a term is always a proposition under a binder
    fn ensure_forall_is_prop<S>(
        &mut self,
        ctx: C,
        binder: Val<C, T>,
        tm: Val<C, T>,
        strategy: &mut S,
        msg: &'static str,
    ) -> Result<(), S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        self.ensure_goal(ForallIsProp { ctx, binder, tm }.into(), strategy, msg)
    }

    /// Attempt to prove that a term is always inhabited in a context under a binder
    fn ensure_forall_inhab<S>(
        &mut self,
        ctx: C,
        binder: Val<C, T>,
        tm: Val<C, T>,
        strategy: &mut S,
        msg: &'static str,
    ) -> Result<(), S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        self.ensure_goal(ForallInhab { ctx, binder, tm }.into(), strategy, msg)
    }

    // /// Attempt to prove that there exists a value of the binder type such that the term is
    // /// inhabited
    // fn ensure_exists_inhab_under<S>(
    //     &mut self,
    //     ctx: C,
    //     binder: Val<C, T>,
    //     ty: Val<C, T>,
    //     strategy: &mut S,
    //     msg: &'static str,
    // ) -> Result<(), S::Fail>
    // where
    //     S: Strategy<C, T, Self>,
    // {
    //     self.ensure_goal(ExistsInhabUnder { ctx, binder, ty }.into(), strategy, msg)
    // }

    /// Attempt to prove that two terms are equal in a context
    fn ensure_eq_in<S>(
        &mut self,
        ctx: C,
        lhs: Val<C, T>,
        rhs: Val<C, T>,
        strategy: &mut S,
        msg: &'static str,
    ) -> Result<(), S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        self.ensure_goal(EqnIn::new(ctx, lhs, rhs).into(), strategy, msg)
    }

    /// Import a value into the given context
    fn import_with<S>(&mut self, ctx: C, val: Val<C, T>, strategy: &mut S) -> Result<T, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        let result = if let Some(result) = strategy.import(ctx, val, self)? {
            let result_val = self.read().val(ctx, result);
            self.ensure_eq_in(ctx, result_val, val, strategy, "import: equality")?;
            result
        } else {
            self.import(ctx, val)
        };
        strategy.finish_import(ctx, val, self);
        Ok(result)
    }

    /// Resolve a value
    fn resolve<S>(
        &mut self,
        ctx: C,
        val: NodeVT<C, T>,
        strategy: &mut S,
    ) -> Result<Val<C, T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        let result = if let Some(_result) = strategy.resolve(ctx, val, self)? {
            todo!("non-null resolution is not yet implemented!");
        } else {
            val.try_map_subterms(|tm| self.import_with(ctx, tm, strategy))?
                .val(ctx, self)
        };
        strategy.finish_resolve(ctx, val, self);
        Ok(result)
    }

    /// Import a resolved value into the given context
    fn add_with<S>(&mut self, ctx: C, val: NodeVT<C, T>, strategy: &mut S) -> Result<T, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        let val = self.resolve(ctx, val, strategy)?;
        self.import_with(ctx, val, strategy)
    }
}

impl<C, T, K> Ensure<C, T> for K
where
    C: Copy,
    T: Copy + PartialEq,
    K: ReadTermDb<C, T> + WriteTermIndex<CtxId = C, TermId = T> + ?Sized,
{
}

/// Safely add facts to the datastore
pub trait WriteTrusted<C, T> {
    /// Add a new term to the given context
    fn add_ix(&mut self, ctx: C, tm: NodeT<C, T>) -> Val<C, T>;
}

/// Typing rules for deriving facts about terms from those already in the datastore
pub trait DeriveTrusted<C, T, S>
where
    S: Strategy<C, T, Self>,
{
    /// Add a new variable to this context with the given type
    ///
    /// TODO: reference Lean
    ///
    /// # Examples
    /// ```rust
    /// # use covalence::kernel::*;
    /// # let mut ker = Kernel::default();
    /// let ctx = ker.new_ctx();
    /// let prop = ker.prop(ctx);
    /// let x = ker.add_var(ctx, prop, &mut ()).unwrap().val(&*ker);
    /// assert_eq!(x.node_ix(&*ker), Fv { ctx, ix : 0 });
    /// let y = ker.add_var(ctx, x, &mut ()).unwrap().val(&*ker);
    /// assert_eq!(y.node_ix(&*ker), Fv { ctx, ix : 1 });
    /// // Fails: y is not a valid type
    /// ker.add_var(ctx, y, &mut ()).unwrap_err();
    /// ```
    fn add_var(&mut self, ctx: C, ty: Val<C, T>, strategy: &mut S) -> Result<Fv<C>, S::Fail>;

    /// Set a context's parent
    ///
    /// TODO: reference Lean
    ///
    /// # Examples
    /// ```rust
    /// # use covalence::kernel::*;
    /// # let mut ker = Kernel::default();
    /// let parent = ker.new_ctx();
    /// let child = ker.new_ctx();
    /// assert!(!ker.is_ancestor(parent, child));
    /// ker.set_parent(child, parent, &mut ()).unwrap();
    /// assert!(ker.is_ancestor(parent, child));
    /// ker.set_parent(parent, child, &mut ()).unwrap_err();
    /// assert!(ker.is_ancestor(parent, child));
    /// ```
    fn set_parent(&mut self, ctx: C, parent: C, strategy: &mut S) -> Result<IsSubctx<C>, S::Fail>;

    /// Cast by universe level
    ///
    /// TODO: reference Lean
    fn derive_u_le(
        &mut self,
        ctx: C,
        tm: Val<C, T>,
        lo: ULvl,
        hi: ULvl,
        strategy: &mut S,
    ) -> Result<HasTy<C, Val<C, T>>, S::Fail>;

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
    fn derive_close_has_ty_under(
        &mut self,
        ctx: C,
        src: Fv<C>,
        tm: Val<C, T>,
        ty: Val<C, T>,
        strategy: &mut S,
    ) -> Result<ForallHasTy<C, Val<C, T>>, S::Fail>;

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
    fn derive_fv(
        &mut self,
        ctx: C,
        var: Fv<C>,
        strategy: &mut S,
    ) -> Result<HasTy<C, Val<C, T>>, S::Fail>;

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
    fn derive_univ(
        &mut self,
        ctx: C,
        lvl: ULvl,
        strategy: &mut S,
    ) -> Result<HasTy<C, Val<C, T>>, S::Fail>;

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
    fn derive_unit(
        &mut self,
        ctx: C,
        lvl: ULvl,
        strategy: &mut S,
    ) -> Result<HasTy<C, Val<C, T>>, S::Fail>;

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
    fn derive_nil(&mut self, ctx: C, strategy: &mut S) -> Result<HasTy<C, Val<C, T>>, S::Fail>;

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
    fn derive_empty(
        &mut self,
        ctx: C,
        lvl: ULvl,
        strategy: &mut S,
    ) -> Result<HasTy<C, Val<C, T>>, S::Fail>;

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
    fn derive_eqn(
        &mut self,
        ctx: C,
        ty: Val<C, T>,
        lhs: Val<C, T>,
        rhs: Val<C, T>,
        strategy: &mut S,
    ) -> Result<HasTy<C, Val<C, T>>, S::Fail>;

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
    fn derive_pi(
        &mut self,
        ctx: C,
        arg_lvl: ULvl,
        lvl: ULvl,
        arg_ty: Val<C, T>,
        res_ty: Val<C, T>,
        strategy: &mut S,
    ) -> Result<HasTy<C, Val<C, T>>, S::Fail>;

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
    fn derive_sigma(
        &mut self,
        ctx: C,
        lvl: ULvl,
        arg_ty: Val<C, T>,
        res_ty: Val<C, T>,
        strategy: &mut S,
    ) -> Result<HasTy<C, Val<C, T>>, S::Fail>;

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
    fn derive_abs(
        &mut self,
        ctx: C,
        arg_ty: Val<C, T>,
        body: Val<C, T>,
        res_ty: Val<C, T>,
        strategy: &mut S,
    ) -> Result<HasTy<C, Val<C, T>>, S::Fail>;

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
    fn derive_app(
        &mut self,
        ctx: C,
        arg_ty: Val<C, T>,
        res_ty: Val<C, T>,
        func: Val<C, T>,
        arg: Val<C, T>,
        strategy: &mut S,
    ) -> Result<HasTy<C, Val<C, T>>, S::Fail>;

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
    fn derive_pair(
        &mut self,
        ctx: C,
        arg_ty: Val<C, T>,
        res_ty: Val<C, T>,
        fst: Val<C, T>,
        snd: Val<C, T>,
        strategy: &mut S,
    ) -> Result<HasTy<C, Val<C, T>>, S::Fail>;

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
    fn derive_fst(
        &mut self,
        ctx: C,
        arg_ty: Val<C, T>,
        res_ty: Val<C, T>,
        pair: Val<C, T>,
        strategy: &mut S,
    ) -> Result<HasTy<C, Val<C, T>>, S::Fail>;

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
    /// ```
    fn derive_snd(
        &mut self,
        ctx: C,
        arg_ty: Val<C, T>,
        res_ty: Val<C, T>,
        pair: Val<C, T>,
        strategy: &mut S,
    ) -> Result<HasTy<C, Val<C, T>>, S::Fail>;

    /// Typecheck a dependent if-then-else
    ///
    /// TODO: reference Lean
    fn derive_dite(
        &mut self,
        ctx: C,
        cond: Val<C, T>,
        then_br: Val<C, T>,
        else_br: Val<C, T>,
        ty: Val<C, T>,
        strategy: &mut S,
    ) -> Result<HasTy<C, Val<C, T>>, S::Fail>;

    // TODO: dite with different branch types; fusion lore

    /// Typecheck a propositional truncation
    ///
    /// Inherits inhabitance/emptiness from the underlying type
    ///
    /// TODO: reference Lean
    fn derive_trunc(
        &mut self,
        ctx: C,
        ty: Val<C, T>,
        strategy: &mut S,
    ) -> Result<HasTy<C, Val<C, T>>, S::Fail>;

    /// Typecheck Hilbert's ε-operator
    ///
    /// TODO: reference Lean
    fn derive_choose(
        &mut self,
        ctx: C,
        ty: Val<C, T>,
        pred: Val<C, T>,
        strategy: &mut S,
    ) -> Result<HasTy<C, Val<C, T>>, S::Fail>;

    /// Typecheck the natural numbers
    ///
    /// TODO: reference Lean
    ///
    /// TODO: fix this test!!!
    ///
    /// # Examples
    /// ```rust
    /// # use covalence::kernel::*;
    /// # let mut ker = Kernel::default();
    /// # let ctx = ker.new_ctx();
    /// let dn = ker.derive_nats(ctx, ULvl::SET, &mut ()).unwrap();
    /// assert_eq!(dn.tm.node_ix(&*ker), NodeIx::Nats);
    /// assert_eq!(dn.ty.node_ix(&*ker), NodeIx::U(ULvl::SET));
    /// // assert!(ker.has_ty(ctx, dn.tm, dn.ty));
    /// ```
    fn derive_nats(
        &mut self,
        ctx: C,
        lvl: ULvl,
        strategy: &mut S,
    ) -> Result<HasTy<C, Val<C, T>>, S::Fail>;

    /// Typecheck a 64-bit natural number
    ///
    /// TODO: reference Lean
    fn derive_n64(
        &mut self,
        ctx: C,
        n: u64,
        strategy: &mut S,
    ) -> Result<HasTy<C, Val<C, T>>, S::Fail>;

    /// Typecheck the successor function on natural numbers
    ///
    /// TODO: reference Lean
    fn derive_succ(
        &mut self,
        ctx: C,
        n: Val<C, T>,
        strategy: &mut S,
    ) -> Result<HasTy<C, Val<C, T>>, S::Fail>;

    /// Typecheck the recursor on natural numbers
    ///
    /// TODO: reference Lean
    fn derive_natrec(
        &mut self,
        ctx: C,
        mot: Val<C, T>,
        z: Val<C, T>,
        s: Val<C, T>,
        strategy: &mut S,
    ) -> Result<HasTy<C, Val<C, T>>, S::Fail>;

    /// Typecheck a let-binding
    ///
    /// If the body does not have a free variable, this also equates the binding to its body.
    ///
    /// TODO: reference Lean
    fn derive_let(
        &mut self,
        ctx: C,
        bound: Val<C, T>,
        bound_ty: Val<C, T>,
        body: Val<C, T>,
        body_ty: Val<C, T>,
        strategy: &mut S,
    ) -> Result<HasTy<C, Val<C, T>>, S::Fail>;

    /// Beta reduction for abstractions
    ///
    /// For well-formed `Γ ⊢ tm ≡ (λ A . b) a`, `Γ ⊢ a : A`; `Γ ⊢ tm b ≡ b^a`
    ///
    /// TODO: reference Lean
    fn derive_beta_abs(
        &mut self,
        ctx: C,
        tm: Val<C, T>,
        arg: Val<C, T>,
        strategy: &mut S,
    ) -> Result<EqnInV<C, T>, S::Fail>;

    // /// Beta reduction for dependent if-then-else at true
    // ///
    // /// For well-formed `Γ ⊢ tm ≡ ite a b c; if a inhab then `Γ ⊢ tm ≡ b^*`
    // ///
    // /// TODO: reference Lean
    // fn derive_beta_tt(
    //     &mut self,
    //     ctx: C,
    //     tm: Val<C, T>,
    //     strategy: &mut S,
    // ) -> Result<EqnInV<C, T>, S::Fail>;

    // /// Beta reduction for dependent if-then-else at false
    // ///
    // /// For well-formed `Γ ⊢ tm ≡ ite a b c; if a empty then `Γ ⊢ tm ≡ c^*`
    // ///
    // /// TODO: reference Lean
    // fn derive_beta_ff(
    //     &mut self,
    //     ctx: C,
    //     tm: Val<C, T>,
    //     strategy: &mut S,
    // ) -> Result<EqnInV<C, T>, S::Fail>;

    // /// Beta reduction for natural number recursors at zero
    // ///
    // /// For well-formed `Γ ⊢ tm ≡ natrec C z s`; `Γ ⊢ tm 0 = z`
    // ///
    // /// TODO: reference Lean
    // fn derive_beta_zero(
    //     &mut self,
    //     ctx: C,
    //     tm: Val<C, T>,
    //     strategy: &mut S,
    // ) -> Result<EqnInV<C, T>, S::Fail>;

    // /// Beta reduction for natural number recursors at successors
    // ///
    // /// For well-formed `Γ ⊢ tm ≡ natrec C z s` and `Γ ⊢ n : ℕ`; `Γ ⊢ tm (succ n) = s^n (tm n)`
    // ///
    // /// TODO: reference Lean
    // fn derive_beta_succ(
    //     &mut self,
    //     ctx: C,
    //     tm: Val<C, T>,
    //     n: Val<C, T>,
    //     strategy: &mut S,
    // ) -> Result<EqnInV<C, T>, S::Fail>;

    // /// Specification for choice
    // ///
    // /// If `∃A . φ` (encoded as Σ A . φ inhab) then `Γ ⊢ φ^(choose A φ)`
    // ///
    // /// TODO: reference lean
    // fn derive_choose_spec(
    //     &mut self,
    //     ctx: C,
    //     ty: Val<C, T>,
    //     pred: Val<C, T>,
    //     strategy: &mut S,
    // ) -> Result<IsInhab<C, Val<C, T>>, S::Fail>;

    // /// Extensionality for the unit type
    // ///
    // /// If `Γ ⊢ a : 1` then `Γ ⊢ a ≡ * : 1`
    // ///
    // /// TODO: reference Lean
    // fn derive_unit_ext(
    //     &mut self,
    //     ctx: C,
    //     a: Val<C, T>,
    //     strategy: &mut S,
    // ) -> Result<EqnInV<C, T>, S::Fail>;

    // /// Extensionality for the true proposition
    // ///
    // /// If `Γ ⊢ a : 2` and `Γ ⊢ a inhab` then `Γ ⊢ a ≡ 1 : 2`
    // ///
    // /// TODO: reference Lean
    // fn derive_prop_ext_tt(
    //     &mut self,
    //     ctx: C,
    //     a: Val<C, T>,
    //     strategy: &mut S,
    // ) -> Result<EqnInV<C, T>, S::Fail>;

    // /// Extensionality for the false proposition
    // ///
    // /// If `Γ ⊢ a : 2` and `Γ ⊢ a empty` then `Γ ⊢ a ≡ 0 : 2`
    // ///
    // /// TODO: reference Lean
    // fn derive_prop_ext_ff(
    //     &mut self,
    //     ctx: C,
    //     a: Val<C, T>,
    //     strategy: &mut S,
    // ) -> Result<EqnInV<C, T>, S::Fail>;

    // /// Extensionality
    // ///
    // /// If `Γ ⊢ a = b` then `Γ ⊢ a ≡ b`
    // ///
    // /// TODO: reference Lean
    // fn derive_ext(
    //     &mut self,
    //     ctx: C,
    //     lhs: Val<C, T>,
    //     rhs: Val<C, T>,
    //     strategy: &mut S,
    // ) -> Result<EqnInV<C, T>, S::Fail>;

    // /// Eta for functions
    // ///
    // /// If `Γ ⊢ f : Π A . B` then `Γ ⊢ f ≡ λx. f x : Π A . B`
    // ///
    // /// TODO: reference Lean
    // fn derive_pi_eta(
    //     &mut self,
    //     ctx: C,
    //     ty: Val<C, T>,
    //     f: Val<C, T>,
    //     strategy: &mut S,
    // ) -> Result<EqnInV<C, T>, S::Fail>;

    // /// Eta for pairs
    // ///
    // /// If `Γ ⊢ p : Σ A . B` then `Γ ⊢ p ≡ (fst p, snd p) : Σ A . B`
    // ///
    // /// TODO: reference Lean
    // fn derive_sigma_eta(
    //     &mut self,
    //     ctx: C,
    //     ty: Val<C, T>,
    //     p: Val<C, T>,
    //     strategy: &mut S,
    // ) -> Result<EqnInV<C, T>, S::Fail>;
}
