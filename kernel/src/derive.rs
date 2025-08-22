use crate::term::ULevel;

/// A trait implemented by a datastore that can read and write facts about terms in a context.
pub trait ReadFacts<C, T> {
    // == Predicates ==
    /// Check whether the term `tm` is well-formed in `ctx`
    /// Corresponds to `Ctx.IsWf` in `covalence-lean`
    fn is_wf(&self, ctx: C, tm: T) -> bool;

    /// Check whether the term `tm` is a type in the context `ctx`
    ///
    /// Corresponds to `Ctx.IsTy` in `covalence-lean`
    fn is_ty(&self, ctx: C, tm: T) -> bool;

    /// Check whether the term `tm` is an inhabited type in the context `ctx`
    ///
    /// Corresponds to `Ctx.IsInhab` in `covalence-lean`
    fn is_inhab(&self, ctx: C, tm: T) -> bool;

    /// Check whether the term `tm` is empty in the context `ctx`
    ///
    /// Corresponds to `Ctx.IsEmpty` in `covalence-lean`
    fn is_empty(&self, ctx: C, tm: T) -> bool;

    /// Check whether the term `tm` is a universe in the context `ctx`
    fn is_univ(&self, ctx: C, tm: T) -> bool;

    /// Check whether the term `tm` is a proposition in the context `ctx`
    ///
    /// Corresponds to `Ctx.IsProp` in `covalence-lean`
    fn is_prop(&self, ctx: C, tm: T) -> bool;

    /// Check whether the term `tm` is a true proposition in the context `ctx`
    ///
    /// Corresponds to `Ctx.IsTrue` in `covalence-lean`
    fn is_true(&self, ctx: C, tm: T) -> bool;

    /// Check whether the term `tm` is a false proposition in the context `ctx`
    ///
    /// Corresponds to `Ctx.IsFalse` in `covalence-lean`
    fn is_false(&self, ctx: C, tm: T) -> bool;

    // == Relations ==
    /// Check whether the term `lhs` is equal to the term `rhs` in `ctx`
    ///
    /// Corresponds to `Ctx.Rw` in `covalence-lean`
    fn eq_in(&self, ctx: C, lhs: T, rhs: T) -> bool;

    /// Check whether the terms `lhs` and `rhs` have compatible types in `ctx`
    ///
    /// Corresponds to `Ctx.RwCmp` in `covalence-lean`
    ///
    /// Note that two equal terms always have compatible types, even if they are not well-formed!
    fn compat_in(&self, ctx: C, lhs: T, rhs: T) -> bool;

    /// Check whether the term `tm` has type `ty` in `ctx`
    ///
    /// Corresponds to `Ctx.HasTy` in `covalence-lean`
    fn has_ty(&self, ctx: C, tm: T, ty: T) -> bool;

    /// Check whether the term `tm` has type `ty` in `ctx` under a binder `binder`
    ///
    /// Corresponds to `Ctx.HasTyUnder` in `covalence-lean`
    fn has_ty_under(&self, ctx: C, binder: T, tm: T, ty: T) -> bool;
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

    /// Mark a term as an empty type
    fn set_is_empty_unchecked(&mut self, ctx: C, tm: T);

    /// Mark a term as a proposition
    fn set_is_prop_unchecked(&mut self, ctx: C, tm: T);

    /// Mark a term as a true proposition
    fn set_true_unchecked(&mut self, ctx: C, tm: T);

    /// Mark a term as a false proposition
    fn set_false_unchecked(&mut self, ctx: C, tm: T);

    // == Relations ==
    /// Set two terms as equal in a given context
    fn set_eq_unchecked(&mut self, ctx: C, lhs: T, rhs: T);

    /// Set the type of a term
    fn set_ty_unchecked(&mut self, ctx: C, tm: T, ty: T);

    /// Set the type of a term under a binder
    fn set_ty_under_unchecked(&mut self, ctx: C, binder: T, tm: T, ty: T);
}

/// A strategy tells a kernel how to derive facts about terms in a context
pub trait Strategy<C, T, K> {
    /// The type returned by the strategy on failure
    type Fail;
}

/// A typing derivation in a given context
pub struct HasTyIn<T> {
    pub tm: T,
    pub ty: T,
}

/// Typing rules for deriving facts about terms from those already in the datastore
pub trait Derive<C, T>: Sized {
    /// Typecheck a typing universe
    ///
    /// Corresponds to the rule `Ctx.HasTy.univ`
    /// ```text
    /// Γ ok
    /// ===
    /// Γ ⊢ U_ℓ : U_(ℓ + 1)
    /// ```
    fn derive_univ(ctx: C, level: ULevel) -> HasTyIn<T>;

    /// Typecheck a variable
    ///
    /// Corresponds to the rule `Ctx.HasTy.var`
    /// ```text
    /// Γ ok
    /// Γ(x) = A
    /// ===
    /// Γ ⊢ x : A
    /// ```
    fn derive_var<S>(ctx: C, var: C, ty: T, strategy: &mut S) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Typecheck the unit type at a given level
    ///
    /// Corresponds to the rule `Ctx.HasTy.unit`
    /// ```text
    /// Γ ok
    /// ===
    /// Γ ⊢ 1_ℓ : U_ℓ
    /// ```
    fn derive_unit(ctx: C, level: ULevel) -> HasTyIn<T>;

    /// Typecheck the unique value of the unit type at a given level
    ///
    /// Corresponds to the rule `Ctx.HasTy.nil`
    /// ```text
    /// Γ ok
    /// ===
    /// Γ ⊢ *_ℓ : 1_ℓ
    /// ```
    fn derive_nil(ctx: C, level: ULevel) -> HasTyIn<T>;

    /// Typecheck the empty type at a given level
    ///
    /// Corresponds to the rule `Ctx.HasTy.empty`
    /// ```text
    /// Γ ok
    /// ===
    /// Γ ⊢ 0_ℓ : U_ℓ
    /// ```
    fn derive_empty(ctx: C, level: ULevel) -> HasTyIn<T>;

    /// Typecheck an equation between terms
    ///
    /// Corresponds to the rule `Ctx.HasTy.eqn`
    /// ```text
    /// Γ ⊢ a : A
    /// Γ ⊢ b : A
    /// ===
    /// Γ ⊢ a = b : 2
    /// ```
    fn derive_eqn<S>(ctx: C, lhs: T, rhs: T, strategy: &mut S) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Typecheck a pi type
    ///
    /// Corresponds to the rule `Ctx.HasTy.pi_cf`
    /// ```text
    /// Γ ⊢ A : U_m
    /// ∀x ∉ L . Γ , x : A ⊢ B^x : U_n
    /// ℓ = imax(m, n)
    /// ===
    /// Γ ⊢ Π_ℓ A . B : U_ℓ
    /// ```
    fn derive_pi<S>(
        ctx: C,
        arg_level: ULevel,
        res_level: ULevel,
        arg_ty: T,
        res_ty: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Typecheck an application
    ///
    /// Corresponds to the rule `Ctx.HasTy.app_cf`
    /// ```text
    /// Γ ⊢ A : U_m
    /// ∀x ∉ L . Γ , x : A ⊢ B^x : U_n
    /// ℓ = imax(m, n)
    /// Γ ⊢ f : Π_ℓ A . B
    /// Γ ⊢ a : A
    /// ===
    /// Γ ⊢ f a : B^a
    /// ```
    fn derive_app<S>(
        ctx: C,
        arg_ty: T,
        res_ty: T,
        func: T,
        arg: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Typecheck a lambda abstraction
    ///
    /// Corresponds to the rule `Ctx.HasTy.abs_cf`
    /// ```text
    /// Γ ⊢ A : U_m
    /// ∀x ∉ L . Γ , x : A ⊢ B^x : U_n
    /// ℓ = imax(m, n)
    /// ∀x ∉ L . Γ , x : A ⊢ b^x : B^x
    /// ===
    /// Γ ⊢ λ_ℓ A => B . b : Π_ℓ A . B
    /// ```
    fn derive_abs<S>(
        ctx: C,
        level: ULevel,
        arg_ty: T,
        res_ty: T,
        body: T,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Typecheck a sigma type
    ///
    /// Corresponds to the rule `Ctx.HasTy.sigma_cf`
    /// ```text
    /// Γ ⊢ A : U_m
    /// ∀x ∉ L . Γ , x : A ⊢ B^x : U_n
    /// ℓ = m ⊔ n
    /// ===
    /// Γ ⊢ Σ_ℓ A . B : U_ℓ
    /// ```
    fn derive_sigma<S>(
        ctx: C,
        arg_level: ULevel,
        res_level: ULevel,
        arg_ty: T,
        res_ty: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Typecheck a pair
    ///     
    /// Corresponds to the rule `Ctx.HasTy.pair_cf`
    /// ```text
    /// Γ ⊢ A : U_m
    /// ∀x ∉ L . Γ , x : A ⊢ B^x : U_n
    /// ℓ = m ⊔ n
    /// Γ ⊢ a : A
    /// Γ ⊢ b : B^a
    /// ===
    /// Γ ⊢ (a, b) : Σ_ℓ A . B
    /// ```
    fn derive_pair<S>(
        ctx: C,
        level: ULevel,
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
    /// Corresponds to the rule `Ctx.HasTy.fst_cf`
    /// ```text
    /// Γ ⊢ A : U_m
    /// ∀x ∉ L . Γ , x : A ⊢ B^x : U_n
    /// ℓ = m ⊔ n
    /// Γ ⊢ p : Σ_ℓ A . B
    /// ===
    /// Γ ⊢ fst_(A . B) p : A
    /// ```
    fn derive_fst<S>(
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
    /// Corresponds to the rule `Ctx.HasTy.snd_cf`
    /// ```text
    /// Γ ⊢ A : U_m
    /// ∀x ∉ L . Γ , x : A ⊢ B^x : U_n
    /// ℓ = m ⊔ n
    /// Γ ⊢ p : Σ_ℓ A . B
    /// ===
    /// Γ ⊢ snd_(A . B) p : B^(fst_(A . B) p)
    /// ```
    fn derive_snd<S>(
        ctx: C,
        arg_ty: T,
        res_ty: T,
        pair: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Typecheck a (dependent) if-then-else expression
    ///
    /// Corresponds to the rule `Ctx.HasTy.dite_cf`
    /// ```text
    /// Γ ⊢ φ : 2
    /// Γ ⊢ A : U_ℓ
    /// ∀x ∉ L . Γ, x : φ ⊢ a : A
    /// ∀x ∉ L . Γ, x : ¬φ ⊢ b : A
    /// ===
    /// Γ ⊢ ite φ A a b : A
    /// ```
    fn derive_dite<S>(
        ctx: C,
        prop: T,
        ty: T,
        then_br: T,
        else_br: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Typecheck a propositional truncation
    ///
    /// Corresponds to the rule `Ctx.HasTy.trunc`
    /// ```text
    /// Γ ⊢ A : U_ℓ
    /// ===
    /// Γ ⊢ ||A|| : 2
    /// ```
    fn derive_trunc<S>(ctx: C, ty: T, strategy: &mut S) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Typecheck Hilbert's ε operator
    ///
    /// Corresponds to the rule `Ctx.HasTy.choose`
    /// ```text
    /// Γ ⊢ A : U_ℓ
    /// Γ ⊢ ||A|| ≡ ⊤ : 2
    /// ∀x ∉ L . Γ, x : A ⊢ φ^x : 2
    /// ===
    /// Γ ⊢ ε_(A, φ) : A
    /// ```
    fn derive_choose<S>(ctx: C, ty: T, prop: T, strategy: &mut S) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;

    /// Typecheck the natural numbers
    ///
    /// Corresponds to the rule `Ctx.HasTy.nats`
    /// ```text
    /// Γ ok
    /// ===
    /// Γ ⊢ ℕ : U_1
    /// ```
    fn derive_nats(ctx: C) -> HasTyIn<T>;

    /// Typecheck zero
    ///
    /// Corresponds to the rule `Ctx.HasTy.zero`
    /// ```text
    /// Γ ok
    /// ===
    /// Γ ⊢ 0 : ℕ
    /// ```
    fn derive_zero(ctx: C) -> HasTyIn<T>;

    /// Typecheck the successor function
    ///
    /// Corresponds to the rule `Ctx.HasTy.succ`
    /// ```text
    /// Γ ok
    /// ===
    /// Γ ⊢ succ : ℕ → ℕ
    /// ```
    fn derive_succ(ctx: C, n: T) -> HasTyIn<T>;

    /// Typecheck the recursor on the natural numbers
    ///
    /// Corresponds to the rule `Ctx.HasTy.natrec`
    /// ```text
    /// ∀x ∉ L . Γ, x : ℕ ⊢ C^x : U_ℓ
    /// Γ ⊢ n : ℕ
    /// Γ ⊢ z : C^0
    /// ∀x ∉ L, Γ, x : ℕ ⊢ s^x : C^x → C^(app_(ℕ . ℕ) succ x)
    fn derive_natrec<S>(
        ctx: C,
        motive: T,
        scrut: T,
        base: T,
        step: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>;
}

// /// The `covalence` kernel
// ///
// /// This type is parametrized by its datastore `D`
// #[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
// pub struct Kernel<D>(D);

// impl<D> Kernel<D> {
//     /// Get an _immutable_ reference to the underlying datastore
//     pub fn data(&self) -> &D {
//         &self.0
//     }
// }

// impl<C, T, D: ReadFacts<C, T>> ReadFacts<C, T> for Kernel<D> {
//     fn is_wf(&self, ctx: C, tm: T) -> bool {
//         self.0.is_wf(ctx, tm)
//     }

//     fn is_ty(&self, ctx: C, tm: T) -> bool {
//         self.0.is_ty(ctx, tm)
//     }

//     fn is_inhab(&self, ctx: C, tm: T) -> bool {
//         self.0.is_inhab(ctx, tm)
//     }

//     fn is_empty(&self, ctx: C, tm: T) -> bool {
//         self.0.is_empty(ctx, tm)
//     }

//     fn is_univ(&self, ctx: C, tm: T) -> bool {
//         self.0.is_univ(ctx, tm)
//     }

//     fn is_prop(&self, ctx: C, tm: T) -> bool {
//         self.0.is_prop(ctx, tm)
//     }

//     fn is_true(&self, ctx: C, tm: T) -> bool {
//         self.0.is_true(ctx, tm)
//     }

//     fn is_false(&self, ctx: C, tm: T) -> bool {
//         self.0.is_false(ctx, tm)
//     }

//     fn eq_in(&self, ctx: C, lhs: T, rhs: T) -> bool {
//         self.0.eq_in(ctx, lhs, rhs)
//     }

//     fn compat_in(&self, ctx: C, lhs: T, rhs: T) -> bool {
//         self.0.compat_in(ctx, lhs, rhs)
//     }

//     fn has_ty(&self, ctx: C, tm: T, ty: T) -> bool {
//         self.0.has_ty(ctx, tm, ty)
//     }

//     fn has_ty_under(&self, ctx: C, binder: T, tm: T, ty: T) -> bool {
//         self.0.has_ty_under(ctx, binder, tm, ty)
//     }
// }
