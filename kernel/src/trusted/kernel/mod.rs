use std::ops::Deref;

use crate::trusted::api::derive::*;
use crate::trusted::api::error::*;
use crate::trusted::api::store::*;
use crate::trusted::data::term::{Bv, Close, GNode, Gv, Import, ULvl};

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

impl<D> Deref for Kernel<D> {
    type Target = D;

    fn deref(&self) -> &D {
        &self.0
    }
}

impl<C, T, D: ReadFacts<C, T>> ReadFacts<C, T> for Kernel<D> {
    fn is_root(&self, ctx: C) -> bool {
        self.0.is_root(ctx)
    }

    fn is_contr(&self, ctx: C) -> bool {
        self.0.is_contr(ctx)
    }

    fn parent(&self, ctx: C) -> Option<C> {
        self.0.parent(ctx)
    }

    fn bvi(&self, ctx: C, tm: T) -> Bv {
        self.0.bvi(ctx, tm)
    }

    fn is_subctx(&self, lo: C, hi: C) -> bool {
        self.0.is_subctx(lo, hi)
    }

    fn is_subctx_of_parent(&self, lo: C, hi: C) -> bool {
        self.0.is_subctx_of_parent(lo, hi)
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

    fn is_empty(&self, ctx: C, tm: T) -> bool {
        self.0.is_empty(ctx, tm)
    }

    fn is_prop(&self, ctx: C, tm: T) -> bool {
        self.0.is_prop(ctx, tm)
    }

    fn has_var(&self, ctx: C, tm: T, var: Gv<C>) -> bool {
        self.0.has_var(ctx, tm, var)
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

    fn is_ty_under(&self, ctx: C, binder: T, ty: T) -> bool {
        self.0.is_ty_under(ctx, binder, ty)
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

    fn forall_inhab_under(&self, ctx: C, binder: T, ty: T) -> bool {
        self.0.forall_inhab_under(ctx, binder, ty)
    }

    fn exists_inhab_under(&self, ctx: C, binder: T, ty: T) -> bool {
        self.0.exists_inhab_under(ctx, binder, ty)
    }
}

impl<C, T, D: TermStore<C, T>> TermStore<C, T> for Kernel<D> {
    fn new_ctx(&mut self) -> C {
        self.0.new_ctx()
    }

    fn with_parent(&mut self, parent: C) -> C {
        self.0.with_parent(parent)
    }

    fn add(&mut self, ctx: C, term: GNode<C, T>) -> T {
        self.0.add(ctx, term)
    }

    fn import(&mut self, ctx: C, src: C, tm: T) -> T {
        self.0.import(ctx, src, tm)
    }

    fn node(&self, ctx: C, term: T) -> &GNode<C, T> {
        self.0.node(ctx, term)
    }

    fn lookup(&self, ctx: C, term: &mut GNode<C, T>) -> Option<T> {
        self.0.lookup(ctx, term)
    }

    fn lookup_import(&self, ctx: C, src: C, tm: T) -> Option<T> {
        self.0.lookup_import(ctx, src, tm)
    }

    fn var_ty(&mut self, ctx: C, var: Gv<C>) -> T {
        self.0.var_ty(ctx, var)
    }

    fn get_var_ty(&self, var: Gv<C>) -> T {
        self.0.get_var_ty(var)
    }

    fn num_assumptions(&self, ctx: C) -> usize {
        self.0.num_assumptions(ctx)
    }

    fn assumption(&self, ctx: C, ix: usize) -> Option<T> {
        self.0.assumption(ctx, ix)
    }

    fn num_vars(&self, ctx: C) -> usize {
        self.0.num_vars(ctx)
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

    fn propagate_in(&mut self, ctx: C) -> usize {
        self.0.propagate_in(ctx)
    }
}

impl<
    C: Copy + PartialEq,
    T: Copy + PartialEq,
    D: TermStore<C, T> + ReadFacts<C, T> + WriteFacts<C, T>,
> Derive<C, T> for Kernel<D>
{
    fn assume<S>(
        &mut self,
        ctx: C,
        ty: T,
        subctx: C,
        strategy: &mut S,
    ) -> Result<IsInhabIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("assume")?;
        if !self.is_subctx_of_parent(subctx, ctx) {
            return Err(strategy.fail(kernel_error::ASSUME_NOT_SUBCTX));
        }
        let in_subctx = self.import(subctx, ctx, ty);
        // If this type is already inhabited in a subcontext, there's no need to add it as an
        // assumption
        if !self.is_inhab(subctx, in_subctx) {
            self.ensure_is_ty(subctx, in_subctx, strategy, kernel_error::ASSUME_IS_TY)?;
            self.0.assume_unchecked(ctx, ty);
        }
        Ok(IsInhabIn(ty).finish_rule(ctx, strategy))
    }

    fn add_var<S>(&mut self, ctx: C, ty: T, strategy: &mut S) -> Result<Gv<C>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("add_var")?;
        self.ensure_is_inhab(ctx, ty, strategy, kernel_error::ADD_VAR_IS_INHAB)?;
        let var = self.0.add_var_unchecked(ctx, ty);
        debug_assert!(self.0.eq_in(ctx, self.0.get_var_ty(var), ty));
        let tm = self.0.add(ctx, GNode::Fv(var));
        self.0.set_has_ty_unchecked(ctx, tm, ty);
        HasTyIn { tm, ty }.finish_rule(ctx, strategy);
        Ok(var)
    }

    fn subst(&mut self, ctx: C, bound: T, body: T) -> T {
        if self.bvi(ctx, body) == Bv(0) {
            return body;
        }
        self.add(ctx, GNode::Let(Bv(0), [bound, body]))
    }

    fn close(&mut self, ctx: C, var: Gv<C>, tm: T) -> T {
        //TODO: optimize this, and cover more cases
        if self.bvi(ctx, tm) == Bv(0) && !self.has_var(ctx, tm, var) {
            return tm;
        }
        self.add(
            ctx,
            GNode::Close(Close {
                under: Bv(0),
                var,
                tm,
            }),
        )
    }

    fn close_import(&mut self, ctx: C, var: Gv<C>, tm: T) -> T {
        let import = self.import(ctx, var.ctx, tm);
        //TODO: optimize this, and cover more cases
        if self.bvi(var.ctx, tm) == Bv(0) && !self.has_var(var.ctx, tm, var) {
            return import;
        }
        self.add(
            ctx,
            GNode::Close(Close {
                under: Bv(0),
                var,
                tm: import,
            }),
        )
    }

    //TODO: implement _eager_ import (i.e. deep copy; name this properly. clone?)

    //TODO: implement _eager_ substitution; combine with import

    //TODO: implement _eager_ close; combine with import

    //TODO: equalities for eager substitution, close, import

    fn lazy_subst_eq(&mut self, ctx: C, bound: T, body: T) -> Eqn<T> {
        let eager = self.add(ctx, GNode::Let(Bv(0), [bound, body]));
        let lazy = self.subst(ctx, bound, body);
        self.0.set_eq_unchecked(ctx, eager, lazy);
        Eqn {
            lhs: eager,
            rhs: lazy,
        }
    }

    fn lazy_close_eq(&mut self, ctx: C, var: Gv<C>, tm: T) -> Eqn<T> {
        let eager = self.add(
            ctx,
            GNode::Close(Close {
                under: Bv(0),
                var,
                tm,
            }),
        );
        let lazy = self.close(ctx, var, tm);
        self.0.set_eq_unchecked(ctx, eager, lazy);
        Eqn {
            lhs: eager,
            rhs: lazy,
        }
    }

    fn lazy_import_eq(&mut self, ctx: C, src: C, tm: T) -> Eqn<T> {
        let eager = self.add(ctx, GNode::Import(Import { ctx: src, tm }));
        let lazy = self.import(ctx, src, tm);
        self.0.set_eq_unchecked(ctx, eager, lazy);
        Eqn {
            lhs: eager,
            rhs: lazy,
        }
    }

    fn lazy_close_import_eq(&mut self, ctx: C, var: Gv<C>, tm: T) -> Eqn<T> {
        let import = self.add(ctx, GNode::Import(Import { ctx: var.ctx, tm }));
        let eager = self.add(
            ctx,
            GNode::Close(Close {
                under: Bv(0),
                var,
                tm: import,
            }),
        );
        let lazy = self.close_import(ctx, var, tm);
        self.0.set_eq_unchecked(ctx, eager, lazy);
        Eqn {
            lhs: eager,
            rhs: lazy,
        }
    }

    fn derive_u_le<S>(
        &mut self,
        ctx: C,
        tm: T,
        lo: ULvl,
        hi: ULvl,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_u_le")?;
        if !self.u_le(lo, hi) {
            return Err(strategy.fail(kernel_error::DERIVE_U_LE_U_LE));
        }
        let old = self.add(ctx, GNode::U(lo));
        self.ensure_has_ty(ctx, tm, old, strategy, kernel_error::DERIVE_U_LE_TM)?;
        let ty = self.add(ctx, GNode::U(hi));
        self.0.set_has_ty_unchecked(ctx, tm, ty);
        Ok(HasTyIn { tm, ty }.finish_rule(ctx, strategy))
    }

    fn derive_close_has_ty_under<S>(
        &mut self,
        ctx: C,
        var: Gv<C>,
        tm: T,
        ty: T,
        strategy: &mut S,
    ) -> Result<HasTyUnderIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_close_has_ty_under")?;
        let import_tm = self.import(var.ctx, ctx, tm);
        let import_ty = self.import(var.ctx, ctx, ty);
        self.ensure_has_ty(
            var.ctx,
            import_tm,
            import_ty,
            strategy,
            kernel_error::DERIVE_CLOSE_HAS_TY_UNDER_HAS_TY,
        )?;
        let binder = self.var_ty(ctx, var);
        debug_assert!(
            self.is_ty(var.ctx, self.get_var_ty(var)),
            "var is valid in its context"
        );
        if var.ctx != ctx {
            // What we're really checking here is that every variable in `import_ty` and `import_tm`
            // either exists in `ctx` (due to our later subcontext check) or is `var` itself.
            //
            // But we can check this directly, and so relax this check, and maybe should, later!
            if self.num_vars(var.ctx) != 1 {
                return Err(strategy.fail(kernel_error::DERIVE_CLOSE_HAS_TY_UNDER_TOO_MANY_VARS));
            }
            // Now we check all the variable's context assumptions are implied by `binder` under
            // `ctx`
            self.ensure_assumptions_valid_under(
                ctx,
                binder,
                var.ctx,
                strategy,
                kernel_error::DERIVE_CLOSE_HAS_TY_UNDER_INVALID_ASSUMPTION,
            )?;
            // Finally, we check that the variable's parent context is a subcontext of `ctx`
            //
            // `ensure_assumptions_valid_under` should not be able to change this, since the check
            // is stable, but if we move to an unstable check its correct to check _afterwards_
            // rather than before!
            if self
                .parent(var.ctx)
                .is_some_and(|parent| !self.is_subctx(parent, ctx))
            {
                return Err(strategy.fail(kernel_error::DERIVE_CLOSE_HAS_TY_UNDER_ILL_SCOPED));
            }
        }
        let close_tm = self.close(ctx, var, tm);
        let close_ty = self.close(ctx, var, ty);
        self.0
            .set_has_ty_under_unchecked(ctx, binder, close_tm, close_ty);
        Ok(HasTyUnderIn {
            tm: close_tm,
            ty: close_ty,
            binder,
        }
        .finish_rule(ctx, strategy))
    }

    fn derive_fv<S>(&mut self, ctx: C, var: Gv<C>, strategy: &mut S) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_fv")?;
        if !self.is_subctx(var.ctx, ctx) {
            return Err(strategy.fail(kernel_error::DERIVE_FV_ILL_SCOPED));
        }
        //NOTE: this will crash if the variable is not in fact valid!
        let tm = self.add(ctx, GNode::Fv(var));
        let ty = self.var_ty(ctx, var);
        self.0.set_has_ty_unchecked(ctx, tm, ty);
        Ok(HasTyIn { tm, ty }.finish_rule(ctx, strategy))
    }

    fn derive_univ(&mut self, ctx: C, lvl: ULvl) -> HasTyIn<T> {
        let tm = self.add(ctx, GNode::U(lvl));
        let ty_lvl = self.succ(lvl);
        let ty = self.add(ctx, GNode::U(ty_lvl));
        self.0.set_has_ty_unchecked(ctx, tm, ty);
        HasTyIn { tm, ty }
    }

    fn derive_unit(&mut self, ctx: C, lvl: ULvl) -> HasTyIn<T> {
        let tm = self.add(ctx, GNode::Unit);
        let ty = self.add(ctx, GNode::U(lvl));
        self.0.set_has_ty_unchecked(ctx, tm, ty);
        self.0.set_is_prop_unchecked(ctx, tm);
        self.0.set_is_inhab_unchecked(ctx, tm);
        HasTyIn { tm, ty }
    }

    fn derive_nil(&mut self, ctx: C) -> HasTyIn<T> {
        let tm = self.add(ctx, GNode::Null);
        let ty = self.add(ctx, GNode::Unit);
        self.0.set_has_ty_unchecked(ctx, tm, ty);
        HasTyIn { tm, ty }
    }

    fn derive_empty(&mut self, ctx: C, lvl: ULvl) -> HasTyIn<T> {
        let tm = self.add(ctx, GNode::Empty);
        let ty = self.add(ctx, GNode::U(lvl));
        self.0.set_has_ty_unchecked(ctx, tm, ty);
        self.0.set_is_prop_unchecked(ctx, tm);
        self.0.set_is_empty_unchecked(ctx, tm);
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
        strategy.start_rule("derive_eqn")?;
        self.ensure_has_ty(ctx, lhs, ty, strategy, kernel_error::DERIVE_EQN_LHS)?;
        self.ensure_has_ty(ctx, rhs, ty, strategy, kernel_error::DERIVE_EQN_RHS)?;
        let tm = self.add(ctx, GNode::Eqn([lhs, rhs]));
        let ty = self.add(ctx, GNode::U(ULvl::PROP));
        self.0.set_has_ty_unchecked(ctx, tm, ty);
        Ok(HasTyIn { tm, ty }.finish_rule(ctx, strategy))
    }

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
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_pi")?;
        if !self.imax_le(arg_lvl, lvl, lvl) {
            return Err(strategy.fail(kernel_error::DERIVE_PI_IMAX_LE));
        }
        let arg_lvl_ty = self.add(ctx, GNode::U(arg_lvl));
        let ty = self.add(ctx, GNode::U(lvl));
        self.ensure_has_ty(
            ctx,
            arg_ty,
            arg_lvl_ty,
            strategy,
            kernel_error::DERIVE_PI_ARG_TY,
        )?;
        self.ensure_has_ty_under(
            ctx,
            arg_ty,
            res_ty,
            ty,
            strategy,
            kernel_error::DERIVE_PI_RES_TY,
        )?;
        let tm = self.add(ctx, GNode::Pi([arg_ty, res_ty]));
        self.0.set_has_ty_unchecked(ctx, tm, ty);
        Ok(HasTyIn { tm, ty }.finish_rule(ctx, strategy))
    }

    fn derive_sigma<S>(
        &mut self,
        ctx: C,
        lvl: ULvl,
        arg_ty: T,
        res_ty: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_sigma")?;
        let ty = self.add(ctx, GNode::U(lvl));
        self.ensure_has_ty(ctx, arg_ty, ty, strategy, kernel_error::DERIVE_SIGMA_ARG_TY)?;
        self.ensure_has_ty_under(
            ctx,
            arg_ty,
            res_ty,
            ty,
            strategy,
            kernel_error::DERIVE_SIGMA_RES_TY,
        )?;
        let tm = self.add(ctx, GNode::Sigma([arg_ty, res_ty]));
        self.0.set_has_ty_unchecked(ctx, tm, ty);
        Ok(HasTyIn { tm, ty }.finish_rule(ctx, strategy))
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
        strategy.start_rule("derive_abs")?;
        self.ensure_has_ty_under(
            ctx,
            arg_ty,
            body,
            res_ty,
            strategy,
            kernel_error::DERIVE_ABS_BODY,
        )?;
        let tm = self.add(ctx, GNode::Abs([arg_ty, body]));
        let ty = self.add(ctx, GNode::Pi([arg_ty, res_ty]));
        self.0.set_has_ty_unchecked(ctx, tm, ty);
        Ok(HasTyIn { tm, ty }.finish_rule(ctx, strategy))
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
        strategy.start_rule("derive_app")?;
        self.ensure_has_ty(ctx, arg, arg_ty, strategy, kernel_error::DERIVE_APP_ARG)?;
        let pi = self.add(ctx, GNode::Pi([arg_ty, res_ty]));
        self.ensure_has_ty(ctx, func, pi, strategy, kernel_error::DERIVE_APP_FUNC)?;
        let tm = self.add(ctx, GNode::App([func, arg]));
        let ty = self.subst(ctx, arg, res_ty);
        self.0.set_has_ty_unchecked(ctx, tm, ty);
        Ok(HasTyIn { tm, ty }.finish_rule(ctx, strategy))
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
        strategy.start_rule("derive_pair")?;
        self.ensure_is_ty_under(
            ctx,
            arg_ty,
            res_ty,
            strategy,
            kernel_error::DERIVE_PAIR_RES_TY,
        )?;
        self.ensure_has_ty(ctx, fst, arg_ty, strategy, kernel_error::DERIVE_PAIR_FST)?;
        let snd_ty = self.subst(ctx, fst, res_ty);
        self.ensure_has_ty(ctx, snd, snd_ty, strategy, kernel_error::DERIVE_PAIR_SND)?;
        let tm = self.add(ctx, GNode::Pair([fst, snd]));
        let ty = self.add(ctx, GNode::Sigma([arg_ty, res_ty]));
        self.0.set_has_ty_unchecked(ctx, tm, ty);
        Ok(HasTyIn { tm, ty }.finish_rule(ctx, strategy))
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
        strategy.start_rule("derive_fst")?;
        let sigma = self.add(ctx, GNode::Sigma([arg_ty, res_ty]));
        self.ensure_has_ty(ctx, pair, sigma, strategy, kernel_error::DERIVE_FST_PAIR)?;
        let tm = self.add(ctx, GNode::Fst([pair]));
        self.0.set_has_ty_unchecked(ctx, tm, arg_ty);
        if let &GNode::Pair([a, _]) = self.node(ctx, pair) {
            self.0.set_eq_unchecked(ctx, tm, a);
        }
        Ok(HasTyIn { tm, ty: arg_ty }.finish_rule(ctx, strategy))
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
        strategy.start_rule("derive_snd")?;
        let sigma = self.add(ctx, GNode::Sigma([arg_ty, res_ty]));
        self.ensure_has_ty(ctx, pair, sigma, strategy, kernel_error::DERIVE_SND_PAIR)?;
        let fst = self.add(ctx, GNode::Fst([pair]));
        self.0.set_has_ty_unchecked(ctx, fst, arg_ty);
        let tm = self.add(ctx, GNode::Snd([pair]));
        let ty = self.subst(ctx, fst, res_ty);
        self.0.set_has_ty_unchecked(ctx, tm, ty);
        if let &GNode::Pair([a, b]) = self.node(ctx, pair) {
            self.0.set_eq_unchecked(ctx, fst, a);
            self.0.set_eq_unchecked(ctx, tm, b);
        }
        Ok(HasTyIn { tm, ty }.finish_rule(ctx, strategy))
    }

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
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_dite")?;
        self.ensure_is_prop(ctx, cond, strategy, kernel_error::DERIVE_DITE_COND)?;
        self.ensure_has_ty_under(
            ctx,
            cond,
            then_br,
            ty,
            strategy,
            kernel_error::DERIVE_DITE_THEN_BR,
        )?;
        let ff = self.add(ctx, GNode::Empty);
        let not_cond = self.add(ctx, GNode::Eqn([cond, ff]));
        self.ensure_has_ty_under(
            ctx,
            not_cond,
            else_br,
            ty,
            strategy,
            kernel_error::DERIVE_DITE_ELSE_BR,
        )?;
        let tm = self.add(ctx, GNode::Ite([cond, then_br, else_br]));
        self.0.set_has_ty_unchecked(ctx, tm, ty);
        if self.is_inhab(ctx, cond) {
            let null = self.add(ctx, GNode::Null);
            let then_br_null = self.subst(ctx, null, then_br);
            self.0.set_eq_unchecked(ctx, tm, then_br_null);
        } else if self.is_empty(ctx, cond) {
            let null = self.add(ctx, GNode::Null);
            let else_br_null = self.subst(ctx, null, else_br);
            self.0.set_eq_unchecked(ctx, tm, else_br_null);
        }
        Ok(HasTyIn { tm, ty }.finish_rule(ctx, strategy))
    }

    fn derive_trunc<S>(&mut self, ctx: C, ty: T, strategy: &mut S) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_trunc")?;
        self.ensure_is_ty(ctx, ty, strategy, kernel_error::DERIVE_TRUNC_TY)?;
        let tm = self.add(ctx, GNode::Trunc([ty]));
        let prop = self.add(ctx, GNode::U(ULvl::PROP));
        self.0.set_has_ty_unchecked(ctx, tm, prop);
        if self.is_inhab(ctx, ty) {
            self.0.set_is_inhab_unchecked(ctx, tm);
        }
        if self.is_empty(ctx, ty) {
            self.0.set_is_empty_unchecked(ctx, tm);
        }
        Ok(HasTyIn { tm, ty: prop }.finish_rule(ctx, strategy))
    }

    fn derive_choose<S>(
        &mut self,
        ctx: C,
        ty: T,
        pred: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_choose")?;
        self.ensure_is_inhab(ctx, ty, strategy, kernel_error::DERIVE_CHOOSE_TY)?;
        let prop = self.add(ctx, GNode::U(ULvl::PROP));
        self.ensure_has_ty_under(
            ctx,
            ty,
            pred,
            prop,
            strategy,
            kernel_error::DERIVE_CHOOSE_PRED,
        )?;
        let tm = self.add(ctx, GNode::Choose([ty, pred]));
        self.0.set_has_ty_unchecked(ctx, tm, ty);
        Ok(HasTyIn { tm, ty }.finish_rule(ctx, strategy))
    }

    fn derive_nats<S>(&mut self, ctx: C, lvl: ULvl, strategy: &mut S) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_nats")?;
        if !self.u_le(ULvl::SET, lvl) {
            return Err(strategy.fail(kernel_error::DERIVE_NATS_SET_LE_LVL));
        }
        let tm = self.add(ctx, GNode::Nats);
        let ty = self.add(ctx, GNode::U(lvl));
        self.0.set_has_ty_unchecked(ctx, tm, ty);
        Ok(HasTyIn { tm, ty }.finish_rule(ctx, strategy))
    }

    fn derive_n64(&mut self, ctx: C, n: u64) -> HasTyIn<T> {
        let tm = self.add(ctx, GNode::N64(n));
        let ty = self.add(ctx, GNode::Nats);
        self.0.set_has_ty_unchecked(ctx, tm, ty);
        HasTyIn { tm, ty }
    }

    fn derive_succ<S>(&mut self, ctx: C, n: T, strategy: &mut S) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_succ")?;
        let nats = self.add(ctx, GNode::Nats);
        self.ensure_has_ty(ctx, n, nats, strategy, kernel_error::DERIVE_SUCC_N)?;
        let tm = self.add(ctx, GNode::Succ([n]));
        self.0.set_has_ty_unchecked(ctx, tm, nats);
        Ok(HasTyIn { tm, ty: nats }.finish_rule(ctx, strategy))
    }

    fn derive_natrec<S>(
        &mut self,
        ctx: C,
        mot: T,
        z: T,
        s: T,
        strategy: &mut S,
    ) -> Result<HasTyIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_natrec")?;
        let nats = self.add(ctx, GNode::Nats);
        self.ensure_is_ty_under(ctx, nats, mot, strategy, kernel_error::DERIVE_NATREC_MOT)?;
        debug_assert!(
            self.bvi(ctx, mot) <= Bv(1),
            "a term which is well-typed under a binder cannot have a bvi greater than one"
        );
        let zero = self.add(ctx, GNode::N64(0));
        let mot_zero = self.subst(ctx, mot, zero);
        self.ensure_has_ty(ctx, z, mot_zero, strategy, kernel_error::DERIVE_NATREC_Z)?;
        let bv_one = self.add(ctx, GNode::Bv(Bv(1)));
        let succ_bv_one = self.add(ctx, GNode::Succ([bv_one]));
        debug_assert_eq!(self.bvi(ctx, succ_bv_one), Bv(2));
        let mot_succ_bv_one = self.subst(ctx, mot, succ_bv_one);
        debug_assert!(self.bvi(ctx, mot_succ_bv_one) <= Bv(2));
        let mot_to_mot_succ = self.add(ctx, GNode::Pi([mot, mot_succ_bv_one]));
        debug_assert!(self.bvi(ctx, mot_to_mot_succ) <= Bv(1));
        self.ensure_has_ty_under(
            ctx,
            nats,
            s,
            mot_to_mot_succ,
            strategy,
            kernel_error::DERIVE_NATREC_S,
        )?;

        let tm = self.add(ctx, GNode::Natrec([mot, z, s]));
        let ty = self.add(ctx, GNode::Pi([nats, mot]));
        self.0.set_has_ty_unchecked(ctx, tm, ty);
        Ok(HasTyIn { tm, ty: nats }.finish_rule(ctx, strategy))
    }

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
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_let")?;
        self.ensure_has_ty(
            ctx,
            bound,
            bound_ty,
            strategy,
            kernel_error::DERIVE_LET_BOUND,
        )?;
        self.ensure_has_ty_under(
            ctx,
            bound_ty,
            body,
            body_ty,
            strategy,
            kernel_error::DERIVE_LET_BODY,
        )?;
        let tm = self.add(ctx, GNode::Let(Bv(0), [bound, body]));
        let ty = self.subst(ctx, bound, body_ty);
        self.0.set_has_ty_unchecked(ctx, tm, ty);
        let tm_s = self.subst(ctx, bound, body);
        self.0.set_eq_unchecked(ctx, tm, tm_s);
        Ok(HasTyIn { tm, ty }.finish_rule(ctx, strategy))
    }

    fn derive_beta_abs<S>(
        &mut self,
        ctx: C,
        tm: T,
        arg: T,
        strategy: &mut S,
    ) -> Result<Eqn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_beta_abs")?;
        let &GNode::Abs([arg_ty, body]) = self.node(ctx, tm) else {
            return Err(strategy.fail("derive_beta_abs: tm ≡ abs A b"));
        };
        self.ensure_is_wf(ctx, tm, strategy, "derive_beta_abs: tm wf")?;
        self.ensure_has_ty(ctx, arg, arg_ty, strategy, "derive_beta_abs: arg")?;
        let tm_app = self.add(ctx, GNode::App([tm, arg]));
        let tm_subst = self.subst(ctx, arg, body);
        self.0.set_eq_unchecked(ctx, tm_app, tm_subst);
        Ok(Eqn {
            lhs: tm_app,
            rhs: tm_subst,
        }
        .finish_rule(ctx, strategy))
    }

    fn derive_beta_zero<S>(&mut self, ctx: C, tm: T, strategy: &mut S) -> Result<Eqn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_beta_zero")?;
        let &GNode::Natrec([_mot, z, _s]) = self.node(ctx, tm) else {
            return Err(strategy.fail("derive_beta_zero: tm ≡ natrec C z s"));
        };
        self.ensure_is_wf(ctx, tm, strategy, "derive_beta_zero: tm wf")?;
        let zero = self.add(ctx, GNode::N64(0));
        let tm_zero = self.add(ctx, GNode::App([tm, zero]));
        self.0.set_eq_unchecked(ctx, tm_zero, z);
        Ok(Eqn {
            lhs: tm_zero,
            rhs: zero,
        }
        .finish_rule(ctx, strategy))
    }

    fn derive_beta_succ<S>(
        &mut self,
        ctx: C,
        tm: T,
        n: T,
        strategy: &mut S,
    ) -> Result<Eqn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_beta_succ")?;
        let &GNode::Natrec([_mot, _z, s]) = self.node(ctx, tm) else {
            return Err(strategy.fail("derive_beta_zero: tm ≡ natrec C z s"));
        };
        self.ensure_is_wf(ctx, tm, strategy, "derive_beta_zero: tm wf")?;
        let nats = self.add(ctx, GNode::Nats);
        self.ensure_has_ty(ctx, n, nats, strategy, "derive_beta_succ: n")?;
        let tm_n = self.add(ctx, GNode::App([tm, n]));
        let s_n = self.subst(ctx, n, s);
        let s_n_tm_n = self.add(ctx, GNode::App([s_n, tm_n]));
        let succ_n = self.add(ctx, GNode::Succ([n]));
        let tm_succ_n = self.add(ctx, GNode::App([tm, succ_n]));
        self.0.set_eq_unchecked(ctx, tm_succ_n, s_n_tm_n);
        Ok(Eqn {
            lhs: tm_succ_n,
            rhs: s_n_tm_n,
        }
        .finish_rule(ctx, strategy))
    }

    fn derive_choose_spec<S>(
        &mut self,
        ctx: C,
        ty: T,
        pred: T,
        strategy: &mut S,
    ) -> Result<IsInhabIn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_choose_spec")?;
        self.ensure_exists_inhab_under(ctx, ty, pred, strategy, "derive_choose_spec: exists")?;
        let choose = self.add(ctx, GNode::Choose([ty, pred]));
        let pred_choose = self.subst(ctx, choose, pred);
        self.0.set_has_ty_unchecked(ctx, choose, ty);
        self.0.set_is_prop_unchecked(ctx, pred_choose);
        self.0.set_is_inhab_unchecked(ctx, pred_choose);
        Ok(IsInhabIn(pred_choose).finish_rule(ctx, strategy))
    }

    fn derive_unit_ext<S>(&mut self, ctx: C, a: T, strategy: &mut S) -> Result<Eqn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_unit_ext")?;
        let unit = self.add(ctx, GNode::Unit);
        self.ensure_has_ty(ctx, a, unit, strategy, "derive_unit_ext: a")?;
        let null = self.add(ctx, GNode::Null);
        self.0.set_eq_unchecked(ctx, a, null);
        Ok(Eqn { lhs: a, rhs: null }.finish_rule(ctx, strategy))
    }

    fn derive_prop_ext_tt<S>(&mut self, ctx: C, a: T, strategy: &mut S) -> Result<Eqn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_prop_ext_tt")?;
        self.ensure_is_prop(ctx, a, strategy, "derive_prop_ext_tt: a prop")?;
        self.ensure_is_inhab(ctx, a, strategy, "derive_prop_ext_tt: a inhab")?;
        let unit = self.add(ctx, GNode::Unit);
        self.0.set_eq_unchecked(ctx, a, unit);
        Ok(Eqn { lhs: a, rhs: unit }.finish_rule(ctx, strategy))
    }

    fn derive_prop_ext_ff<S>(&mut self, ctx: C, a: T, strategy: &mut S) -> Result<Eqn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_prop_ext_ff")?;
        self.ensure_is_prop(ctx, a, strategy, "derive_prop_ext_ff: a prop")?;
        self.ensure_is_empty(ctx, a, strategy, "derive_prop_ext_ff: a empty")?;
        let empty = self.add(ctx, GNode::Empty);
        self.0.set_eq_unchecked(ctx, a, empty);
        Ok(Eqn { lhs: a, rhs: empty }.finish_rule(ctx, strategy))
    }

    fn derive_ext<S>(&mut self, ctx: C, lhs: T, rhs: T, strategy: &mut S) -> Result<Eqn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_ext")?;
        let eqn = self.add(ctx, GNode::Eqn([lhs, rhs]));
        self.ensure_is_inhab(ctx, eqn, strategy, "derive_ext: eqn inhab")?;
        self.0.set_eq_unchecked(ctx, lhs, rhs);
        Ok(Eqn { lhs, rhs }.finish_rule(ctx, strategy))
    }

    fn derive_pi_eta<S>(&mut self, ctx: C, ty: T, f: T, strategy: &mut S) -> Result<Eqn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_pi_eta")?;
        let &GNode::Pi([arg_ty, _res_ty]) = self.node(ctx, ty) else {
            return Err(strategy.fail("derive_pi_eta: ty ≡ pi A B"));
        };
        self.ensure_has_ty(ctx, f, ty, strategy, "derive_pi_eta: f")?;
        let bv_zero = self.add(ctx, GNode::Bv(Bv(0)));
        let app_f_bv_zero = self.add(ctx, GNode::App([f, bv_zero]));
        let eta = self.add(ctx, GNode::Abs([arg_ty, app_f_bv_zero]));
        self.0.set_eq_unchecked(ctx, f, eta);
        Ok(Eqn { lhs: f, rhs: eta }.finish_rule(ctx, strategy))
    }

    fn derive_sigma_eta<S>(
        &mut self,
        ctx: C,
        ty: T,
        p: T,
        strategy: &mut S,
    ) -> Result<Eqn<T>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        strategy.start_rule("derive_sigma_eta")?;
        let &GNode::Sigma(_) = self.node(ctx, ty) else {
            return Err(strategy.fail("derive_sigma_eta: ty ≡ sigma A B"));
        };
        self.ensure_has_ty(ctx, p, ty, strategy, "derive_sigma_eta: p")?;
        let fst_p = self.add(ctx, GNode::Fst([p]));
        let snd_p = self.add(ctx, GNode::Snd([p]));
        let eta = self.add(ctx, GNode::Pair([fst_p, snd_p]));
        self.0.set_eq_unchecked(ctx, p, eta);
        Ok(Eqn { lhs: p, rhs: eta }.finish_rule(ctx, strategy))
    }
}

pub trait KernelAPI<C: Copy, T: Copy + PartialEq>:
    Derive<C, T> + Ensure<C, T> + TermStore<C, T> + ReadFacts<C, T>
{
}

impl<K, C: Copy, T: Copy + PartialEq> KernelAPI<C, T> for K where
    K: Derive<C, T> + Ensure<C, T> + TermStore<C, T> + ReadFacts<C, T>
{
}
