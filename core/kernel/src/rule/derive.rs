// use crate::data::term::Close;
// use crate::data::term::{Bv, Fv, NodeT, ULvl, Val};
// use crate::fact::*;
// use crate::store::*;
// use crate::strategy::*;

// use crate::Kernel;

// use super::ensure::*;

// impl<C, T, D> WriteTrusted<C, T> for Kernel<D>
// where
//     C: Copy + PartialEq,
//     T: Copy + PartialEq,
//     D: ReadTermDb<C, T> + WriteLocalTerm<CtxId = C, Ix = T> + WriteFacts<C, T>,
// {
//     fn add_ix(&mut self, ctx: C, tm: NodeT<C, T>) -> Val<C, T> {
//         let flags = super::pred::infer_flags(tm, ctx, self.read());
//         let tm = self.0.add_raw(ctx, tm);
//         self.0.set_tm_flags_unchecked(ctx, tm, flags);
//         Val { ctx, tm }
//     }
// }

// impl<C, T, D, S> DeriveTrusted<C, T, S> for Kernel<D>
// where
//     C: Copy + PartialEq,
//     T: Copy + PartialEq,
//     D: ReadTermDb<C, T> + WriteLocalTerm<CtxId = C, Ix = T> + WriteFacts<C, T>,
//     S: Strategy<C, T, Self>,
// {
//     fn add_var(&mut self, ctx: C, ty: Val<C, T>, strategy: &mut S) -> Result<Fv<C>, S::Fail> {
//         strategy.start_rule("add_var", self)?;

//         self.ensure_is_ty(ctx, ty, strategy, "")?;

//         strategy.commit_rule(self);

//         let var = self.0.add_var_unchecked(ctx, ty);

//         //TODO: think about whether we should do this? more? at the `add_ix` level (probably!)?
//         let _x = self.add_ix(ctx, NodeT::Fv(var));

//         strategy.finish_rule(self);
//         Ok(var)
//     }

//     fn set_parent(&mut self, ctx: C, parent: C, strategy: &mut S) -> Result<IsSubctx<C>, S::Fail> {
//         strategy.start_rule("set_parent", self)?;

//         if self.read().is_ancestor(ctx, parent) {
//             return Err(strategy.fail("", self));
//         }
//         if !self.read().parents_are_subctx(ctx, parent) {
//             return Err(strategy.fail("", self));
//         }

//         strategy.commit_rule(self);

//         self.0.set_parent_unchecked(ctx, parent);
//         let result = IsSubctx {
//             lo: parent,
//             hi: ctx,
//         };

//         strategy.finish_rule(self);
//         Ok(result)
//     }

//     fn derive_u_le(
//         &mut self,
//         ctx: C,
//         tm: Val<C, T>,
//         lo: ULvl,
//         hi: ULvl,
//         strategy: &mut S,
//     ) -> Result<HasTyV<C, T>, S::Fail> {
//         strategy.start_rule("derive_u_le", self)?;

//         if !self.read().u_le(lo, hi) {
//             return Err(strategy.fail("", self));
//         }
//         let old = self.resolve(ctx, NodeT::U(lo), strategy)?;
//         self.ensure_has_ty(ctx, tm, old, strategy, "")?;

//         strategy.commit_rule(self);

//         let tm = self.import_with(ctx, tm, strategy)?;
//         let ty = self.add_with(ctx, NodeT::U(hi), strategy)?;
//         self.0.set_has_ty_unchecked(ctx, tm, ty);

//         strategy.finish_rule(self);
//         Ok(HasTyV {
//             ctx,
//             tm: self.read().val(ctx, tm),
//             ty: self.read().val(ctx, ty),
//         })
//     }

//     fn derive_close_has_ty_under(
//         &mut self,
//         ctx: C,
//         var: Fv<C>,
//         tm: Val<C, T>,
//         ty: Val<C, T>,
//         strategy: &mut S,
//     ) -> Result<HasTyUnderV<C, T>, S::Fail> {
//         strategy.start_rule("derive_close_has_ty_under", self)?;

//         // Let Γ = ctx, Δ = var.ctx, a = tm, B = ty

//         // This rule only supports single-variable closures
//         if var.ix != 0 {
//             return Err(strategy.fail("", self));
//         }

//         // The variable closed over must be valid
//         if var.ix >= self.read().num_vars(var.ctx) {
//             return Err(strategy.fail("", self));
//         }

//         // We begin by checking that Δ ⊢ a : B
//         self.ensure_has_ty(var.ctx, tm, ty, strategy, "")?;

//         // For foreign-context closures...
//         if var.ctx != ctx {
//             debug_assert_ne!(
//                 self.read().num_vars(var.ctx),
//                 0,
//                 "var is a valid variable, so there must be at least one variable"
//             );
//             // We check that `var` is the only variable in its context
//             //
//             // We might loosen this check later
//             if self.read().num_vars(var.ctx) != 1 {
//                 return Err(strategy.fail("", self));
//             }
//             // We check that Δ = Δ', x : A where Δ' ≤ Γ
//             if !self.read().parents_are_subctx(var.ctx, ctx) {
//                 return Err(strategy.fail("", self));
//             }
//         }

//         strategy.commit_rule(self);

//         let binder = self.read().var_ty(var);
//         let binder = self.import_with(ctx, binder, strategy)?;
//         let close_tm = self.add_with(ctx, NodeT::Close(Close::new(var, tm)), strategy)?;
//         let close_ty = self.add_with(ctx, NodeT::Close(Close::new(var, ty)), strategy)?;

//         self.0
//             .set_forall_has_ty_unchecked(ctx, binder, close_tm, close_ty);

//         strategy.finish_rule(self);
//         Ok(HasTyUnderV {
//             ctx,
//             tm: self.read().val(ctx, close_tm),
//             ty: self.read().val(ctx, close_ty),
//             binder: self.read().val(ctx, binder),
//         })
//     }

//     fn derive_fv(&mut self, ctx: C, var: Fv<C>, strategy: &mut S) -> Result<HasTyV<C, T>, S::Fail> {
//         strategy.start_rule("derive_fv", self)?;

//         // Check the variable is well-scoped
//         if !self.read().is_subctx(var.ctx, ctx) || var.ix >= self.read().num_vars(var.ctx) {
//             return Err(strategy.fail("", self));
//         }

//         strategy.commit_rule(self);

//         let tm = self.add_with(ctx, NodeT::Fv(var), strategy)?;
//         let ty = self.import_with(ctx, self.read().var_ty(var), strategy)?;
//         self.0.set_has_ty_unchecked(ctx, tm, ty);

//         strategy.finish_rule(self);
//         Ok(HasTyV {
//             ctx,
//             tm: self.read().val(ctx, tm),
//             ty: self.read().val(ctx, ty),
//         })
//     }

//     fn derive_univ(
//         &mut self,
//         ctx: C,
//         lvl: ULvl,
//         strategy: &mut S,
//     ) -> Result<HasTyV<C, T>, S::Fail> {
//         strategy.start_rule("derive_univ", self)?;

//         strategy.commit_rule(self);

//         let tm = self.add_with(ctx, NodeT::U(lvl), strategy)?;
//         let ty_lvl = self.succ(lvl);
//         let ty = self.add_with(ctx, NodeT::U(ty_lvl), strategy)?;
//         self.0.set_has_ty_unchecked(ctx, tm, ty);

//         strategy.finish_rule(self);
//         Ok(HasTyV {
//             ctx,
//             tm: self.read().val(ctx, tm),
//             ty: self.read().val(ctx, ty),
//         })
//     }

//     fn derive_unit(
//         &mut self,
//         ctx: C,
//         lvl: ULvl,
//         strategy: &mut S,
//     ) -> Result<HasTyV<C, T>, S::Fail> {
//         strategy.start_rule("derive_unit", self)?;

//         strategy.commit_rule(self);

//         let tm = self.add_with(ctx, NodeT::Unit, strategy)?;
//         let ty = self.add_with(ctx, NodeT::U(lvl), strategy)?;
//         self.0.set_has_ty_unchecked(ctx, tm, ty);
//         self.0.set_is_prop_unchecked(ctx, tm);
//         self.0.set_is_inhab_unchecked(ctx, tm);

//         strategy.finish_rule(self);
//         Ok(HasTyV {
//             ctx,
//             tm: self.read().val(ctx, tm),
//             ty: self.read().val(ctx, ty),
//         })
//     }

//     fn derive_nil(&mut self, ctx: C, strategy: &mut S) -> Result<HasTyV<C, T>, S::Fail> {
//         strategy.start_rule("derive_nil", self)?;

//         strategy.commit_rule(self);

//         let tm = self.add_with(ctx, NodeT::Null, strategy)?;
//         let ty = self.add_with(ctx, NodeT::Unit, strategy)?;
//         self.0.set_has_ty_unchecked(ctx, tm, ty);

//         strategy.finish_rule(self);
//         Ok(HasTyV {
//             ctx,
//             tm: self.read().val(ctx, tm),
//             ty: self.read().val(ctx, ty),
//         })
//     }

//     fn derive_empty(
//         &mut self,
//         ctx: C,
//         lvl: ULvl,
//         strategy: &mut S,
//     ) -> Result<HasTyV<C, T>, S::Fail> {
//         strategy.start_rule("derive_empty", self)?;

//         strategy.commit_rule(self);

//         let tm = self.add_with(ctx, NodeT::Empty, strategy)?;
//         let ty = self.add_with(ctx, NodeT::U(lvl), strategy)?;
//         self.0.set_has_ty_unchecked(ctx, tm, ty);
//         self.0.set_is_ff_unchecked(ctx, tm);

//         strategy.finish_rule(self);
//         Ok(HasTyV {
//             ctx,
//             tm: self.read().val(ctx, tm),
//             ty: self.read().val(ctx, ty),
//         })
//     }

//     fn derive_eqn(
//         &mut self,
//         ctx: C,
//         ty: Val<C, T>,
//         lhs: Val<C, T>,
//         rhs: Val<C, T>,
//         strategy: &mut S,
//     ) -> Result<HasTyV<C, T>, S::Fail> {
//         strategy.start_rule("derive_eqn", self)?;

//         self.ensure_has_ty(ctx, lhs, ty, strategy, "")?;
//         self.ensure_has_ty(ctx, rhs, ty, strategy, "")?;

//         strategy.commit_rule(self);

//         let tm = self.add_with(ctx, NodeT::Eqn([lhs, rhs]), strategy)?;
//         let ty = self.add_with(ctx, NodeT::U(ULvl::PROP), strategy)?;
//         self.0.set_has_ty_unchecked(ctx, tm, ty);

//         strategy.finish_rule(self);
//         Ok(HasTyV {
//             ctx,
//             tm: self.read().val(ctx, tm),
//             ty: self.read().val(ctx, ty),
//         })
//     }

//     fn derive_pi(
//         &mut self,
//         ctx: C,
//         arg_lvl: ULvl,
//         lvl: ULvl,
//         arg_ty: Val<C, T>,
//         res_ty: Val<C, T>,
//         strategy: &mut S,
//     ) -> Result<HasTyV<C, T>, S::Fail> {
//         strategy.start_rule("derive_pi", self)?;

//         if !self.read().imax_le(arg_lvl, lvl, lvl) {
//             return Err(strategy.fail("", self));
//         }

//         let arg_lvl_ty = self.resolve(ctx, NodeT::U(arg_lvl), strategy)?;
//         self.ensure_has_ty(ctx, arg_ty, arg_lvl_ty, strategy, "")?;

//         let ty = self.resolve(ctx, NodeT::U(lvl), strategy)?;
//         self.ensure_forall_has_ty(ctx, arg_ty, res_ty, ty, strategy, "")?;

//         strategy.commit_rule(self);

//         let tm = self.add_with(ctx, NodeT::Pi([arg_ty, res_ty]), strategy)?;
//         let ty = self.import_with(ctx, ty, strategy)?;
//         self.0.set_has_ty_unchecked(ctx, tm, ty);

//         strategy.finish_rule(self);
//         Ok(HasTyV {
//             ctx,
//             tm: self.read().val(ctx, tm),
//             ty: self.read().val(ctx, ty),
//         })
//     }

//     fn derive_sigma(
//         &mut self,
//         ctx: C,
//         lvl: ULvl,
//         arg_ty: Val<C, T>,
//         res_ty: Val<C, T>,
//         strategy: &mut S,
//     ) -> Result<HasTyV<C, T>, S::Fail> {
//         strategy.start_rule("derive_sigma", self)?;

//         let ty = self.resolve(ctx, NodeT::U(lvl), strategy)?;
//         self.ensure_has_ty(ctx, arg_ty, ty, strategy, "")?;
//         self.ensure_forall_has_ty(ctx, arg_ty, res_ty, ty, strategy, "")?;

//         strategy.commit_rule(self);

//         let tm = self.add_with(ctx, NodeT::Sigma([arg_ty, res_ty]), strategy)?;
//         let ty = self.import_with(ctx, ty, strategy)?;
//         self.0.set_has_ty_unchecked(ctx, tm, ty);

//         strategy.finish_rule(self);
//         Ok(HasTyV {
//             ctx,
//             tm: self.read().val(ctx, tm),
//             ty: self.read().val(ctx, ty),
//         })
//     }

//     fn derive_abs(
//         &mut self,
//         ctx: C,
//         arg_ty: Val<C, T>,
//         body: Val<C, T>,
//         res_ty: Val<C, T>,
//         strategy: &mut S,
//     ) -> Result<HasTyV<C, T>, S::Fail> {
//         strategy.start_rule("derive_abs", self)?;

//         self.ensure_forall_has_ty(ctx, arg_ty, body, res_ty, strategy, "")?;

//         strategy.commit_rule(self);

//         let tm = self.add_with(ctx, NodeT::Abs([arg_ty, body]), strategy)?;
//         let ty = self.add_with(ctx, NodeT::Pi([arg_ty, res_ty]), strategy)?;
//         self.0.set_has_ty_unchecked(ctx, tm, ty);

//         strategy.finish_rule(self);
//         Ok(HasTyV {
//             ctx,
//             tm: self.read().val(ctx, tm),
//             ty: self.read().val(ctx, ty),
//         })
//     }

//     fn derive_app(
//         &mut self,
//         ctx: C,
//         arg_ty: Val<C, T>,
//         res_ty: Val<C, T>,
//         func: Val<C, T>,
//         arg: Val<C, T>,
//         strategy: &mut S,
//     ) -> Result<HasTyV<C, T>, S::Fail> {
//         strategy.start_rule("derive_app", self)?;

//         self.ensure_has_ty(ctx, arg, arg_ty, strategy, "")?;
//         let pi = self.resolve(ctx, NodeT::Pi([arg_ty, res_ty]), strategy)?;
//         self.ensure_has_ty(ctx, func, pi, strategy, "")?;

//         strategy.commit_rule(self);

//         let tm = self.add_with(ctx, NodeT::App([func, arg]), strategy)?;
//         let ty = self.add_with(ctx, NodeT::subst1(arg, res_ty), strategy)?;
//         self.0.set_has_ty_unchecked(ctx, tm, ty);

//         strategy.finish_rule(self);
//         Ok(HasTyV {
//             ctx,
//             tm: self.read().val(ctx, tm),
//             ty: self.read().val(ctx, ty),
//         })
//     }

//     fn derive_pair(
//         &mut self,
//         ctx: C,
//         arg_ty: Val<C, T>,
//         res_ty: Val<C, T>,
//         fst: Val<C, T>,
//         snd: Val<C, T>,
//         strategy: &mut S,
//     ) -> Result<HasTyV<C, T>, S::Fail> {
//         strategy.start_rule("derive_pair", self)?;

//         self.ensure_is_ty_under(ctx, arg_ty, res_ty, strategy, "")?;
//         self.ensure_has_ty(ctx, fst, arg_ty, strategy, "")?;
//         let snd_ty = self.resolve(ctx, NodeT::subst1(fst, res_ty), strategy)?;
//         self.ensure_has_ty(ctx, snd, snd_ty, strategy, "")?;

//         strategy.commit_rule(self);

//         let tm = self.add_with(ctx, NodeT::Pair([fst, snd]), strategy)?;
//         let ty = self.add_with(ctx, NodeT::Sigma([arg_ty, res_ty]), strategy)?;
//         self.0.set_has_ty_unchecked(ctx, tm, ty);

//         strategy.finish_rule(self);
//         Ok(HasTyV {
//             ctx,
//             tm: self.read().val(ctx, tm),
//             ty: self.read().val(ctx, ty),
//         })
//     }

//     fn derive_fst(
//         &mut self,
//         ctx: C,
//         arg_ty: Val<C, T>,
//         res_ty: Val<C, T>,
//         pair: Val<C, T>,
//         strategy: &mut S,
//     ) -> Result<HasTyV<C, T>, S::Fail> {
//         strategy.start_rule("derive_fst", self)?;

//         let sigma = self.resolve(ctx, NodeT::Sigma([arg_ty, res_ty]), strategy)?;
//         self.ensure_has_ty(ctx, pair, sigma, strategy, "")?;

//         strategy.commit_rule(self);

//         let tm = self.add_with(ctx, NodeT::Fst([pair]), strategy)?;
//         let ty = self.import_with(ctx, arg_ty, strategy)?;
//         self.0.set_has_ty_unchecked(ctx, tm, ty);

//         strategy.finish_rule(self);
//         Ok(HasTyV {
//             ctx,
//             tm: self.read().val(ctx, tm),
//             ty: self.read().val(ctx, ty),
//         })
//     }

//     fn derive_snd(
//         &mut self,
//         ctx: C,
//         arg_ty: Val<C, T>,
//         res_ty: Val<C, T>,
//         pair: Val<C, T>,
//         strategy: &mut S,
//     ) -> Result<HasTyV<C, T>, S::Fail> {
//         strategy.start_rule("derive_snd", self)?;

//         let sigma = self.resolve(ctx, NodeT::Sigma([arg_ty, res_ty]), strategy)?;
//         self.ensure_has_ty(ctx, pair, sigma, strategy, "")?;

//         strategy.commit_rule(self);

//         let fst = self.resolve(ctx, NodeT::Fst([pair]), strategy)?;
//         let tm = self.add_with(ctx, NodeT::Snd([pair]), strategy)?;
//         let ty = self.add_with(ctx, NodeT::subst1(fst, res_ty), strategy)?;
//         self.0.set_has_ty_unchecked(ctx, tm, ty);

//         strategy.finish_rule(self);
//         Ok(HasTyV {
//             ctx,
//             tm: self.read().val(ctx, tm),
//             ty: self.read().val(ctx, ty),
//         })
//     }

//     fn derive_dite(
//         &mut self,
//         ctx: C,
//         cond: Val<C, T>,
//         then_br: Val<C, T>,
//         else_br: Val<C, T>,
//         ty: Val<C, T>,
//         strategy: &mut S,
//     ) -> Result<HasTyV<C, T>, S::Fail> {
//         strategy.start_rule("derive_dite", self)?;

//         self.ensure_is_prop(ctx, cond, strategy, "")?;
//         self.ensure_forall_has_ty(ctx, cond, then_br, ty, strategy, "")?;
//         let ff = self.resolve(ctx, NodeT::Empty, strategy)?;
//         let not_cond = self.resolve(ctx, NodeT::Eqn([cond, ff]), strategy)?;
//         self.ensure_forall_has_ty(ctx, not_cond, else_br, ty, strategy, "")?;

//         strategy.commit_rule(self);

//         let tm = self.add_with(ctx, NodeT::Ite([cond, then_br, else_br]), strategy)?;
//         let ty = self.import_with(ctx, ty, strategy)?;
//         self.0.set_has_ty_unchecked(ctx, tm, ty);

//         strategy.finish_rule(self);
//         Ok(HasTyV {
//             ctx,
//             tm: self.read().val(ctx, tm),
//             ty: self.read().val(ctx, ty),
//         })
//     }

//     fn derive_trunc(
//         &mut self,
//         ctx: C,
//         ty: Val<C, T>,
//         strategy: &mut S,
//     ) -> Result<HasTyV<C, T>, S::Fail> {
//         strategy.start_rule("derive_trunc", self)?;

//         self.ensure_is_ty(ctx, ty, strategy, "")?;

//         strategy.commit_rule(self);

//         let tm = self.add_with(ctx, NodeT::Trunc([ty]), strategy)?;
//         let ty = self.add_with(ctx, NodeT::U(ULvl::PROP), strategy)?;
//         self.0.set_has_ty_unchecked(ctx, tm, ty);

//         strategy.finish_rule(self);
//         Ok(HasTyV {
//             ctx,
//             tm: self.read().val(ctx, tm),
//             ty: self.read().val(ctx, ty),
//         })
//     }

//     fn derive_choose(
//         &mut self,
//         ctx: C,
//         ty: Val<C, T>,
//         pred: Val<C, T>,
//         strategy: &mut S,
//     ) -> Result<HasTyV<C, T>, S::Fail> {
//         strategy.start_rule("derive_choose", self)?;

//         self.ensure_is_inhab(ctx, ty, strategy, "")?;
//         self.ensure_forall_is_prop(ctx, ty, pred, strategy, "")?;

//         strategy.commit_rule(self);

//         let tm = self.add_with(ctx, NodeT::Choose([ty, pred]), strategy)?;
//         let ty = self.import_with(ctx, ty, strategy)?;
//         self.0.set_has_ty_unchecked(ctx, tm, ty);

//         strategy.finish_rule(self);
//         Ok(HasTyV {
//             ctx,
//             tm: self.read().val(ctx, tm),
//             ty: self.read().val(ctx, ty),
//         })
//     }

//     fn derive_nats(
//         &mut self,
//         ctx: C,
//         lvl: ULvl,
//         strategy: &mut S,
//     ) -> Result<HasTyV<C, T>, S::Fail> {
//         strategy.start_rule("derive_nats", self)?;

//         if !self.read().u_le(ULvl::SET, lvl) {
//             return Err(strategy.fail("", self));
//         }

//         strategy.commit_rule(self);

//         let tm = self.add_with(ctx, NodeT::Nats, strategy)?;
//         let ty = self.add_with(ctx, NodeT::U(lvl), strategy)?;
//         self.0.set_has_ty_unchecked(ctx, tm, ty);

//         strategy.finish_rule(self);
//         Ok(HasTyV {
//             ctx,
//             tm: self.read().val(ctx, tm),
//             ty: self.read().val(ctx, ty),
//         })
//     }

//     fn derive_n64(&mut self, ctx: C, n: u64, strategy: &mut S) -> Result<HasTyV<C, T>, S::Fail> {
//         strategy.start_rule("derive_n64", self)?;

//         strategy.commit_rule(self);

//         let tm = self.add_with(ctx, NodeT::N64(n), strategy)?;
//         let ty = self.add_with(ctx, NodeT::Nats, strategy)?;
//         self.0.set_has_ty_unchecked(ctx, tm, ty);

//         strategy.finish_rule(self);
//         Ok(HasTyV {
//             ctx,
//             tm: self.read().val(ctx, tm),
//             ty: self.read().val(ctx, ty),
//         })
//     }

//     fn derive_succ(
//         &mut self,
//         ctx: C,
//         n: Val<C, T>,
//         strategy: &mut S,
//     ) -> Result<HasTyV<C, T>, S::Fail> {
//         strategy.start_rule("derive_succ", self)?;

//         let nats = self.resolve(ctx, NodeT::Nats, strategy)?;
//         self.ensure_has_ty(ctx, n, nats, strategy, "")?;

//         strategy.commit_rule(self);

//         let tm = self.add_with(ctx, NodeT::Succ([n]), strategy)?;
//         let ty = self.import_with(ctx, nats, strategy)?;
//         self.0.set_has_ty_unchecked(ctx, tm, ty);

//         strategy.finish_rule(self);
//         Ok(HasTyV {
//             ctx,
//             tm: self.read().val(ctx, tm),
//             ty: self.read().val(ctx, ty),
//         })
//     }

//     fn derive_natrec(
//         &mut self,
//         ctx: C,
//         mot: Val<C, T>,
//         z: Val<C, T>,
//         s: Val<C, T>,
//         strategy: &mut S,
//     ) -> Result<HasTyV<C, T>, S::Fail> {
//         strategy.start_rule("derive_natrec", self)?;

//         let nats = self.resolve(ctx, NodeT::Nats, strategy)?;
//         self.ensure_is_ty_under(ctx, nats, mot, strategy, "")?;

//         let zero = self.resolve(ctx, NodeT::N64(0), strategy)?;
//         let mot_zero = self.resolve(ctx, NodeT::subst1(zero, mot), strategy)?;
//         self.ensure_has_ty(ctx, z, mot_zero, strategy, "")?;

//         // NOT succ bv 0, since bv 0 is the variable bound by the Π-type!
//         let bv_one = self.resolve(ctx, NodeT::Bv(Bv(1)), strategy)?;
//         let succ_bv_one = self.resolve(ctx, NodeT::Succ([bv_one]), strategy)?;
//         let mot_succ_bv_one = self.resolve(ctx, NodeT::subst1(succ_bv_one, mot), strategy)?;
//         let mot_to_mot_succ = self.resolve(ctx, NodeT::Pi([mot, mot_succ_bv_one]), strategy)?;
//         self.ensure_forall_has_ty(ctx, nats, s, mot_to_mot_succ, strategy, "")?;

//         strategy.commit_rule(self);

//         let tm = self.add_with(ctx, NodeT::Natrec([mot, z, s]), strategy)?;
//         let ty = self.add_with(ctx, NodeT::Pi([nats, mot]), strategy)?;
//         self.0.set_has_ty_unchecked(ctx, tm, ty);

//         strategy.finish_rule(self);
//         Ok(HasTyV {
//             ctx,
//             tm: self.read().val(ctx, tm),
//             ty: self.read().val(ctx, ty),
//         })
//     }

//     fn derive_let(
//         &mut self,
//         ctx: C,
//         bound: Val<C, T>,
//         bound_ty: Val<C, T>,
//         body: Val<C, T>,
//         body_ty: Val<C, T>,
//         strategy: &mut S,
//     ) -> Result<HasTyV<C, T>, S::Fail> {
//         strategy.start_rule("derive_let", self)?;

//         self.ensure_has_ty(ctx, bound, bound_ty, strategy, "")?;
//         self.ensure_forall_has_ty(ctx, bound_ty, body, body_ty, strategy, "")?;

//         strategy.commit_rule(self);

//         let tm = self.add_with(ctx, NodeT::subst1(bound, body), strategy)?;
//         let ty = self.add_with(ctx, NodeT::subst1(bound, body_ty), strategy)?;
//         self.0.set_has_ty_unchecked(ctx, tm, ty);

//         strategy.finish_rule(self);
//         Ok(HasTyV {
//             ctx,
//             tm: self.read().val(ctx, tm),
//             ty: self.read().val(ctx, ty),
//         })
//     }

//     fn derive_beta_abs(
//         &mut self,
//         ctx: C,
//         tm: Val<C, T>,
//         arg: Val<C, T>,
//         strategy: &mut S,
//     ) -> Result<EqnInV<C, T>, S::Fail> {
//         strategy.start_rule("derive_beta_abs", self)?;

//         let NodeT::Abs([arg_ty, body]) = tm.node_val(self.read()) else {
//             return Err(strategy.fail("derive_beta_abs: tm ≡ abs A b", self));
//         };
//         self.ensure_is_wf(ctx, tm, strategy, "derive_beta_abs: tm wf")?;
//         self.ensure_has_ty(ctx, arg, arg_ty, strategy, "derive_beta_abs: arg")?;

//         strategy.commit_rule(self);

//         let lhs = self.add_with(ctx, NodeT::App([tm, arg]), strategy)?;
//         let rhs = self.add_with(ctx, NodeT::subst1(arg, body), strategy)?;
//         self.0.set_eq_unchecked(ctx, lhs, rhs);

//         strategy.finish_rule(self);
//         Ok(EqnInV::new(
//             ctx,
//             self.read().val(ctx, lhs),
//             self.read().val(ctx, rhs),
//         ))
//     }

//     // fn derive_beta_zero(
//     //     &mut self,
//     //     ctx: C,
//     //     tm: Val<C, T>,
//     //     strategy: &mut S,
//     // ) -> Result<EqnInV<C, T>, S::Fail> {
//     //     todo!()
//     //     // strategy.start_rule("derive_beta_zero")?;
//     //     // let &NodeT::Natrec([_mot, z, _s]) = self.read().node(ctx, tm) else {
//     //     //     return Err(strategy.fail("derive_beta_zero: tm ≡ natrec C z s"));
//     //     // };
//     //     // self.ensure_is_wf(ctx, tm, strategy, "derive_beta_zero: tm wf")?;
//     //     // let zero = self.add(ctx, NodeT::N64(0));
//     //     // let tm_zero = self.add(ctx, NodeT::App([tm, zero]));
//     //     // self.0.set_eq_unchecked(ctx, tm_zero, z);
//     //     // Ok(Eqn {
//     //     //     lhs: tm_zero,
//     //     //     rhs: zero,
//     //     // }
//     //     // .finish_rule(ctx, strategy))
//     // }

//     // fn derive_beta_succ(
//     //     &mut self,
//     //     ctx: C,
//     //     tm: Val<C, T>,
//     //     n: Val<C, T>,
//     //     strategy: &mut S,
//     // ) -> Result<EqnInV<C, T>, S::Fail> {
//     //     todo!()
//     //     // strategy.start_rule("derive_beta_succ")?;
//     //     // let &NodeT::Natrec([_mot, _z, s]) = self.read().node(ctx, tm) else {
//     //     //     return Err(strategy.fail("derive_beta_zero: tm ≡ natrec C z s"));
//     //     // };
//     //     // self.ensure_is_wf(ctx, tm, strategy, "derive_beta_zero: tm wf")?;
//     //     // let nats = self.add(ctx, NodeT::Nats);
//     //     // self.ensure_has_ty(ctx, n, nats, strategy, "derive_beta_succ: n")?;
//     //     // let tm_n = self.add(ctx, NodeT::App([tm, n]));
//     //     // let s_n = self.subst(ctx, n, s);
//     //     // let s_n_tm_n = self.add(ctx, NodeT::App([s_n, tm_n]));
//     //     // let succ_n = self.add(ctx, NodeT::Succ([n]));
//     //     // let tm_succ_n = self.add(ctx, NodeT::App([tm, succ_n]));
//     //     // self.0.set_eq_unchecked(ctx, tm_succ_n, s_n_tm_n);
//     //     // Ok(Eqn {
//     //     //     lhs: tm_succ_n,
//     //     //     rhs: s_n_tm_n,
//     //     // }
//     //     // .finish_rule(ctx, strategy))
//     // }

//     // fn derive_choose_spec(
//     //     &mut self,
//     //     ctx: C,
//     //     ty: Val<C, T>,
//     //     pred: Val<C, T>,
//     //     strategy: &mut S,
//     // ) -> Result<IsInhabV<C, T>, S::Fail> {
//     //     todo!()
//     //     // strategy.start_rule("derive_choose_spec")?;
//     //     // self.ensure_exists_inhab_under(ctx, ty, pred, strategy, "derive_choose_spec: exists")?;
//     //     // let choose = self.add(ctx, NodeT::Choose([ty, pred]));
//     //     // let pred_choose = self.subst(ctx, choose, pred);
//     //     // self.0.set_has_ty_unchecked(ctx, choose, ty);
//     //     // self.0.set_is_prop_unchecked(ctx, pred_choose);
//     //     // self.0.set_is_inhab_unchecked(ctx, pred_choose);
//     //     // Ok(IsInhabIn(pred_choose).finish_rule(ctx, strategy))
//     // }

//     // fn derive_unit_ext(
//     //     &mut self,
//     //     ctx: C,
//     //     a: Val<C, T>,
//     //     strategy: &mut S,
//     // ) -> Result<EqnInV<C, T>, S::Fail> {
//     //     todo!()
//     //     // strategy.start_rule("derive_unit_ext")?;
//     //     // let unit = self.add(ctx, NodeT::Unit);
//     //     // self.ensure_has_ty(ctx, a, unit, strategy, "derive_unit_ext: a")?;
//     //     // let null = self.add(ctx, NodeT::Null);
//     //     // self.0.set_eq_unchecked(ctx, a, null);
//     //     // Ok(Eqn { lhs: a, rhs: null }.finish_rule(ctx, strategy))
//     // }

//     // fn derive_prop_ext_tt(
//     //     &mut self,
//     //     ctx: C,
//     //     p: Val<C, T>,
//     //     strategy: &mut S,
//     // ) -> Result<EqnInV<C, T>, S::Fail> {
//     //     todo!()
//     //     // strategy.start_rule("derive_prop_ext_tt")?;
//     //     // self.ensure_is_prop(ctx, a, strategy, "derive_prop_ext_tt: a prop")?;
//     //     // self.ensure_is_inhab(ctx, a, strategy, "derive_prop_ext_tt: a inhab")?;
//     //     // let unit = self.add(ctx, NodeT::Unit);
//     //     // self.0.set_eq_unchecked(ctx, a, unit);
//     //     // Ok(Eqn { lhs: a, rhs: unit }.finish_rule(ctx, strategy))
//     // }

//     // fn derive_prop_ext_ff(
//     //     &mut self,
//     //     ctx: C,
//     //     p: Val<C, T>,
//     //     strategy: &mut S,
//     // ) -> Result<EqnInV<C, T>, S::Fail> {
//     //     todo!()
//     //     // strategy.start_rule("derive_prop_ext_ff")?;
//     //     // self.ensure_is_prop(ctx, a, strategy, "derive_prop_ext_ff: a prop")?;
//     //     // self.ensure_is_empty(ctx, a, strategy, "derive_prop_ext_ff: a empty")?;
//     //     // let empty = self.add(ctx, NodeT::Empty);
//     //     // self.0.set_eq_unchecked(ctx, a, empty);
//     //     // Ok(Eqn { lhs: a, rhs: empty }.finish_rule(ctx, strategy))
//     // }

//     // fn derive_ext(
//     //     &mut self,
//     //     ctx: C,
//     //     lhs: Val<C, T>,
//     //     rhs: Val<C, T>,
//     //     strategy: &mut S,
//     // ) -> Result<EqnInV<C, T>, S::Fail> {
//     //     todo!()
//     //     // strategy.start_rule("derive_ext")?;
//     //     // let eqn = self.add(ctx, NodeT::Eqn([lhs, rhs]));
//     //     // self.ensure_is_inhab(ctx, eqn, strategy, "derive_ext: eqn inhab")?;
//     //     // self.0.set_eq_unchecked(ctx, lhs, rhs);
//     //     // Ok(Eqn { lhs, rhs }.finish_rule(ctx, strategy))
//     // }

//     // fn derive_pi_eta(
//     //     &mut self,
//     //     ctx: C,
//     //     ty: Val<C, T>,
//     //     f: Val<C, T>,
//     //     strategy: &mut S,
//     // ) -> Result<EqnInV<C, T>, S::Fail> {
//     //     todo!()
//     //     // strategy.start_rule("derive_pi_eta")?;
//     //     // let &NodeT::Pi([arg_ty, _res_ty]) = self.read().node(ctx, ty) else {
//     //     //     return Err(strategy.fail("derive_pi_eta: ty ≡ pi A B"));
//     //     // };
//     //     // self.ensure_has_ty(ctx, f, ty, strategy, "derive_pi_eta: f")?;
//     //     // let bv_zero = self.add(ctx, NodeT::Bv(Bv(0)));
//     //     // let app_f_bv_zero = self.add(ctx, NodeT::App([f, bv_zero]));
//     //     // let eta = self.add(ctx, NodeT::Abs([arg_ty, app_f_bv_zero]));
//     //     // self.0.set_eq_unchecked(ctx, f, eta);
//     //     // Ok(Eqn { lhs: f, rhs: eta }.finish_rule(ctx, strategy))
//     // }

//     // fn derive_sigma_eta(
//     //     &mut self,
//     //     ctx: C,
//     //     ty: Val<C, T>,
//     //     p: Val<C, T>,
//     //     strategy: &mut S,
//     // ) -> Result<EqnInV<C, T>, S::Fail> {
//     //     todo!()
//     //     // strategy.start_rule("derive_sigma_eta")?;
//     //     // let &NodeT::Sigma(_) = self.read().node(ctx, ty) else {
//     //     //     return Err(strategy.fail("derive_sigma_eta: ty ≡ sigma A B"));
//     //     // };
//     //     // self.ensure_has_ty(ctx, p, ty, strategy, "derive_sigma_eta: p")?;
//     //     // let fst_p = self.add(ctx, NodeT::Fst([p]));
//     //     // let snd_p = self.add(ctx, NodeT::Snd([p]));
//     //     // let eta = self.add(ctx, NodeT::Pair([fst_p, snd_p]));
//     //     // self.0.set_eq_unchecked(ctx, p, eta);
//     //     // Ok(Eqn { lhs: p, rhs: eta }.finish_rule(ctx, strategy))
//     // }
// }
