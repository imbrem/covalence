use crate::Pred1;
use crate::api::store::*;
use crate::data::term::*;

impl<C, T> NodeT<C, T> {
    /// Infer predicates for this term in the given context
    pub fn static_flags(&self) -> Pred1 {
        match self {
            NodeT::U(_) => Pred1::IS_UNIV,
            NodeT::Unit => Pred1::IS_TT,
            NodeT::Empty => Pred1::IS_FF,
            NodeT::Nats => Pred1::IS_INHAB,
            NodeT::N64(_) | NodeT::Null => Pred1::IS_WF,
            _ => Pred1::default(),
        }
    }
}

impl<C: Copy, T: Copy> NodeT<C, T> {
    /// Infer predicates for this term in the given context
    pub fn infer_flags(&self, ctx: C, store: &impl ReadTermStore<C, T>) -> Pred1 {
        let mut result = Pred1::default();
        match self {
            &NodeT::Fv(var) => return var.infer_flags(ctx, store),
            &NodeT::Pi([arg, res]) => {
                let arg_flags = store.tm_flags(ctx, arg);
                let res_flags = store.tm_flags(ctx, res);
                if arg_flags.contains(Pred1::IS_TY) && res_flags.contains(Pred1::IS_TY) {
                    result.insert(Pred1::IS_TY);
                    if arg_flags.contains(Pred1::IS_EMPTY) || res_flags.contains(Pred1::IS_INHAB) {
                        result.insert(Pred1::IS_INHAB);
                    }
                    if arg_flags.contains(Pred1::IS_INHAB) && res_flags.contains(Pred1::IS_EMPTY) {
                        result.insert(Pred1::IS_EMPTY);
                    }
                    if res_flags.contains(Pred1::IS_PROP) {
                        result.insert(Pred1::IS_PROP);
                    }
                }
            }
            &NodeT::Sigma([fst, snd]) => {
                let fst_flags = store.tm_flags(ctx, fst);
                let snd_flags = store.tm_flags(ctx, snd);
                if fst_flags.contains(Pred1::IS_TY) && snd_flags.contains(Pred1::IS_TY) {
                    result.insert(Pred1::IS_TY);
                    if fst_flags.contains(Pred1::IS_EMPTY) || snd_flags.contains(Pred1::IS_EMPTY) {
                        result.insert(Pred1::IS_EMPTY);
                    }
                    if fst_flags.contains(Pred1::IS_INHAB) && snd_flags.contains(Pred1::IS_INHAB) {
                        result.insert(Pred1::IS_INHAB);
                    }
                    if fst_flags.contains(Pred1::IS_PROP) && snd_flags.contains(Pred1::IS_PROP) {
                        result.insert(Pred1::IS_PROP);
                    }
                }
            }
            &NodeT::Eqn([lhs, rhs]) => {
                if store.eq_in(ctx, lhs, rhs) && store.is_wf(ctx, lhs) {
                    result.insert(Pred1::IS_TT);
                }
            }
            &NodeT::Choose([ty, pred]) => {
                if store.is_inhab(ctx, ty) && store.is_prop(ctx, pred) {
                    result.insert(Pred1::IS_WF);
                }
            }
            &NodeT::Pair([fst, snd]) => {
                if store.is_wf(ctx, fst) && store.is_wf(ctx, snd) {
                    result.insert(Pred1::IS_WF);
                }
            }
            &NodeT::Trunc([tm]) => {
                let tm_flags = store.tm_flags(ctx, tm);
                if tm_flags.contains(Pred1::IS_TY) {
                    result.insert(Pred1::IS_PROP);
                }
                if tm_flags.contains(Pred1::IS_INHAB) {
                    result.insert(Pred1::IS_TT);
                }
                if tm_flags.contains(Pred1::IS_EMPTY) {
                    result.insert(Pred1::IS_FF);
                }
            }
            this => {
                return this.static_flags();
            }
        }
        result
    }
}
