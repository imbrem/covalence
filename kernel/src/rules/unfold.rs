// use crate::{
//     api::store::*,
//     data::term::{Bv, Close, Fv, NodeT, NodeT2, Shift, Val},
// };

// impl<C, T> Close<C, T> {}

// impl<C: Copy, T: Copy> Close<C, T> {
//     /// Get this close's term as a value
//     pub fn tm_val(self, ctx: C) -> Val<C, T> {
//         Val { ctx, tm: self.tm }
//     }

//     /// Get whether this closure is the identity in the given context
//     pub fn is_id(&self, ctx: C, store: &(impl TermStore<C, T> + ReadFacts<C, T>)) -> bool {
//         store.bvi(ctx, self.tm) <= self.under
//     }

//     /// Unfold this close by a single step in the given context, if possible
//     pub fn unfold(&self, ctx: C, store: &impl TermStore<C, T>) -> Result<NodeT2<C, T>, ()> {
//         store.node(ctx, self.tm).nested_close(self.under, self.var)
//     }

//     /// Unfold this close by a single step in the given context, if possible
//     ///
//     /// Return an import if this closure is the identity
//     pub fn step(
//         &self,
//         ctx: C,
//         store: &(impl TermStore<C, T> + ReadFacts<C, T>),
//     ) -> Result<NodeT2<C, T>, ()> {
//         if self.is_id(ctx, store) {
//             return Ok(NodeT2::Import(self.tm_val(ctx)));
//         }
//         self.unfold(ctx, store)
//     }
// }

// // impl<C: Copy, T: Copy> Close<C, Val<C, T>> {
// //     /// Get whether this closure is the identity in the given store
// //     pub fn is_id_val(&self, store: &(impl TermStore<C, T> + ReadFacts<C, T>)) -> bool {
// //         self.tm.bvi(store) <= self.under
// //     }

// //     /// Unfold this close by a single step in the given store, if possible
// //     ///
// //     /// Return an import if this closure is the identity
// //     pub fn step_val(
// //         &self,
// //         store: &(impl TermStore<C, T> + ReadFacts<C, T>),
// //     ) -> Result<NodeT2<C, Val<C, T>>, ()> {
// //         if self.is_id_val(store) {
// //             return Ok(NodeT2::Import(self.tm_val(ctx)));
// //         }
// //         self.unfold(ctx, store)
// //     }
// // }

// impl<C: Copy, T: Copy> NodeT<C, T> {
//     /// Get the nested closure of this node
//     pub fn nested_close(self, under: Bv, var: Fv<C>) -> Result<NodeT2<C, T>, ()> {
//         if self.is_unfoldable() {
//             return Err(());
//         }
//         Ok(self.with_binders().map_subterms(|(bv, tm)| {
//             Close {
//                 under: under + bv,
//                 var,
//                 tm,
//             }
//             .into()
//         }))
//     }

//     /// Get the nested single substitution of this node
//     pub fn nested_subst1(
//         self,
//         ctx: C,
//         under: Bv,
//         bound: T,
//         store: &impl ReadFacts<C, T>,
//     ) -> Result<NodeT2<C, T>, ()> {
//         if self.is_unfoldable() {
//             return Err(());
//         }
//         self.with_binders().try_map_subterms(|(bv, tm)| {
//             if store.bvi(ctx, bound) != Bv(0) {
//                 return Err(());
//             }
//             Ok(NodeT::Subst1(under + bv, [bound, tm]))
//         })
//     }

//     /// Get the weakening of this node
//     pub fn nested_bwk(self, shift: Shift) -> Result<NodeT2<C, T>, ()> {
//         if self.is_unfoldable() {
//             return Err(());
//         }
//         self.with_binders()
//             .try_map_subterms(|(bv, tm)| Ok(NodeT::BWk(shift.lift_under(bv), [tm])))
//     }

//     /// Unfold this node by a single step in the given context, if possible
//     pub fn step(
//         self,
//         ctx: C,
//         store: &(impl TermStore<C, T> + ReadFacts<C, T>),
//     ) -> Option<Result<NodeT2<C, T>, ()>> {
//         match self {
//             NodeT::Import(val) => Some(Ok(val.node_val(store))),
//             NodeT::Close(cl) => Some(cl.step(ctx, store)),
//             NodeT::Subst1(under, [bound, tm]) => Some(if store.bvi(ctx, tm) <= under {
//                 Ok(NodeT2::Import(Val { ctx, tm }))
//             } else {
//                 store.node(ctx, tm).nested_subst1(ctx, under, bound, store)
//             }),
//             NodeT::BWk(shift, [tm]) => {
//                 Some(if shift.is_id() || store.bvi(ctx, tm) <= shift.under() {
//                     Ok(NodeT2::Import(Val { ctx, tm }))
//                 } else {
//                     store.node(ctx, tm).nested_bwk(shift)
//                 })
//             }
//             _ => None,
//         }
//     }
// }
