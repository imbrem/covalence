// use std::cmp::Ordering;

// use crate::{
//     data::term::{Bv, Close, Fv, NodeT, NodeT2, NodeVT, NodeVT2, Shift, Val},
//     store::*,
// };

// impl<C: Copy, T> NodeVT<C, T> {
//     /// Convert nested values to nested imports
//     pub fn import_children(self) -> NodeVT2<C, T> {
//         self.map_subterms(|tm| NodeT::Import(tm))
//     }
// }

// impl<C: Copy, T> NodeT2<C, T> {
//     /// Flatten this node into a single level in a given context
//     pub fn flatten_in(
//         self,
//         ctx: C,
//         store: &mut impl WriteTermIndex<CtxId = C, TermId = T>,
//     ) -> NodeT<C, T> {
//         self.map_subterms(|tm| store.add_raw(ctx, tm))
//     }

//     /// Get the value corresponding to this nested node
//     pub fn add(self, ctx: C, store: &mut impl WriteTermIndex<CtxId = C, TermId = T>) -> Val<C, T> {
//         self.flatten_in(ctx, store).add_val(ctx, store)
//     }
// }

// /// A trait for a value with a bound variable index
// pub trait Bvi<S> {
//     /// Get the bound variable index of this value
//     fn bvi(&self, store: &S) -> Bv;
// }

// impl<S: ReadTermIndex> Bvi<S> for KValId<S> {
//     fn bvi(&self, store: &S) -> Bv {
//         store.bvi(self.ctx, self.tm)
//     }
// }

// impl<S, C, T, I> Bvi<S> for NodeT<C, T, I>
// where
//     I: Bvi<S>,
//     T: Bvi<S>,
// {
//     fn bvi(&self, store: &S) -> Bv {
//         match self {
//             NodeT::Import(import) => import.bvi(store),
//             this => this.bvi_with(|x| x.bvi(store)),
//         }
//     }
// }

// /// A trait for a value which can be added into a given context of a term store
// ///
// /// `import`ing a value, unlike `add`ing it, unfolds all imports
// pub trait AddNode<S, C, T> {
//     /// Insert a value into the given store in the given context
//     fn add(self, ctx: C, store: &mut S) -> T;

//     /// Get the value inserted into the given store
//     fn add_val(self, ctx: C, store: &mut S) -> Val<C, T>
//     where
//         Self: Sized,
//         C: Copy,
//     {
//         Val {
//             ctx,
//             tm: self.add(ctx, store),
//         }
//     }
// }

// impl<S, C, T> AddNode<S, C, T> for NodeT<C, T>
// where
//     S: WriteTermIndex<CtxId = C, TermId = T>,
// {
//     fn add(self, ctx: C, store: &mut S) -> T {
//         store.add_raw(ctx, self)
//     }
// }

// impl<C: Copy + PartialEq, T: Copy> Val<C, T> {
//     /// Get the substitution of this value after a single step, if possible
//     pub fn subst1_step(
//         self,
//         under: Bv,
//         bound: Val<C, T>,
//         store: &impl ReadTermIndex<CtxId = C, TermId = T>,
//     ) -> Option<NodeVT2<C, T>> {
//         if self.bvi(store) <= under {
//             return Some(NodeVT2::Import(self));
//         }
//         self.node_val(store).subst1_step(under, bound, store)
//     }

//     /// Get the weakening of this value after a single step, if possible
//     pub fn bwk_step(
//         self,
//         shift: Shift,
//         store: &impl ReadTermIndex<CtxId = C, TermId = T>,
//     ) -> Option<NodeVT2<C, T>> {
//         if shift.is_id() || self.bvi(store) <= shift.under() {
//             return Some(NodeVT2::Import(self));
//         }
//         self.node_val(store).bwk_step(shift, store)
//     }

//     /// Get the close of this value after a single step, if possible
//     pub fn close_step(
//         self,
//         under: Bv,
//         var: Fv<C>,
//         store: &impl ReadTermIndex<CtxId = C, TermId = T>,
//     ) -> Option<NodeVT2<C, T>> {
//         if self.bvi(store) <= under {
//             return Some(NodeVT2::Import(self));
//         }
//         self.node_val(store).close_step(under, var, store)
//     }

//     /// Unfold this value by a single step, if possible
//     pub fn step(self, store: &impl ReadTermIndex<CtxId = C, TermId = T>) -> Option<NodeVT2<C, T>> {
//         self.node_val(store).step(store)
//     }

//     /// Unfold this node, unfolding imports as far as possible
//     pub fn import_step(
//         self,
//         store: &impl ReadTermIndex<CtxId = C, TermId = T>,
//     ) -> Option<NodeVT2<C, T>> {
//         self.node_val(store).import_step(store)
//     }
// }

// impl Shift {
//     /// Construct a value under the given shift
//     ///
//     /// If the shift is the identity, returns an import
//     pub fn val<C, T>(self, val: Val<C, T>) -> NodeVT<C, T> {
//         if self.is_id() {
//             NodeVT::Import(val)
//         } else {
//             NodeVT::BWk(self, [val])
//         }
//     }
// }

// impl Bv {
//     /// Substitute a bound variable
//     pub fn subst1<C, T>(self, under: Bv, bound: Val<C, T>) -> NodeVT2<C, T> {
//         match self.cmp(&under) {
//             Ordering::Less => NodeVT2::Bv(self),
//             Ordering::Equal => NodeVT2::Import(bound),
//             Ordering::Greater => NodeVT2::Bv(self.pred()),
//         }
//     }
// }

// impl<C: PartialEq> Fv<C> {
//     /// Close a free variable
//     pub fn close<T>(self, under: Bv, var: Fv<C>) -> NodeVT2<C, T> {
//         if self.ctx == var.ctx && self.ix <= var.ix {
//             NodeVT2::Bv(under + Bv::new(self.ix))
//         } else {
//             NodeVT2::Fv(self)
//         }
//     }
// }

// impl<C: Copy + PartialEq, T: Copy> NodeVT<C, T> {
//     /// Get the substitution of this node after a single step, if possible
//     pub fn subst1_step(
//         self,
//         under: Bv,
//         bound: Val<C, T>,
//         store: &impl ReadTermIndex<CtxId = C, TermId = T>,
//     ) -> Option<NodeVT2<C, T>> {
//         match self {
//             NodeVT::Bv(i) => Some(i.subst1(under, bound)),
//             NodeVT::Import(val) => val.subst1_step(under, bound, store),
//             _ => {
//                 if self.is_unfoldable() {
//                     return None;
//                 }
//                 self.with_binders()
//                     .try_map_subterms(|(bv, tm)| {
//                         // To support this case, we need to insert a `BWk`, which we don't have space for
//                         //
//                         // Don't reduce under binders, friend!
//                         if bv != Bv(0) && bound.bvi(store) != Bv(0) {
//                             return Err(());
//                         }
//                         Ok(NodeT::Subst1(under + bv, [bound, tm]))
//                     })
//                     .ok()
//             }
//         }
//     }

//     /// Get the weakening of this node after a single step, if possible
//     pub fn bwk_step(
//         self,
//         shift: Shift,
//         store: &impl ReadTermIndex<CtxId = C, TermId = T>,
//     ) -> Option<NodeVT2<C, T>> {
//         match self {
//             NodeVT::Bv(i) => Some(NodeVT2::Bv(shift.apply(i))),
//             NodeVT::Import(val) => val.bwk_step(shift, store),
//             _ => {
//                 if self.is_unfoldable() {
//                     return None;
//                 }
//                 Some(
//                     self.with_binders()
//                         .map_subterms(|(bv, tm)| NodeT::BWk(shift.lift_under(bv), [tm])),
//                 )
//             }
//         }
//     }

//     /// Get the close of this node after a single step, if possible
//     pub fn close_step(
//         self,
//         under: Bv,
//         var: Fv<C>,
//         store: &impl ReadTermIndex<CtxId = C, TermId = T>,
//     ) -> Option<NodeVT2<C, T>> {
//         match self {
//             NodeVT::Fv(x) => Some(x.close(under, var)),
//             NodeVT::Bv(i) => Some(NodeVT2::Bv(i.bvi_add_under(Bv::new(var.ix), under))),
//             NodeVT::Import(val) => val.close_step(under, var, store),
//             _ => {
//                 if self.is_unfoldable() {
//                     return None;
//                 }
//                 Some(self.with_binders().map_subterms(|(bv, tm)| {
//                     NodeT::Close(Close {
//                         under: under + bv,
//                         var,
//                         tm,
//                     })
//                 }))
//             }
//         }
//     }

//     /// Unfold this node by a single step, if possible
//     pub fn step(self, store: &impl ReadTermIndex<CtxId = C, TermId = T>) -> Option<NodeVT2<C, T>> {
//         match self {
//             NodeVT::Import(this) => match this.node_val(store) {
//                 NodeVT::Import(that) => Some(NodeVT2::Import(that)),
//                 this => Some(this.import_children()),
//             },
//             NodeVT::Subst1(under, [bound, tm]) => tm.subst1_step(under, bound, store),
//             NodeVT::BWk(shift, [tm]) => tm.bwk_step(shift, store),
//             NodeVT::Close(Close { under, var, tm }) => tm.close_step(under, var, store),
//             _ => {
//                 debug_assert!(!self.is_unfoldable());
//                 None
//             }
//         }
//     }

//     /// Unfold this node, unfolding imports as far as possible
//     pub fn import_step(
//         self,
//         store: &impl ReadTermIndex<CtxId = C, TermId = T>,
//     ) -> Option<NodeVT2<C, T>> {
//         match self.step(store)? {
//             NodeVT2::Import(val) => {
//                 let result = NodeVT::Import(val).import_step(store);
//                 debug_assert!(result.is_some());
//                 result
//             }
//             this => {
//                 debug_assert!(!this.is_unfoldable());
//                 Some(this)
//             }
//         }
//     }
// }

// impl<C: Copy + PartialEq, T: Copy + PartialEq> Val<C, T> {
//     pub fn syn_eq(
//         self,
//         other: Val<C, T>,
//         store: &impl ReadTermIndex<CtxId = C, TermId = T>,
//     ) -> bool {
//         if self == other {
//             return true;
//         }
//         self.node_val(store).syn_eq(other.node_val(store), store)
//     }

//     pub fn def_eq(
//         self,
//         other: Val<C, T>,
//         store: &impl ReadTermIndex<CtxId = C, TermId = T>,
//     ) -> bool {
//         if self == other {
//             return true;
//         }
//         self.node_val(store).def_eq(other.node_val(store), store)
//     }
// }

// impl<C: Copy + PartialEq, T: Copy + PartialEq> NodeVT<C, T> {
//     pub fn syn_eq(
//         self,
//         other: NodeVT<C, T>,
//         store: &impl ReadTermIndex<CtxId = C, TermId = T>,
//     ) -> bool {
//         match (self, other) {
//             (NodeVT::Import(val), other) => val.node_val(store).syn_eq(other, store),
//             (this, NodeVT::Import(val)) => this.syn_eq(val.node_val(store), store),
//             (NodeVT::Close(lc), NodeVT::Close(rc)) => {
//                 lc.under == rc.under && lc.var == rc.var && lc.tm.syn_eq(rc.tm, store)
//             }
//             _ => {
//                 self.disc() == other.disc()
//                     && self
//                         .children()
//                         .iter()
//                         .zip(other.children().iter())
//                         .all(|(&l, &r)| l.syn_eq(r, store))
//             }
//         }
//     }

//     pub fn def_eq(
//         self,
//         other: NodeVT<C, T>,
//         store: &impl ReadTermIndex<CtxId = C, TermId = T>,
//     ) -> bool {
//         if self == other {
//             return true;
//         }
//         let this = self.import_step(store).unwrap_or(self.import_children());
//         let other = self.import_step(store).unwrap_or(self.import_children());
//         match (this, other) {
//             (NodeVT2::Close(lc), NodeVT2::Close(rc)) => {
//                 lc.under == rc.under && lc.var == rc.var && lc.tm.def_eq(rc.tm, store)
//             }
//             _ => {
//                 this.disc() == other.disc()
//                     && this
//                         .children()
//                         .iter()
//                         .zip(other.children().iter())
//                         .all(|(&l, &r)| l.def_eq(r, store))
//             }
//         }
//     }
// }
