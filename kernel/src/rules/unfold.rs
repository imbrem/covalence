use std::cmp::Ordering;

use crate::{
    Bvi,
    api::store::*,
    data::term::{Bv, Close, Fv, NodeT, NodeVT, NodeVT2, Shift, Val},
};

impl<C: Copy + PartialEq, T: Copy> Val<C, T> {
    /// Get the substitution of this value after a single step, if possible
    pub fn subst1_step(
        self,
        under: Bv,
        bound: Val<C, T>,
        store: &(impl TermStore<C, T> + ReadFacts<C, T>),
    ) -> Result<NodeVT2<C, T>, ()> {
        if self.bvi(store) <= under {
            return Ok(NodeVT2::Import(self));
        }
        self.node_val(store).subst1_step(under, bound, store)
    }

    /// Get the weakening of this value after a single step, if possible
    pub fn bwk_step(
        self,
        shift: Shift,
        store: &(impl TermStore<C, T> + ReadFacts<C, T>),
    ) -> Result<NodeVT2<C, T>, ()> {
        if shift.is_id() || self.bvi(store) <= shift.under() {
            return Ok(NodeVT2::Import(self));
        }
        self.node_val(store).bwk_step(shift, store)
    }

    /// Get the close of this value after a single step, if possible
    pub fn close_step(
        self,
        under: Bv,
        var: Fv<C>,
        store: &(impl TermStore<C, T> + ReadFacts<C, T>),
    ) -> Result<NodeVT2<C, T>, ()> {
        if self.bvi(store) <= under {
            return Ok(NodeVT2::Import(self));
        }
        self.node_val(store).close_step(under, var, store)
    }

    /// Unfold this value by a single step, if possible
    pub fn step(
        self,
        store: &(impl TermStore<C, T> + ReadFacts<C, T>),
    ) -> Option<Result<NodeVT2<C, T>, ()>> {
        self.node_val(store).step(store)
    }

    /// Unfold this node, unfolding imports as far as possible
    pub fn import_step(
        self,
        store: &(impl TermStore<C, T> + ReadFacts<C, T>),
    ) -> Option<Result<NodeVT2<C, T>, ()>> {
        self.node_val(store).import_step(store)
    }
}

impl Shift {
    /// Construct a value under the given shift
    ///
    /// If the shift is the identity, returns an import
    pub fn val<C, T>(self, val: Val<C, T>) -> NodeVT<C, T> {
        if self.is_id() {
            NodeVT::Import(val)
        } else {
            NodeVT::BWk(self, [val])
        }
    }
}

impl Bv {
    /// Substitute a bound variable
    ///
    /// # Examples
    /// ```rust
    /// # use covalence_kernel::*;
    /// # use covalence_kernel::data::term::*;
    /// # let mut ker = Kernel::new();
    /// # let ctx = ker.new_ctx();
    /// # let val = ValId { ctx, tm : ker.add(ctx, Node::Nats) };
    /// assert_eq!(Bv(0).subst1(Bv(0), val), NodeVT2::Import(val));
    /// assert_eq!(Bv(3).subst1(Bv(0), val), NodeVT2::bv(2));
    /// assert_eq!(Bv(3).subst1(Bv(5), val), NodeVT2::bv(3));
    /// // NOTE: _no_ shifting necessary!
    /// assert_eq!(Bv(3).subst1(Bv(3), val), NodeVT2::Import(val));
    /// ```
    pub fn subst1<C, T>(self, under: Bv, bound: Val<C, T>) -> NodeVT2<C, T> {
        match self.cmp(&under) {
            Ordering::Less => NodeVT2::Bv(self),
            Ordering::Equal => NodeVT2::Import(bound),
            Ordering::Greater => NodeVT2::Bv(self.pred()),
        }
    }
}

impl<C: PartialEq> Fv<C> {
    /// Close a free variable
    pub fn close<T>(self, under: Bv, var: Fv<C>) -> NodeVT2<C, T> {
        if self.ctx == var.ctx && self.ix <= var.ix {
            NodeVT2::Bv(under + Bv::new(self.ix))
        } else {
            NodeVT2::Fv(self)
        }
    }
}

impl<C: Copy + PartialEq, T: Copy> NodeVT<C, T> {
    /// Get the substitution of this node after a single step, if possible
    pub fn subst1_step(
        self,
        under: Bv,
        bound: Val<C, T>,
        store: &(impl TermStore<C, T> + ReadFacts<C, T>),
    ) -> Result<NodeVT2<C, T>, ()> {
        if self.is_unfoldable() {
            return Err(());
        }
        match self {
            NodeVT::Bv(i) => Ok(i.subst1(under, bound)),
            NodeVT::Import(val) => val.subst1_step(under, bound, store),
            _ => self.with_binders().try_map_subterms(|(bv, tm)| {
                // To support this case, we need to insert a `BWk`, which we don't have space for
                //
                // Don't reduce under binders, friend!
                if bv != Bv(0) && bound.bvi(store) != Bv(0) {
                    return Err(());
                }
                Ok(NodeT::Subst1(under + bv, [bound, tm]))
            }),
        }
    }

    /// Get the weakening of this node after a single step, if possible
    pub fn bwk_step(
        self,
        shift: Shift,
        store: &(impl TermStore<C, T> + ReadFacts<C, T>),
    ) -> Result<NodeVT2<C, T>, ()> {
        if self.is_unfoldable() {
            return Err(());
        }
        match self {
            NodeVT::Bv(i) => Ok(NodeVT2::Bv(shift.apply(i))),
            NodeVT::Import(val) => val.bwk_step(shift, store),
            _ => Ok(self
                .with_binders()
                .map_subterms(|(bv, tm)| NodeT::BWk(shift.lift_under(bv), [tm]))),
        }
    }

    /// Get the close of this node after a single step, if possible
    pub fn close_step(
        self,
        under: Bv,
        var: Fv<C>,
        store: &(impl TermStore<C, T> + ReadFacts<C, T>),
    ) -> Result<NodeVT2<C, T>, ()> {
        if self.is_unfoldable() {
            return Err(());
        }
        match self {
            NodeVT::Fv(x) => Ok(x.close(under, var)),
            NodeVT::Bv(i) => Ok(NodeVT2::Bv(i.bvi_add_under(Bv::new(var.ix), under))),
            NodeVT::Import(val) => val.close_step(under, var, store),
            _ => Ok(self.with_binders().map_subterms(|(bv, tm)| {
                NodeT::Close(Close {
                    under: under + bv,
                    var,
                    tm,
                })
            })),
        }
    }

    /// Unfold this node by a single step, if possible
    ///
    /// # Examples
    /// ```rust
    /// # use covalence_kernel::*;
    /// # use covalence_kernel::data::term::*;
    /// # let mut ker = Kernel::new();
    /// # let ctx = ker.new_ctx();
    /// let nats = Node::Nats.add_val(ctx, &mut ker);
    /// assert_eq!(nats.step(&ker), None);
    /// let i = Node::bv(0).add_val(ctx, &mut ker);
    /// assert_eq!(i.step(&ker), None);
    /// let s = Node::Subst1(Bv(0), [nats.tm, i.tm]).add_val(ctx, &mut ker);
    /// assert_eq!(s.step(&ker), Some(Ok(NodeVT2::Import(nats))));
    /// ```
    pub fn step(
        self,
        store: &(impl TermStore<C, T> + ReadFacts<C, T>),
    ) -> Option<Result<NodeVT2<C, T>, ()>> {
        match self {
            NodeVT::Import(this) => match this.node_val(store) {
                NodeVT::Import(that) => Some(Ok(NodeVT2::Import(that))),
                this => Some(Ok(this.into_nested_val())),
            },
            NodeVT::Subst1(under, [bound, tm]) => Some(tm.subst1_step(under, bound, store)),
            NodeVT::BWk(shift, [tm]) => Some(tm.bwk_step(shift, store)),
            NodeVT::Close(Close { under, var, tm }) => Some(tm.close_step(under, var, store)),
            _ => {
                debug_assert!(!self.is_unfoldable());
                None
            }
        }
    }

    /// Unfold this node, unfolding imports as far as possible
    ///
    /// # Examples
    /// ```rust
    /// # use covalence_kernel::*;
    /// # use covalence_kernel::data::term::*;
    /// # let mut ker = Kernel::new();
    /// # let ctx = ker.new_ctx();
    /// let nats = Node::Nats.add_val(ctx, &mut ker);
    /// assert_eq!(nats.import_step(&ker), None);
    /// let i = Node::bv(0).add_val(ctx, &mut ker);
    /// assert_eq!(i.import_step(&ker), None);
    /// let s = Node::Subst1(Bv(0), [nats.tm, i.tm]).add_val(ctx, &mut ker);
    /// assert_eq!(s.import_step(&ker), Some(Ok(NodeVT2::Nats)));
    /// ```
    pub fn import_step(
        self,
        store: &(impl TermStore<C, T> + ReadFacts<C, T>),
    ) -> Option<Result<NodeVT2<C, T>, ()>> {
        match self.step(store)? {
            Ok(NodeVT2::Import(val)) => {
                let result = NodeVT::Import(val).import_step(store);
                debug_assert!(result.is_some());
                result
            }
            Ok(this) => {
                debug_assert!(!this.is_unfoldable());
                Some(Ok(this))
            }
            Err(err) => Some(Err(err)),
        }
    }
}
