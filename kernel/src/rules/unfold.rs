use crate::{
    Bvi,
    api::store::*,
    data::term::{Bv, Close, Fv, NodeT, NodeVT, NodeVT2, Shift, Val},
};

impl<C: Copy, T: Copy> Val<C, T> {
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
        match self.step(store)? {
            Ok(NodeVT2::Import(val)) => val.step(store),
            Ok(this) => {
                debug_assert!(!this.is_unfoldable());
                Some(Ok(this))
            }
            Err(err) => Some(Err(err)),
        }
    }
}

impl<C: Copy, T: Copy> NodeVT<C, T> {
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
    pub fn import_step(
        self,
        store: &(impl TermStore<C, T> + ReadFacts<C, T>),
    ) -> Option<Result<NodeVT2<C, T>, ()>> {
        match self.step(store)? {
            Ok(NodeVT2::Import(val)) => val.import_step(store),
            Ok(this) => {
                debug_assert!(!this.is_unfoldable());
                Some(Ok(this))
            }
            Err(err) => Some(Err(err)),
        }
    }
}
