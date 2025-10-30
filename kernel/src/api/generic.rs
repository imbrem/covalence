use crate::{api::store::*, data::term::*};

impl<C, T> Val<C, T> {
    /// Get the node in `self.ctx` corresponding to this value
    pub fn node(self, store: &impl TermStore<C, T>) -> &NodeT<C, T> {
        store.node(self.ctx, self.tm)
    }
}

impl<C: Copy, T> NodeT<C, T> {
    /// Annotate this node with a context, yielding a global node
    pub fn with(self, ctx: C) -> VNodeT<C, T> {
        VNodeT { ctx, tm: self }
    }

    /// Annotate the _children_ of this node with a context, yielding a nested node
    pub fn children_with(self, ctx: C) -> NodeVT<C, T> {
        self.map_subterms(|tm| Val { ctx, tm })
    }
}

impl<C: Copy, T: Copy> Val<C, T> {
    /// Get the value node corresponding to this value
    ///
    /// # Examples
    /// ```rust
    /// # use covalence_kernel::*;
    /// # let mut ker = Kernel::new();
    /// # // TODO: pick better values here...
    /// # let ctx = ker.new_ctx();
    /// # let other = ker.new_ctx();
    /// # let values = [
    /// #   Node::U(ULvl::SET).add_val(ctx, &mut ker),
    /// #   Node::U(ULvl::PROP).add_val(ctx, &mut ker),
    /// #   Node::U(ULvl::SET).add_val(other, &mut ker),
    /// #   Node::U(ULvl::PROP).add_val(other, &mut ker),
    /// # ];
    /// # for v in values {
    /// assert_eq!(v.val_node(&ker).add(&mut ker), v);
    /// # }
    /// ```
    pub fn val_node(self, store: &impl TermStore<C, T>) -> VNodeT<C, T> {
        VNodeT {
            ctx: self.ctx,
            tm: *self.node(store),
        }
    }

    /// Get the node value corresponding to this value
    pub fn node_val(self, store: &impl TermStore<C, T>) -> NodeVT<C, T> {
        self.node(store).children_with(self.ctx)
    }
}

impl<C: Copy, T> VNodeT<C, T> {
    /// Get the value corresponding to this value node
    ///
    /// # Examples
    /// ```rust
    /// # use covalence_kernel::*;
    /// # let mut ker = Kernel::new();
    /// # // TODO: pick better values here...
    /// # let ctx = ker.new_ctx();
    /// # let other = ker.new_ctx();
    /// # let nodes = [
    /// #   Node::U(ULvl::SET).with(ctx),
    /// #   Node::U(ULvl::PROP).with(ctx),
    /// #   Node::U(ULvl::SET).with(other),
    /// #   Node::U(ULvl::PROP).with(other),
    /// # ];
    /// # for g in nodes {
    /// assert_eq!(g.add(&mut ker).val_node(&ker), g);
    /// # }
    /// ```
    pub fn add(self, store: &mut impl TermStore<C, T>) -> Val<C, T> {
        self.tm.add_val(self.ctx, store)
    }

    /// Get the node value corresponding to this value
    pub fn into_node_val(self) -> NodeVT<C, T> {
        self.tm.children_with(self.ctx)
    }
}

impl<C: Copy, T> NodeVT<C, T> {
    /// Convert nested values to nested imports
    pub fn into_nested_val(self) -> NodeVT2<C, T> {
        self.map_subterms(|tm| NodeT::Import(tm))
    }
}

impl<C: Copy, T> NodeT2<C, T> {
    /// Flatten this node into a single level in a given context
    pub fn flatten_in(self, ctx: C, store: &mut impl TermStore<C, T>) -> NodeT<C, T> {
        self.map_subterms(|tm| store.add(ctx, tm))
    }

    /// Get the value corresponding to this nested node
    pub fn add(self, ctx: C, store: &mut impl TermStore<C, T>) -> Val<C, T> {
        self.flatten_in(ctx, store).add_val(ctx, store)
    }
}

impl<C: Copy, T> VNodeT2<C, T> {
    /// Get the value corresponding to this global node
    pub fn add(self, store: &mut impl TermStore<C, T>) -> Val<C, T> {
        self.tm.add(self.ctx, store)
    }
}

/// A trait for a value with a bound variable index
pub trait Bvi<S> {
    /// Get the bound variable index of this value
    fn bvi(&self, store: &S) -> Bv;
}

impl<S: ReadFacts<C, T>, C: Copy, T: Copy> Bvi<S> for Val<C, T> {
    fn bvi(&self, store: &S) -> Bv {
        store.bvi(self.ctx, self.tm)
    }
}

impl<S, C, T, I> Bvi<S> for NodeT<C, T, I>
where
    I: Bvi<S>,
    T: Bvi<S>,
{
    fn bvi(&self, store: &S) -> Bv {
        match self {
            NodeT::Import(import) => import.bvi(store),
            this => this.bvi_with(|x| x.bvi(store)),
        }
    }
}

/// A trait for a value which can be added into a given context of a term store
///
/// `import`ing a value, unlike `add`ing it, unfolds all imports
pub trait AddNode<S, C, T> {
    /// Insert a value into the given store in the given context
    fn add(self, ctx: C, store: &mut S) -> T;

    /// Get the value inserted into the given store
    fn add_val(self, ctx: C, store: &mut S) -> Val<C, T>
    where
        Self: Sized,
        C: Copy,
    {
        Val {
            ctx,
            tm: self.add(ctx, store),
        }
    }
}

impl<S, C, T> AddNode<S, C, T> for NodeT<C, T>
where
    S: TermStore<C, T>,
{
    fn add(self, ctx: C, store: &mut S) -> T {
        store.add(ctx, self)
    }
}

/// A trait for a value which can be inserted into a given context of a term store
///
/// `import`ing a value, unlike `add`ing it, unfolds imports _within_ the object
pub trait ImportNode<S, C, T> {
    /// Insert a value into the given store in the given context
    fn import(self, ctx: C, store: &mut S) -> T;

    /// Get the value inserted into the given store
    fn import_val(self, ctx: C, store: &mut S) -> Val<C, T>
    where
        Self: Sized,
        C: Copy,
    {
        Val {
            ctx,
            tm: self.import(ctx, store),
        }
    }
}

impl<S, C, T, V, I> ImportNode<S, C, T> for NodeT<C, V, I>
where
    S: TermStore<C, T>,
    C: Copy,
    T: Copy,
    V: ImportNode<S, C, T>,
    I: ImportNode<S, C, T>,
{
    fn import(self, ctx: C, store: &mut S) -> T {
        match self {
            NodeT::Import(import) => import.import(ctx, store),
            this => {
                let node = this
                    .map_subterms(|x| x.import(ctx, store))
                    .map_import(|_| unreachable!());
                store.add(ctx, node)
            }
        }
    }
}
