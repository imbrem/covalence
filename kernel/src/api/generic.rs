use crate::{api::store::*, data::term::*};

impl<C: Copy, T: Copy> Val<C, T> {}

impl<C: Copy, T> NodeVT<C, T> {
    /// Convert nested values to nested imports
    pub fn import_children(self) -> NodeVT2<C, T> {
        self.map_subterms(|tm| NodeT::Import(tm))
    }
}

impl<C: Copy, T> NodeT2<C, T> {
    /// Flatten this node into a single level in a given context
    pub fn flatten_in(self, ctx: C, store: &mut impl WriteTerm<C, T>) -> NodeT<C, T> {
        self.map_subterms(|tm| store.add(ctx, tm))
    }

    /// Get the value corresponding to this nested node
    pub fn add(self, ctx: C, store: &mut impl WriteTerm<C, T>) -> Val<C, T> {
        self.flatten_in(ctx, store).add_val(ctx, store)
    }
}

/// A trait for a value with a bound variable index
pub trait Bvi<S> {
    /// Get the bound variable index of this value
    fn bvi(&self, store: &S) -> Bv;
}

impl<S: ReadTerm<C, T>, C: Copy, T: Copy> Bvi<S> for Val<C, T> {
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
    S: WriteTerm<C, T>,
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
    S: WriteTerm<C, T>,
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
