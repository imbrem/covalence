use crate::{
    data::term::{Close1, Fv, Kind, Node, Subst1, Tm1, Tm2, Tm3, TmIn},
    id::KernelId,
    store::{ReadLocalTerm, WriteLocalTerm, index::term_sealed::SessionSealed},
};
use std::{
    fmt::{self, Debug},
    hash::Hash,
};

/// A term database with a given index kind
///
/// This trait specifies types for
/// - A _context identifier_: a unique ID mapping to a context in the term database
/// - A _local index_: an index into a context mapping to a term
///
/// In general, _identifiers_ `Id` like `CtxId` and `TmId` are _global_ identifiers w.r.t. the term
/// database, while _indices_ `Ix` are _local_ identifiers which need to be _resolved_ w.r.t. a
/// context to get their value.
///
/// In particular, a `TmId` is just a pair of a `CtxId` and an `Ix`, representing the term at local
/// index `ix` in context `ctx`.
pub trait TermIndex {
    /// The context identifier type
    type CtxId: Copy + Eq + Hash + Ord;
    /// A local index for a term
    type Ix: Copy + Eq + Hash + Ord;
}

/// A context identifier in a datastore with term index `D`
///
/// This is just a newtype wrapper around `<D as TermIndex>::CtxId` indicating that we mean to use
/// this as a valid context identifier.
pub struct CtxId<D: TermIndex + ?Sized>(pub <D as TermIndex>::CtxId);

impl<D: TermIndex + ?Sized> Copy for CtxId<D> {}

impl<D: TermIndex + ?Sized> Clone for CtxId<D> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<D: TermIndex + ?Sized> PartialEq for CtxId<D> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<D: TermIndex + ?Sized> Eq for CtxId<D> {}

impl<D: TermIndex + ?Sized> PartialOrd for CtxId<D> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<D: TermIndex + ?Sized> Ord for CtxId<D> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.cmp(&other.0)
    }
}

impl<D: TermIndex + ?Sized> Hash for CtxId<D> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl<D: TermIndex + ?Sized> Debug for CtxId<D>
where
    <D as TermIndex>::CtxId: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("CtxId").field(&self.0).finish()
    }
}

/// A local index in a datastore with term index `D`
///
/// This is just a newtype wrapper around `<D as TermIndex>::Ix` indicating that we mean to use
/// this as a valid local index.
pub struct Ix<D: TermIndex + ?Sized>(pub <D as TermIndex>::Ix);

impl<D: TermIndex + ?Sized> Copy for Ix<D> {}

impl<D: TermIndex + ?Sized> Clone for Ix<D> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<D: TermIndex + ?Sized> PartialEq for Ix<D> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<D: TermIndex + ?Sized> Eq for Ix<D> {}

impl<D: TermIndex + ?Sized> PartialOrd for Ix<D> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<D: TermIndex + ?Sized> Ord for Ix<D> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.cmp(&other.0)
    }
}

impl<D: TermIndex + ?Sized> Hash for Ix<D> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl<D: TermIndex + ?Sized> Debug for Ix<D>
where
    <D as TermIndex>::Ix: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Ix").field(&self.0).finish()
    }
}

pub type TmId<D> = TmIn<CtxId<D>, Ix<D>>;

pub type NodeIx<D> = Node<CtxId<D>, Ix<D>>;

pub type NodeTm<D> = Node<CtxId<D>, TmId<D>, TmId<D>>;

pub type FvId<D> = Fv<CtxId<D>>;

mod term_sealed {
    use crate::id::KernelId;

    pub trait SessionSealed<D> {}

    pub trait CtxSealed<D, S = KernelId> {}

    pub trait TelescopeSealed<C, D, S = KernelId> {}

    pub trait TermSealed<C, D, S = KernelId> {}
}

use term_sealed::{CtxSealed, TelescopeSealed, TermSealed};

/// A region for a given datastore
pub trait Session<D>: SessionSealed<D> {
    /// Whether this is always the global session
    const IS_GLOBAL: bool;

    /// Whether this is the global session
    fn is_global(&self) -> bool {
        Self::IS_GLOBAL
    }
}

impl<D> SessionSealed<D> for () {}

impl<D> Session<D> for () {
    const IS_GLOBAL: bool = true;
}

impl<D> SessionSealed<D> for KernelId {}

impl<D> Session<D> for KernelId {
    const IS_GLOBAL: bool = false;
}

/// A context in the datastore, potentially equipped with a telescope
pub trait CtxTelescope<D, S = KernelId>: CtxSealed<D, S> {
    /// This context's base component
    type Base: Ctx<D, S>;
}

/// A context in the datastore
pub trait Ctx<D, S = KernelId>: CtxTelescope<D, S> {}

impl<D> CtxSealed<D> for () {}

impl<D> CtxTelescope<D> for () {
    type Base = ();
}

impl<D> Ctx<D> for () {}

impl<D: TermIndex> CtxSealed<D> for CtxId<D> {}

impl<D: TermIndex> CtxTelescope<D> for CtxId<D> {
    type Base = CtxId<D>;
}

impl<D: TermIndex> Ctx<D> for CtxId<D> {}

/// A telescope in the datastore
pub trait Telescope<C, D, S = KernelId>: TelescopeSealed<C, D, S> {}

impl<C, D, S> TelescopeSealed<C, D, S> for () where C: Ctx<D, S> {}

impl<C, D, S> Telescope<C, D, S> for () where C: Ctx<D, S> {}

/// A local term in the datastore
///
/// A _local_ term can be interpreted as a term given a context ID
pub trait LocalTerm<C, D, S = KernelId>: TermSealed<C, D, S> {
    /// Whether this term type can always be relocated
    const RELOCATABLE: bool;

    /// Whether this term can be relocated
    fn relocatable(&self) -> bool {
        Self::RELOCATABLE
    }
}

impl<C, D: TermIndex> TermSealed<C, D> for Ix<D> where C: Segment<D> {}

impl<C, D: TermIndex> LocalTerm<C, D> for Ix<D>
where
    C: Segment<D>,
{
    const RELOCATABLE: bool = false;
}

impl<D, C, T, S> TermSealed<C, D, S> for &T
where
    C: Ctx<D, S>,
    T: TermSealed<C, D, S>,
{
}

impl<D, C, T, S> LocalTerm<C, D, S> for &T
where
    C: Ctx<D, S>,
    T: LocalTerm<C, D, S>,
{
    const RELOCATABLE: bool = T::RELOCATABLE;

    fn relocatable(&self) -> bool {
        T::relocatable(*self)
    }
}

impl<D, C, T, CO, S> TermSealed<CO, D, S> for TmIn<C, T>
where
    C: Ctx<D, S>,
    T: LocalTerm<C, D, S>,
    CO: Ctx<D, S>,
{
}

impl<D, C, T, CO, S> LocalTerm<CO, D, S> for TmIn<C, T>
where
    C: Ctx<D, S>,
    T: LocalTerm<C, D, S>,
    CO: Ctx<D, S>,
{
    const RELOCATABLE: bool = true;
}

impl<D, C, CN, T, I, X, S> TermSealed<C, D, S> for Node<CN, T, I, X>
where
    C: Ctx<D, S>,
    CN: Ctx<D, S>,
    T: TermSealed<C, D, S>,
    I: TermSealed<C, D, S>,
    X: TermSealed<C, D, S>,
{
}

impl<D, C, CN, T, I, X, S> LocalTerm<C, D, S> for Node<CN, T, I, X>
where
    C: Ctx<D, S>,
    CN: Ctx<D, S>,
    T: LocalTerm<C, D, S>,
    I: LocalTerm<C, D, S>,
    X: LocalTerm<C, D, S>,
{
    const RELOCATABLE: bool = T::RELOCATABLE && I::RELOCATABLE && X::RELOCATABLE;

    fn relocatable(&self) -> bool {
        match self {
            Node::Quote(tm) => tm.relocatable(),
            Node::Close1(close) => close.relocatable(),
            this => this.children().iter().all(|tm| tm.relocatable()),
        }
    }
}

impl<D, C, S> TermSealed<C, D, S> for Fv<C> where C: Ctx<D, S> {}

impl<D, C, S> LocalTerm<C, D, S> for Fv<C>
where
    C: Ctx<D, S>,
{
    const RELOCATABLE: bool = true;
}

impl<D, C, K, T, S> TermSealed<C, D, S> for Tm1<K, T>
where
    C: Ctx<D, S>,
    K: Kind<1>,
    T: TermSealed<C, D, S>,
{
}

impl<D, C, K, T, S> LocalTerm<C, D, S> for Tm1<K, T>
where
    C: Ctx<D, S>,
    K: Kind<1>,
    T: LocalTerm<C, D, S>,
{
    const RELOCATABLE: bool = T::RELOCATABLE;

    fn relocatable(&self) -> bool {
        self.1.relocatable()
    }
}

impl<D, C, K, L, R, S> TermSealed<C, D, S> for Tm2<K, L, R>
where
    C: Ctx<D, S>,
    K: Kind<2>,
    L: TermSealed<C, D, S>,
    R: TermSealed<C, D, S>,
{
}

impl<D, C, K, L, R, S> LocalTerm<C, D, S> for Tm2<K, L, R>
where
    C: Ctx<D, S>,
    K: Kind<2>,
    L: LocalTerm<C, D, S>,
    R: LocalTerm<C, D, S>,
{
    const RELOCATABLE: bool = L::RELOCATABLE && R::RELOCATABLE;

    fn relocatable(&self) -> bool {
        self.1.relocatable() && self.2.relocatable()
    }
}

impl<D, C, K, L, M, R, S> TermSealed<C, D, S> for Tm3<K, L, M, R>
where
    C: Ctx<D, S>,
    K: Kind<3>,
    L: TermSealed<C, D, S>,
    M: TermSealed<C, D, S>,
    R: TermSealed<C, D, S>,
{
}

impl<D, C, K, L, M, R, S> LocalTerm<C, D, S> for Tm3<K, L, M, R>
where
    C: Ctx<D, S>,
    K: Kind<3>,
    L: LocalTerm<C, D, S>,
    M: LocalTerm<C, D, S>,
    R: LocalTerm<C, D, S>,
{
    const RELOCATABLE: bool = L::RELOCATABLE && M::RELOCATABLE && R::RELOCATABLE;

    fn relocatable(&self) -> bool {
        self.1.relocatable() && self.2.relocatable() && self.3.relocatable()
    }
}

impl<D, CC, T, C, S> TermSealed<C, D, S> for Close1<CC, T>
where
    C: Ctx<D, S>,
    CC: Ctx<D, S>,
    T: TermSealed<C, D, S>,
{
}

impl<D, CC, T, C, S> LocalTerm<C, D, S> for Close1<CC, T>
where
    C: Ctx<D, S>,
    CC: Ctx<D, S>,
    T: LocalTerm<C, D, S>,
{
    const RELOCATABLE: bool = T::RELOCATABLE;

    fn relocatable(&self) -> bool {
        self.tm.relocatable()
    }
}

impl<D, C, L, R, S> TermSealed<C, D, S> for Subst1<L, R>
where
    C: Ctx<D, S>,
    L: TermSealed<C, D, S>,
    R: TermSealed<C, D, S>,
{
}

impl<D, C, L, R, S> LocalTerm<C, D, S> for Subst1<L, R>
where
    C: Ctx<D, S>,
    L: LocalTerm<C, D, S>,
    R: LocalTerm<C, D, S>,
{
    const RELOCATABLE: bool = L::RELOCATABLE && R::RELOCATABLE;

    fn relocatable(&self) -> bool {
        self.bound.relocatable() && self.body.relocatable()
    }
}

/// A term in the datastore
///
/// Unlike a local term, this may be interpreted without a context ID
pub trait Term<D, S = KernelId>: LocalTerm<(), D, S> {}

impl<D, T, S> Term<D, S> for T where T: LocalTerm<(), D, S> {}

/// A global term
///
/// Unlike a (local) term, this may be interpreted without a context ID _or_ session ID
pub trait GlobalTerm<D>: LocalTerm<(), D, ()> {}

impl<D, T> GlobalTerm<D> for T where T: LocalTerm<(), D, ()> {}

pub trait Segment<D: TermIndex, S = KernelId>: Ctx<D, S> {
    fn segment_id(&self, db: &D) -> CtxId<D>;
}

impl<D> Segment<D> for CtxId<D>
where
    D: TermIndex,
{
    fn segment_id(&self, _db: &D) -> CtxId<D> {
        *self
    }
}

pub trait GetSubterms<C, D: TermIndex, S = KernelId> {
    type IxSubterms;

    type ValSubterms;

    fn get_subterms_in(&self, ctx: C, db: &D) -> Option<Self::IxSubterms>;

    fn cons_subterms_in(&self, ctx: C, db: &mut D) -> Self::IxSubterms;

    fn get_subterms_val(&self, ctx: C, db: &D) -> Option<Self::ValSubterms>;

    fn cons_subterms_val(&self, ctx: C, db: &mut D) -> Self::ValSubterms;
}

pub trait GetTerm<C, D: TermIndex, S = KernelId>: LocalTerm<C, D, S> {
    fn get_in(&self, ctx: C, db: &D) -> Option<Ix<D>>;

    fn cons_in(&self, ctx: C, db: &mut D) -> Ix<D>;

    fn get_val(&self, ctx: C, db: &D) -> Option<TmId<D>>;

    fn cons_val(&self, ctx: C, db: &mut D) -> TmId<D>;
}

impl<C, D> GetTerm<C, D> for Ix<D>
where
    D: TermIndex + ReadLocalTerm<D>,
    C: Segment<D>,
{
    fn get_in(&self, _ctx: C, _db: &D) -> Option<Ix<D>> {
        Some(*self)
    }

    fn cons_in(&self, _ctx: C, _db: &mut D) -> Ix<D> {
        *self
    }

    fn get_val(&self, ctx: C, db: &D) -> Option<TmId<D>> {
        let ctx = ctx.segment_id(db);
        Some(db.val(ctx, *self))
    }

    fn cons_val(&self, ctx: C, db: &mut D) -> TmId<D> {
        let ctx = ctx.segment_id(db);
        db.val(ctx, *self)
    }
}

impl<D> GetTerm<CtxId<D>, D> for TmId<D>
where
    D: TermIndex + ReadLocalTerm<D> + WriteLocalTerm<D>,
{
    fn get_in(&self, ctx: CtxId<D>, db: &D) -> Option<Ix<D>> {
        db.lookup_import(ctx, *self)
    }

    fn cons_in(&self, ctx: CtxId<D>, db: &mut D) -> Ix<D> {
        db.import(ctx, *self)
    }

    fn get_val(&self, _ctx: CtxId<D>, db: &D) -> Option<TmId<D>> {
        Some(db.val(self.ctx, self.ix))
    }

    fn cons_val(&self, _ctx: CtxId<D>, db: &mut D) -> TmId<D> {
        db.val(self.ctx, self.ix)
    }
}

impl<C, T, I, X, D, S> GetSubterms<C, D, S> for Node<C, T, I, X>
where
    D: TermIndex,
    C: Segment<D, S> + Copy,
    T: GetTerm<C, D, S>,
    I: GetTerm<C, D, S>,
    X: GetTerm<C, D, S>,
{
    type IxSubterms = NodeIx<D>;

    type ValSubterms = NodeTm<D>;

    fn get_subterms_in(&self, ctx: C, db: &D) -> Option<Self::IxSubterms> {
        self.as_ref()
            .try_map(
                |ctx| Ok(ctx.segment_id(db)),
                |tm| tm.get_in(ctx, db).ok_or(()),
                |qt| qt.get_val(ctx, db).ok_or(()),
                |syn| syn.get_in(ctx, db).ok_or(()),
            )
            .ok()
    }

    fn cons_subterms_in(&self, _ctx: C, _db: &mut D) -> Self::IxSubterms {
        todo!()
        // self.as_ref().map(
        //     |ctx| ctx.segment_id(db),
        //     |tm| tm.cons_in(ctx, db),
        //     |qt| qt.cons_val(ctx, db),
        //     |syn| syn.cons_in(ctx, db),
        // )
    }

    fn get_subterms_val(&self, ctx: C, db: &D) -> Option<Self::ValSubterms> {
        self.as_ref()
            .try_map(
                |ctx| Ok(ctx.segment_id(db)),
                |tm| tm.get_val(ctx, db).ok_or(()),
                |qt| qt.get_val(ctx, db).ok_or(()),
                |syn| syn.get_val(ctx, db).ok_or(()),
            )
            .ok()
    }

    fn cons_subterms_val(&self, _ctx: C, _db: &mut D) -> Self::ValSubterms {
        todo!()
    }
}

// impl<C, T, I, X, D, S> GetTerm<C, D, S> for Node<C, T, I, X>
// where
//     D: TermIndex,
//     C: Ctx<D, S>,
//     T: GetTerm<C, D, S>,
//     I: GetTerm<C, D, S>,
//     X: GetTerm<C, D, S>,
// {
//     fn get_in(&self, ctx: C, db: &D) -> Option<Ix<D>> {
//         todo!()
//     }

//     fn cons_in(&self, ctx: C, db: &mut D) -> Ix<D> {
//         todo!()
//     }

//     fn get_val(&self, ctx: C, db: &D) -> Option<TmId<D>> {
//         todo!()
//     }

//     fn cons_val(&self, ctx: C, db: &mut D) -> TmId<D> {
//         todo!()
//     }
// }
