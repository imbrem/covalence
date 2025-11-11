use crate::data::term::{Close1, Fv, Kind, Node, Subst1, Tm1, Tm2, Tm3, TmIn};
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

pub type NodeTm<D> = Node<CtxId<D>, TmId<D>>;

pub type FvId<D> = Fv<CtxId<D>>;

mod term_sealed {
    pub trait CtxSealed<D> {}

    pub trait TermSealed<C, D> {}
}

use term_sealed::{CtxSealed, TermSealed};

/// A context in the datastore
pub trait Ctx<D>: CtxSealed<D> {}

impl<D> CtxSealed<D> for () {}

impl<D> Ctx<D> for () {}

impl<D: TermIndex> CtxSealed<D> for CtxId<D> {}

impl<D: TermIndex> Ctx<D> for CtxId<D> {}

/// A local term in the datastore
///
/// A _local_ term can be interpreted as a term given a context ID
pub trait LocalTerm<C, D>: TermSealed<C, D> {
    /// Whether this term type can always be relocated
    const RELOCATABLE: bool;

    /// Whether this term can be relocated
    fn relocatable(&self) -> bool {
        Self::RELOCATABLE
    }
}

impl<D: TermIndex> TermSealed<CtxId<D>, D> for Ix<D> {}

impl<D: TermIndex> LocalTerm<CtxId<D>, D> for Ix<D> {
    const RELOCATABLE: bool = false;
}

impl<D, C, T> TermSealed<C, D> for &T
where
    C: Ctx<D>,
    T: TermSealed<C, D>,
{
}

impl<D, C, T> LocalTerm<C, D> for &T
where
    C: Ctx<D>,
    T: LocalTerm<C, D>,
{
    const RELOCATABLE: bool = T::RELOCATABLE;

    fn relocatable(&self) -> bool {
        T::relocatable(*self)
    }
}

impl<D, C, T, CO> TermSealed<CO, D> for TmIn<C, T>
where
    C: Ctx<D>,
    T: LocalTerm<C, D>,
    CO: Ctx<D>,
{
}

impl<D, C, T, CO> LocalTerm<CO, D> for TmIn<C, T>
where
    C: Ctx<D>,
    T: LocalTerm<C, D>,
    CO: Ctx<D>,
{
    const RELOCATABLE: bool = true;
}

impl<D, C, T, I> TermSealed<C, D> for Node<C, T, I>
where
    C: Ctx<D>,
    T: TermSealed<C, D>,
    I: TermSealed<C, D>,
{
}

impl<D, C, T, I> LocalTerm<C, D> for Node<C, T, I>
where
    C: Ctx<D>,
    T: LocalTerm<C, D>,
    I: LocalTerm<C, D>,
{
    const RELOCATABLE: bool = T::RELOCATABLE && I::RELOCATABLE;

    fn relocatable(&self) -> bool {
        match self {
            Node::Quote(tm) => tm.relocatable(),
            Node::Close1(close) => close.relocatable(),
            this => this.children().iter().all(|tm| tm.relocatable()),
        }
    }
}

impl<D, C> TermSealed<C, D> for Fv<C> where C: Ctx<D> {}

impl<D, C> LocalTerm<C, D> for Fv<C>
where
    C: Ctx<D>,
{
    const RELOCATABLE: bool = true;
}

impl<D, C, K, T> TermSealed<C, D> for Tm1<K, T>
where
    C: Ctx<D>,
    K: Kind<1>,
    T: TermSealed<C, D>,
{
}

impl<D, C, K, T> LocalTerm<C, D> for Tm1<K, T>
where
    C: Ctx<D>,
    K: Kind<1>,
    T: LocalTerm<C, D>,
{
    const RELOCATABLE: bool = T::RELOCATABLE;

    fn relocatable(&self) -> bool {
        self.1.relocatable()
    }
}

impl<D, C, K, L, R> TermSealed<C, D> for Tm2<K, L, R>
where
    C: Ctx<D>,
    K: Kind<2>,
    L: TermSealed<C, D>,
    R: TermSealed<C, D>,
{
}

impl<D, C, K, L, R> LocalTerm<C, D> for Tm2<K, L, R>
where
    C: Ctx<D>,
    K: Kind<2>,
    L: LocalTerm<C, D>,
    R: LocalTerm<C, D>,
{
    const RELOCATABLE: bool = L::RELOCATABLE && R::RELOCATABLE;

    fn relocatable(&self) -> bool {
        self.1.relocatable() && self.2.relocatable()
    }
}

impl<D, C, K, L, M, R> TermSealed<C, D> for Tm3<K, L, M, R>
where
    C: Ctx<D>,
    K: Kind<3>,
    L: TermSealed<C, D>,
    M: TermSealed<C, D>,
    R: TermSealed<C, D>,
{
}

impl<D, C, K, L, M, R> LocalTerm<C, D> for Tm3<K, L, M, R>
where
    C: Ctx<D>,
    K: Kind<3>,
    L: LocalTerm<C, D>,
    M: LocalTerm<C, D>,
    R: LocalTerm<C, D>,
{
    const RELOCATABLE: bool = L::RELOCATABLE && M::RELOCATABLE && R::RELOCATABLE;

    fn relocatable(&self) -> bool {
        self.1.relocatable() && self.2.relocatable() && self.3.relocatable()
    }
}

impl<D, CC, T, C> TermSealed<C, D> for Close1<CC, T>
where
    C: Ctx<D>,
    CC: Ctx<D>,
    T: TermSealed<C, D>,
{
}

impl<D, CC, T, C> LocalTerm<C, D> for Close1<CC, T>
where
    C: Ctx<D>,
    CC: Ctx<D>,
    T: LocalTerm<C, D>,
{
    const RELOCATABLE: bool = T::RELOCATABLE;

    fn relocatable(&self) -> bool {
        self.tm.relocatable()
    }
}

impl<D, C, L, R> TermSealed<C, D> for Subst1<L, R>
where
    C: Ctx<D>,
    L: TermSealed<C, D>,
    R: TermSealed<C, D>,
{
}

impl<D, C, L, R> LocalTerm<C, D> for Subst1<L, R>
where
    C: Ctx<D>,
    L: LocalTerm<C, D>,
    R: LocalTerm<C, D>,
{
    const RELOCATABLE: bool = L::RELOCATABLE && R::RELOCATABLE;

    fn relocatable(&self) -> bool {
        self.bound.relocatable() && self.body.relocatable()
    }
}

/// A term in the datastore
///
/// Unlike a local term, this may be interpreted without a context ID
pub trait Term<D>: LocalTerm<(), D> {}

impl<D, T: LocalTerm<(), D>> Term<D> for T {}
