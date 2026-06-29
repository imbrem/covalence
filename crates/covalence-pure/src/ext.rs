//! Ergonomic **extension traits** over the kernel. `MThm` is defined in
//! `covalence-pure-trusted`, so sugar that adds methods lives here as traits
//! (not inherent impls). Everything here only *composes* public kernel ops — it
//! cannot mint, so it adds nothing to the TCB.

use covalence_pure_trusted::{MThm, TryUnion, Union};

/// Same-context conveniences over any `MThm<K, P>`.
pub trait MThmExt<K, P>: Sized {
    /// Same-context [`MThm::try_zip`]: fallibly merge two same-context theorems,
    /// staying in `K` (no output-context annotation). For type-erased contexts
    /// this is the pointer-equality-or-error union.
    fn try_zip_same<P2>(
        self,
        other: MThm<K, P2>,
    ) -> Result<MThm<K, (P, P2)>, <K as TryUnion<K, K>>::Err>
    where
        K: TryUnion<K, K>;
}

impl<K, P> MThmExt<K, P> for MThm<K, P> {
    fn try_zip_same<P2>(
        self,
        other: MThm<K, P2>,
    ) -> Result<MThm<K, (P, P2)>, <K as TryUnion<K, K>>::Err>
    where
        K: TryUnion<K, K>,
    {
        self.try_zip(other)
    }
}

/// Same-context conveniences over a vector theorem `MThm<K, Vec<T>>`.
pub trait MThmVecExt<K, T>: Sized {
    /// Same-context [`MThm::push`]: append a same-context element, staying in `K`
    /// so it chains. Needs the context to be self-mergeable (trivial for a
    /// stateless / ZST context).
    fn push_same(self, elem: MThm<K, T>) -> MThm<K, Vec<T>>
    where
        K: Union<K, K>;
}

impl<K, T> MThmVecExt<K, T> for MThm<K, Vec<T>> {
    fn push_same(self, elem: MThm<K, T>) -> MThm<K, Vec<T>>
    where
        K: Union<K, K>,
    {
        self.push(elem)
    }
}
