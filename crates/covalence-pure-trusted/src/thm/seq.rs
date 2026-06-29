//! Sequence props as **N-ary conjunction**: `[T; N]`, `Vec<T>`, and `&[T]` read
//! as "every element holds in `K`". [`MThm::unpack`] projects each element (the
//! collection analog of [`MThm::and_elim`]); [`MThm::empty_vec`] / [`MThm::push`]
//! build a `Vec` theorem (the analog of [`MThm::zip`]).
//!
//! These are **neutral** — their meaning needs nothing trusted about `T`.
//! Ordered/hashed containers (`BTreeSet`, `HashSet`) are deliberately omitted:
//! their structure (dedup, membership, set-equality) trusts `T: Ord` /
//! `T: Hash + Eq`, so they belong with the equality/ordering trust layer, not
//! the neutral floor. (Even there, only *those* operations trust `T`'s impls —
//! unpacking a set stays sound.)

use super::{MThm, Stmt, Union};

/// `∧`-elimination over a fixed-size array: every element holds in `K`.
impl<K: Clone, T, const N: usize> MThm<K, [T; N]> {
    pub fn unpack(self) -> [MThm<K, T>; N] {
        let Stmt { ctx, prop } = self.0;
        prop.map(|t| {
            MThm::new(Stmt {
                ctx: ctx.clone(),
                prop: t,
            })
        })
    }
}

impl<K, T> MThm<K, Vec<T>> {
    /// The empty conjunction: a vector theorem asserting nothing (trivially true,
    /// like [`MThm::trivial`]).
    pub fn empty_vec(ctx: K) -> MThm<K, Vec<T>> {
        MThm::new(Stmt {
            ctx,
            prop: Vec::new(),
        })
    }

    /// Append an element, [`Union`]-ing the two context values — the N-ary analog
    /// of [`MThm::zip`]. For the common same-context case (which chains in `K`),
    /// use the convenience `push_same` (the `MThmVecExt` trait in `covalence-pure`).
    pub fn push<K2, U>(self, elem: MThm<K2, T>) -> MThm<U, Vec<T>>
    where
        U: Union<K, K2>,
    {
        let Stmt { ctx, mut prop } = self.0;
        let Stmt { ctx: ctx2, prop: t } = elem.0;
        prop.push(t);
        MThm::new(Stmt {
            ctx: U::union(ctx, ctx2),
            prop,
        })
    }
}

/// `∧`-elimination over a vector: every element holds in `K`.
impl<K: Clone, T> MThm<K, Vec<T>> {
    pub fn unpack(self) -> Vec<MThm<K, T>> {
        let Stmt { ctx, prop } = self.0;
        prop.into_iter()
            .map(|t| {
                MThm::new(Stmt {
                    ctx: ctx.clone(),
                    prop: t,
                })
            })
            .collect()
    }
}

/// `∧`-elimination over a slice: every element holds in `K` (clones each).
impl<K: Clone, T: Clone> MThm<K, &[T]> {
    pub fn unpack(self) -> Vec<MThm<K, T>> {
        let Stmt { ctx, prop } = self.0;
        prop.iter()
            .map(|t| {
                MThm::new(Stmt {
                    ctx: ctx.clone(),
                    prop: t.clone(),
                })
            })
            .collect()
    }
}
