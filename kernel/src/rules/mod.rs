use std::ops::Deref;

use crate::api::derive::*;
use crate::api::store::*;
use crate::api::strategy;
use crate::api::strategy::Strategy;
use crate::data::term::{Fv, NodeT, ULvl, Val};

/// Derivation rules for the `covalence` kernel
mod derive;

/// Rules for unfolding substitutions, imports, and closures
mod unfold;

/// The `covalence` kernel
///
/// This type is parametrized by its datastore `D`
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
pub struct Kernel<D>(D);

impl<D> Kernel<D> {
    /// Get an _immutable_ reference to the underlying datastore
    pub fn data(&self) -> &D {
        &self.0
    }
}

impl<D> Deref for Kernel<D> {
    type Target = D;

    fn deref(&self) -> &D {
        &self.0
    }
}

impl<C, T, D: ReadTermDb<C, T>> ReadTermDb<C, T> for Kernel<D> {
    type Reader = D::Reader;

    fn read(&self) -> &Self::Reader {
        self.0.read()
    }
}

impl<D: TermIndex> TermIndex for Kernel<D> {
    type CtxId = D::CtxId;
    type TermId = D::TermId;
}

impl<C, T, D: WriteTerm<C, T>> WriteTerm<C, T> for Kernel<D> {
    fn new_ctx(&mut self) -> C {
        self.0.new_ctx()
    }

    fn with_parent(&mut self, parent: C) -> C {
        self.0.with_parent(parent)
    }

    fn add(&mut self, ctx: C, term: NodeT<C, T>) -> T {
        self.0.add(ctx, term)
    }

    fn import(&mut self, ctx: C, val: Val<C, T>) -> T {
        self.0.import(ctx, val)
    }

    fn var_ty(&mut self, ctx: C, var: Fv<C>) -> T {
        self.0.var_ty(ctx, var)
    }

    fn succ(&mut self, level: ULvl) -> ULvl {
        self.0.succ(level)
    }

    fn umax(&mut self, lhs: ULvl, rhs: ULvl) -> ULvl {
        self.0.umax(lhs, rhs)
    }

    fn imax(&mut self, lhs: ULvl, rhs: ULvl) -> ULvl {
        self.0.imax(lhs, rhs)
    }

    fn propagate_in(&mut self, ctx: C) -> usize {
        self.0.propagate_in(ctx)
    }
}

pub trait KernelAPI<C: Copy, T: Copy + PartialEq>:
    DeriveTrusted<C, T> + Ensure<C, T> + WriteTerm<C, T> + ReadTermDb<C, T>
{
}

impl<K, C: Copy, T: Copy + PartialEq> KernelAPI<C, T> for K where
    K: DeriveTrusted<C, T> + Ensure<C, T> + WriteTerm<C, T> + ReadTermDb<C, T>
{
}
