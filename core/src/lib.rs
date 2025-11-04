/*!
The kernel's trusted code base

This module is further subdivided into three primary components:
- `data`, which contains generic data structures and (trusted) functions for manipulating them
- `api`, which describes the generic API our rules are implemented over, including the API of the
  rules themselves
- `rules`, which implements an LCF-style kernel for `covalence` over an abstract datastore
- `store`, which is a specific, trusted implementation of our datastore API using `egg`
- `kernel`, which instantiates the kernel in `rules` with the datastore
*/

pub use covalence_data as data;
pub use covalence_data::store;

pub mod db;
pub mod fact;
pub mod kernel;
pub mod rule;
pub mod strategy;

pub use crate::rule::ensure::{DeriveTrusted, WriteTrusted};
pub use crate::store::{
    ReadCtxFacts, ReadCtxRel, ReadFacts, ReadQuantFacts, ReadTermDb, ReadTermFacts, ReadTermIndex,
    ReadTermStore, WriteTermIndex, ReadCtx,
};
pub use covalence_data::univ::{ReadUniv, WriteUniv};

pub use covalence_data::fact::{
    IS_CONTR, IS_EMPTY, IS_FF, IS_INHAB, IS_PROP, IS_SCOPED, IS_TT, IS_TY, IS_UNIV, IS_WF, Pred1,
};

#[doc(inline)]
pub use crate::db::{CtxId, FvId, NodeIx, TermDb, TermId, ValId};

#[doc(inline)]
pub use covalence_data::term::{Bv, Fv, ULvl};

pub type Kernel = crate::rule::Kernel<TermDb>;

impl Kernel {
    /// Construct a new, empty kernel
    pub fn new() -> Kernel {
        Kernel::default()
    }
}
