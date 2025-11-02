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

pub mod api;
pub mod data;
pub mod fact;
pub mod rules;
pub mod store;

pub use crate::api::derive::DeriveTrusted;
pub use crate::api::generic::*;
pub use crate::api::store::{
    ReadCtx, ReadCtxFacts, ReadCtxRel, ReadFacts, ReadTerm, ReadTermDb, ReadTermFacts,
    ReadTermStore, WriteTerm,
};

pub use crate::fact::{
    IS_CONTR, IS_EMPTY, IS_FALSE, IS_INHAB, IS_PROP, IS_SCOPED, IS_TRUE, IS_TY, IS_UNIV, IS_WF,
    IS_WF_EMP, Pred1,
};

#[doc(inline)]
pub use crate::store::{CtxId, Node, TermDb, TermId, ValId};

#[doc(inline)]
pub use crate::data::term::{Bv, Fv, ULvl};

pub type Kernel = crate::rules::Kernel<TermDb>;

impl Kernel {
    /// Construct a new, empty kernel
    pub fn new() -> Kernel {
        Kernel::default()
    }
}
