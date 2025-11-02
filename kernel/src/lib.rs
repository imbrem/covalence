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
pub mod rules;
pub mod store;

pub use crate::api::derive::Derive;
pub use crate::api::generic::*;
pub use crate::api::store::{
    ReadCtx, ReadFacts, ReadTerm, ReadTermDb, ReadTermFacts, ReadTermStore, WriteTerm,
};

#[doc(inline)]
pub use crate::store::{CtxId, Node, TermDb, TermId, ValId};

#[doc(inline)]
pub use crate::data::term::{Bv, ULvl};

pub type Kernel = crate::rules::Kernel<TermDb>;

impl Kernel {
    /// Construct a new, empty kernel
    pub fn new() -> Kernel {
        Kernel::default()
    }
}

#[cfg(test)]
mod test {
    use crate::api::error::kernel_error;

    use super::*;

    // #[test]
    // fn derive_unit_to_empty_wf() {
    //     let mut ker = Kernel::default();
    //     let ctx = ker.new_ctx();
    //     assert!(ker.is_root(ctx));
    //     assert!(!ker.is_contr(ctx));
    //     let unit = ker.add(ctx, Node::Unit);
    //     let empty = ker.add(ctx, Node::Empty);
    //     assert_ne!(unit, empty);
    //     let u1 = ker.add(ctx, Node::U(ULvl::SET));
    //     assert!(!ker.has_ty(ctx, unit, u1));
    //     assert!(!ker.has_ty(ctx, empty, u1));
    //     debug_assert!(!ker.is_contr(ctx));
    //     let unit_deriv = ker.derive_unit(ctx, ULvl::SET);
    //     assert_eq!(unit_deriv.ty, u1);
    //     assert_eq!(unit_deriv.tm, unit);
    //     assert!(ker.has_ty(ctx, unit, u1));
    //     let empty_deriv = ker.derive_empty(ctx, ULvl::SET);
    //     assert_eq!(empty_deriv.ty, u1);
    //     assert_eq!(empty_deriv.tm, empty);
    //     assert!(ker.has_ty(ctx, empty, u1));
    //     assert_eq!(
    //         ker.derive_pi(ctx, ULvl::SET, ULvl::PROP, unit, empty, &mut ())
    //             .unwrap_err(),
    //         kernel_error::DERIVE_PI_RES_TY
    //     );
    //     assert_eq!(
    //         ker.derive_pi(ctx, ULvl::PROP, ULvl::PROP, unit, empty, &mut ())
    //             .unwrap_err(),
    //         kernel_error::DERIVE_PI_ARG_TY
    //     );
    //     let empty_deriv = ker.derive_empty(ctx, ULvl::PROP);
    //     let u0 = ker.add(ctx, Node::U(ULvl::PROP));
    //     assert_eq!(empty_deriv.tm, empty);
    //     assert_eq!(empty_deriv.ty, u0);
    //     assert_eq!(
    //         ker.derive_pi(ctx, ULvl::PROP, ULvl::PROP, unit, empty, &mut ())
    //             .unwrap_err(),
    //         kernel_error::DERIVE_PI_ARG_TY
    //     );
    //     let pi_deriv = ker
    //         .derive_pi(ctx, ULvl::SET, ULvl::PROP, unit, empty, &mut ())
    //         .unwrap();
    //     let pi = ker.add(ctx, Node::Pi([unit, empty]));
    //     assert_eq!(pi_deriv.tm, pi);
    //     assert_eq!(pi_deriv.ty, u0);
    //     assert!(ker.has_ty(ctx, pi, u0));
    //     assert!(ker.is_prop(ctx, pi));
    // }
}
