/*!
The base `covalence` kernel, currently implemented using `egg`
*/
pub use crate::derive::{Derive, DeriveExt, ReadFacts, TermStore};

//TODO: add docs
type TermDb = crate::store::EggTermDb;

#[doc(inline)]
pub use crate::store::{CtxId, Node, TermId};

#[doc(inline)]
pub use crate::term::ULvl;

pub type Kernel = crate::trusted::kernel::Kernel<TermDb>;

impl Kernel {
    /// Construct a new, empty kernel
    pub fn new() -> Kernel {
        Kernel::default()
    }
}

#[cfg(test)]
mod test {
    use crate::error::kernel_error;

    use super::*;

    #[test]
    fn derive_unit_to_empty_wf() {
        let mut ker = Kernel::default();
        let ctx = ker.new_ctx();
        assert!(ker.is_root(ctx));
        assert!(!ker.is_contr(ctx));
        assert_eq!(ker.parent(ctx), None);
        let unit = ker.add(ctx, Node::Unit);
        let empty = ker.add(ctx, Node::Empty);
        assert_ne!(unit, empty);
        let u1 = ker.add(ctx, Node::U(ULvl::SET));
        assert!(!ker.has_ty(ctx, unit, u1));
        assert!(!ker.has_ty(ctx, empty, u1));
        debug_assert!(!ker.is_contr(ctx));
        let unit_deriv = ker.derive_unit(ctx, ULvl::SET);
        assert_eq!(unit_deriv.ty, u1);
        assert_eq!(unit_deriv.tm, unit);
        assert!(ker.has_ty(ctx, unit, u1));
        let empty_deriv = ker.derive_empty(ctx, ULvl::SET);
        assert_eq!(empty_deriv.ty, u1);
        assert_eq!(empty_deriv.tm, empty);
        assert!(ker.has_ty(ctx, empty, u1));
        assert_eq!(
            ker.derive_pi(ctx, ULvl::SET, ULvl::SET, ULvl::PROP, unit, empty, &mut ())
                .unwrap_err(),
            kernel_error::DERIVE_PI_IMAX_LE
        );
        assert_eq!(
            ker.derive_pi(ctx, ULvl::SET, ULvl::PROP, ULvl::PROP, unit, empty, &mut ())
                .unwrap_err(),
            kernel_error::DERIVE_PI_RES_TY
        );
        assert_eq!(
            ker.derive_pi(ctx, ULvl::PROP, ULvl::SET, ULvl::PROP, unit, empty, &mut ())
                .unwrap_err(),
            kernel_error::DERIVE_PI_IMAX_LE
        );
        assert_eq!(
            ker.derive_pi(
                ctx,
                ULvl::PROP,
                ULvl::PROP,
                ULvl::PROP,
                unit,
                empty,
                &mut ()
            )
            .unwrap_err(),
            kernel_error::DERIVE_PI_ARG_TY
        );
        let empty_deriv = ker.derive_empty(ctx, ULvl::PROP);
        let u0 = ker.add(ctx, Node::U(ULvl::PROP));
        assert_eq!(empty_deriv.tm, empty);
        assert_eq!(empty_deriv.ty, u0);
        assert_eq!(
            ker.derive_pi(ctx, ULvl::SET, ULvl::SET, ULvl::PROP, unit, empty, &mut ())
                .unwrap_err(),
            kernel_error::DERIVE_PI_IMAX_LE
        );
        assert_eq!(
            ker.derive_pi(ctx, ULvl::PROP, ULvl::SET, ULvl::PROP, unit, empty, &mut ())
                .unwrap_err(),
            kernel_error::DERIVE_PI_IMAX_LE
        );
        assert_eq!(
            ker.derive_pi(
                ctx,
                ULvl::PROP,
                ULvl::PROP,
                ULvl::PROP,
                unit,
                empty,
                &mut ()
            )
            .unwrap_err(),
            kernel_error::DERIVE_PI_ARG_TY
        );
        let pi_deriv = ker
            .derive_pi(ctx, ULvl::SET, ULvl::PROP, ULvl::PROP, unit, empty, &mut ())
            .unwrap();
        let pi = ker.add(ctx, Node::Pi([unit, empty]));
        assert_eq!(pi_deriv.tm, pi);
        assert_eq!(pi_deriv.ty, u0);
        assert!(ker.has_ty(ctx, pi, u0));
        assert!(ker.is_prop(ctx, pi));
    }
}
