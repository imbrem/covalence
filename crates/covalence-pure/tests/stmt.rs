//! The abstract statement surface — `GetCtx`/`GetProp`/`IntoParts` views,
//! including the no-copy forwarding through `&` and `Arc`, and the `P ⟺ Q`
//! multi-view (one carrier exposing its prop as two types).

use std::sync::Arc;

use covalence_pure::{GetCtx, GetProp, IntoParts, Stmt};

#[test]
fn views_and_pointer_forwarding() {
    let s = Stmt {
        ctx: 1u32,
        prop: 2u8,
    };
    assert_eq!(*s.get_ctx(), 1u32);
    assert_eq!(*s.get_prop(), 2u8);

    // Read the statement through a shared pointer without copying it.
    let a = Arc::new(s);
    assert_eq!(*a.get_ctx(), 1u32);
    assert_eq!(*a.get_prop(), 2u8);

    // Materialize the canonical `(K, P)` (clones through the Arc).
    let (c, p): (u32, u8) = a.into_parts();
    assert_eq!((c, p), (1, 2));
}

/// A carrier exposing its single prop value as two different view types — the
/// host-level `P ⟺ Q`: one value *is* both a `u8` and a `Wrapped`.
#[derive(Clone, Copy, PartialEq, Debug)]
struct Wrapped(u8);

struct Dual {
    raw: u8,
    wrapped: Wrapped,
}

impl GetCtx<()> for Dual {
    fn get_ctx(&self) -> &() {
        &()
    }
}
impl GetProp<u8> for Dual {
    fn get_prop(&self) -> &u8 {
        &self.raw
    }
}
impl GetProp<Wrapped> for Dual {
    fn get_prop(&self) -> &Wrapped {
        &self.wrapped
    }
}

#[test]
fn one_carrier_two_prop_views() {
    let d = Dual {
        raw: 5,
        wrapped: Wrapped(5),
    };
    let as_u8: &u8 = d.get_prop();
    let as_wrapped: &Wrapped = d.get_prop();
    assert_eq!(*as_u8, 5);
    assert_eq!(*as_wrapped, Wrapped(5));
}

#[test]
fn dyn_capability_object() {
    // A single capability is object-safe, so a `dyn` carrier exposing it works
    // behind a pointer (combining several capabilities into one `dyn` is a
    // user-defined trait — `GetProp`/`GetCtx` are deliberately separate).
    let boxed: Box<dyn GetProp<u8>> = Box::new(Dual {
        raw: 7,
        wrapped: Wrapped(7),
    });
    assert_eq!(*boxed.get_prop(), 7u8);
}

#[test]
fn statement_pointer_wrapping_roundtrips() {
    use covalence_pure::testing::TestCtx;

    let b = TestCtx::axiom(5u32).box_stmt().unbox_stmt();
    assert_eq!(b.into_parts().1, 5);

    let a = TestCtx::axiom(6u32).arc_stmt().unarc_stmt();
    assert_eq!(a.into_parts().1, 6);

    let r = TestCtx::axiom(7u32).rc_stmt().unrc_stmt();
    assert_eq!(r.into_parts().1, 7);

    // Borrow the statement inside an `Arc` without copying it.
    let shared = TestCtx::axiom(8u32).arc_stmt();
    let borrowed = shared.deref_stmt();
    assert_eq!(*borrowed.get_prop(), 8u32);
}
