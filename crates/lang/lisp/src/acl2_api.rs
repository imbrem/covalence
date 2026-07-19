//! Theorem-neutral capabilities for an ordered ACL2 read-time world.
//!
//! These traits sit above generic Lisp syntax and below book importing and
//! checked NativeHol replay. Handling an event here means only that its
//! read-time effects were modeled; it never admits a logical definition or
//! produces theorem authority.

/// Whether an ordered ACL2 world recognized a surface event.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WorldEventStatus {
    /// The event's read-time effects were processed.
    Handled,
    /// The event is outside this world's theorem-neutral responsibility.
    Unhandled,
}

impl WorldEventStatus {
    /// Whether the backend recognized and processed the event.
    pub const fn is_handled(self) -> bool {
        matches!(self, Self::Handled)
    }
}

/// Read-only access to values established by preceding ACL2 world events.
///
/// The associated value carrier deliberately leaves storage and evaluation
/// representation to the backend.
pub trait Acl2WorldView {
    type Value;

    fn constant(&self, name: &str) -> Option<&Self::Value>;
}

/// Ordered processing of theorem-neutral ACL2 world events.
///
/// A successful [`WorldEventStatus::Handled`] result carries no proof,
/// admission, or kernel authority. Logical events must remain
/// [`WorldEventStatus::Unhandled`] and proceed through a separate checked
/// replay capability.
pub trait Acl2EventWorld: Acl2WorldView {
    type Form: ?Sized;
    type Error;

    fn process_world_event(&mut self, event: &Self::Form) -> Result<WorldEventStatus, Self::Error>;
}

// TODO(cov:acl2.api.read-time-capability-split, major): Extract separate
// macro-expansion, sharp-dot/make-event evaluation, and generated-data
// mutation capabilities, then inject the composed backend into the book
// pipeline without coupling it to NativeHol checked replay.

#[cfg(test)]
mod tests {
    use covalence_sexp::SExpr;
    use covalence_types::Int;

    use super::{Acl2EventWorld, Acl2WorldView, WorldEventStatus};
    use crate::reader::read_book;
    use crate::world::{Acl2World, WorldError, WorldValue};

    fn process<W>(world: &mut W, source: &str) -> Result<WorldEventStatus, W::Error>
    where
        W: Acl2EventWorld<Form = SExpr, Value = WorldValue>,
    {
        let event = read_book(source)
            .expect("test event parses")
            .into_iter()
            .next()
            .expect("one test event");
        world.process_world_event(&event)
    }

    #[test]
    fn concrete_adapter_preserves_ordered_world_state() {
        let mut world = Acl2World::new();

        assert_eq!(
            process(&mut world, "(defconst *base* 4)").unwrap(),
            WorldEventStatus::Handled
        );
        assert_eq!(
            process(&mut world, "(defconst *next* (+ *base* 1))").unwrap(),
            WorldEventStatus::Handled
        );
        assert_eq!(
            Acl2WorldView::constant(&world, "*base*"),
            Some(&WorldValue::Int(Int::from(4)))
        );
        assert_eq!(
            Acl2WorldView::constant(&world, "*next*"),
            Some(&WorldValue::Int(Int::from(5)))
        );
    }

    #[test]
    fn logical_events_are_unhandled_and_failed_events_do_not_bind() {
        let mut world = Acl2World::new();

        assert_eq!(
            process(&mut world, "(defthm bogus nil)").unwrap(),
            WorldEventStatus::Unhandled
        );
        assert_eq!(
            process(&mut world, "(defconst *bad* missing)"),
            Err(WorldError::Unbound("missing".into()))
        );
        assert_eq!(Acl2WorldView::constant(&world, "*bad*"), None);
    }
}
