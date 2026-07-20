//! Small typed resource tables for proof-free runtime backends.
//!
//! This is deliberately storage mechanics rather than Lisp semantics. A
//! [`ResourceArena`] gives related tables one identity; [`Resource`] carries
//! that identity plus a typed index; [`ResourceTable`] performs all
//! foreign/stale-handle checks. CEK and concatenative runtimes can therefore
//! share the WIT-like handle discipline without sharing their value domains.

use core::fmt::{Debug, Display, Formatter};
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use std::cell::RefCell;
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};

static NEXT_ARENA_ID: AtomicUsize = AtomicUsize::new(1);

#[derive(Debug)]
struct ArenaIdentity {
    id: usize,
}

/// Identity shared by a family of typed resource tables.
#[derive(Clone, Debug)]
pub struct ResourceArena(Rc<ArenaIdentity>);

impl Default for ResourceArena {
    fn default() -> Self {
        Self::new()
    }
}

impl ResourceArena {
    pub fn new() -> Self {
        Self(Rc::new(ArenaIdentity {
            id: NEXT_ARENA_ID.fetch_add(1, Ordering::Relaxed),
        }))
    }

    pub fn table<K, T>(&self, resource: &'static str) -> ResourceTable<K, T> {
        ResourceTable {
            identity: Rc::clone(&self.0),
            resource,
            entries: Rc::new(RefCell::new(Vec::new())),
            _kind: PhantomData,
        }
    }
}

/// Opaque typed reference to one table entry.
pub struct Resource<K> {
    arena: usize,
    index: usize,
    _kind: PhantomData<fn() -> K>,
}

impl<K> Resource<K> {
    pub const fn arena(&self) -> usize {
        self.arena
    }

    pub const fn index(&self) -> usize {
        self.index
    }
}

impl<K> Clone for Resource<K> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<K> Copy for Resource<K> {}

impl<K> PartialEq for Resource<K> {
    fn eq(&self, other: &Self) -> bool {
        self.arena == other.arena && self.index == other.index
    }
}

impl<K> Eq for Resource<K> {}

impl<K> Hash for Resource<K> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.arena.hash(state);
        self.index.hash(state);
    }
}

impl<K> Debug for Resource<K> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "Resource({}:{})", self.arena, self.index)
    }
}

/// Invalid typed resource lookup.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResourceError {
    Foreign {
        resource: &'static str,
        expected_arena: usize,
        actual_arena: usize,
    },
    Stale {
        resource: &'static str,
        index: usize,
    },
}

impl Display for ResourceError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Foreign {
                resource,
                expected_arena,
                actual_arena,
            } => write!(
                f,
                "{resource} handle belongs to arena {actual_arena}, expected {expected_arena}"
            ),
            Self::Stale { resource, index } => {
                write!(f, "stale {resource} handle at index {index}")
            }
        }
    }
}

impl core::error::Error for ResourceError {}

/// Cloneable typed table belonging to a [`ResourceArena`].
pub struct ResourceTable<K, T> {
    identity: Rc<ArenaIdentity>,
    resource: &'static str,
    entries: Rc<RefCell<Vec<T>>>,
    _kind: PhantomData<fn() -> K>,
}

impl<K, T> Clone for ResourceTable<K, T> {
    fn clone(&self) -> Self {
        Self {
            identity: Rc::clone(&self.identity),
            resource: self.resource,
            entries: Rc::clone(&self.entries),
            _kind: PhantomData,
        }
    }
}

impl<K, T> Debug for ResourceTable<K, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("ResourceTable")
            .field("arena", &self.identity.id)
            .field("resource", &self.resource)
            .field("len", &self.entries.borrow().len())
            .finish()
    }
}

impl<K, T> ResourceTable<K, T> {
    pub fn insert(&self, value: T) -> Resource<K> {
        let mut entries = self.entries.borrow_mut();
        let handle = Resource {
            arena: self.identity.id,
            index: entries.len(),
            _kind: PhantomData,
        };
        entries.push(value);
        handle
    }

    fn checked_index(&self, handle: Resource<K>) -> Result<usize, ResourceError> {
        if handle.arena != self.identity.id {
            return Err(ResourceError::Foreign {
                resource: self.resource,
                expected_arena: self.identity.id,
                actual_arena: handle.arena,
            });
        }
        if handle.index >= self.entries.borrow().len() {
            return Err(ResourceError::Stale {
                resource: self.resource,
                index: handle.index,
            });
        }
        Ok(handle.index)
    }

    pub fn get_cloned(&self, handle: Resource<K>) -> Result<T, ResourceError>
    where
        T: Clone,
    {
        let index = self.checked_index(handle)?;
        Ok(self.entries.borrow()[index].clone())
    }

    pub fn contains(&self, handle: Resource<K>) -> Result<(), ResourceError> {
        self.checked_index(handle).map(|_| ())
    }

    pub fn update<U>(
        &self,
        handle: Resource<K>,
        update: impl FnOnce(&mut T) -> U,
    ) -> Result<U, ResourceError> {
        let index = self.checked_index(handle)?;
        Ok(update(&mut self.entries.borrow_mut()[index]))
    }

    pub fn len(&self) -> usize {
        self.entries.borrow().len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.borrow().is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    enum Number {}

    #[test]
    fn tables_reject_foreign_handles_and_share_updates_across_clones() {
        let first = ResourceArena::new().table::<Number, usize>("number");
        let second = ResourceArena::new().table::<Number, usize>("number");
        let handle = first.insert(41);
        let clone = first.clone();

        clone.update(handle, |value| *value += 1).unwrap();
        assert_eq!(first.get_cloned(handle).unwrap(), 42);
        assert!(matches!(
            second.get_cloned(handle),
            Err(ResourceError::Foreign { .. })
        ));
    }
}
