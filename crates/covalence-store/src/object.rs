//! Typed object storage: [`ObjectKind`], [`Object`] trait, concrete types, and [`ObjectStore`].

use crate::StoreError;

/// The kind of a stored object.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ObjectKind {
    Blob,
    Tree,
    Commit,
    Tag,
}

/// A typed store object with a statically-known kind.
pub trait Object: Send + Sync + Sized {
    /// The kind of this object type.
    const KIND: ObjectKind;

    /// Access raw data bytes.
    fn data(&self) -> &[u8];

    /// Wrap raw bytes into this type.
    fn from_data(data: Vec<u8>) -> Self;

    /// Consume into raw bytes.
    fn into_data(self) -> Vec<u8>;
}

/// Raw binary blob.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Blob(pub Vec<u8>);

/// Raw tree data (serialized directory listing).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tree(pub Vec<u8>);

/// Raw commit object (header + message).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Commit(pub Vec<u8>);

/// Raw annotated tag object.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tag(pub Vec<u8>);

macro_rules! impl_object {
    ($ty:ident, $kind:expr) => {
        impl Object for $ty {
            const KIND: ObjectKind = $kind;
            fn data(&self) -> &[u8] {
                &self.0
            }
            fn from_data(data: Vec<u8>) -> Self {
                Self(data)
            }
            fn into_data(self) -> Vec<u8> {
                self.0
            }
        }
    };
}

impl_object!(Blob, ObjectKind::Blob);
impl_object!(Tree, ObjectKind::Tree);
impl_object!(Commit, ObjectKind::Commit);
impl_object!(Tag, ObjectKind::Tag);

/// Dynamically-typed object (any kind).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AnyObject {
    pub kind: ObjectKind,
    pub data: Vec<u8>,
}

/// A content-addressed store that preserves object type information.
///
/// Generic over key type `K` and typed object `T`.
/// Type checking happens on read: if the stored kind doesn't match `T::KIND`,
/// returns `Err(StoreError::KindMismatch)`.
pub trait ObjectStore<K, T: Object>: Send + Sync {
    /// Retrieve a typed object by key.
    /// Returns `Ok(None)` if not found, `Err(KindMismatch)` if wrong type.
    fn get(&self, key: &K) -> Result<Option<T>, StoreError>;

    /// Hash and store a typed object, returning its content key.
    fn insert(&self, obj: &T) -> Result<K, StoreError>;

    /// Store at a specific key (verifies hash match).
    fn put(&self, key: K, obj: &T) -> Result<(), StoreError>;

    /// Check if a key exists (any type).
    fn contains(&self, key: &K) -> bool;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn blob_object_impl() {
        let data = b"hello world".to_vec();
        let blob = Blob::from_data(data.clone());
        assert_eq!(Blob::KIND, ObjectKind::Blob);
        assert_eq!(blob.data(), b"hello world");
        assert_eq!(blob.into_data(), data);
    }

    #[test]
    fn tree_object_impl() {
        let data = vec![1, 2, 3];
        let tree = Tree::from_data(data.clone());
        assert_eq!(Tree::KIND, ObjectKind::Tree);
        assert_eq!(tree.data(), &[1, 2, 3]);
        assert_eq!(tree.into_data(), data);
    }

    #[test]
    fn commit_object_impl() {
        let data = b"commit data".to_vec();
        let commit = Commit::from_data(data.clone());
        assert_eq!(Commit::KIND, ObjectKind::Commit);
        assert_eq!(commit.data(), b"commit data");
        assert_eq!(commit.into_data(), data);
    }

    #[test]
    fn tag_object_impl() {
        let data = b"tag data".to_vec();
        let tag = Tag::from_data(data.clone());
        assert_eq!(Tag::KIND, ObjectKind::Tag);
        assert_eq!(tag.data(), b"tag data");
        assert_eq!(tag.into_data(), data);
    }

    #[test]
    fn any_object_construction() {
        let obj = AnyObject {
            kind: ObjectKind::Tree,
            data: vec![10, 20, 30],
        };
        assert_eq!(obj.kind, ObjectKind::Tree);
        assert_eq!(obj.data, vec![10, 20, 30]);
    }
}
