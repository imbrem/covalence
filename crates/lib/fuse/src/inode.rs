use std::collections::HashMap;
use std::sync::Mutex;
use std::sync::atomic::{AtomicU64, Ordering};

use covalence_hash::O256;
use covalence_object::DirMode;

/// What a FUSE inode resolves to in our world.
#[derive(Clone, Copy, Debug)]
pub struct InodeEntry {
    pub hash: O256,
    pub mode: DirMode,
    /// File size in bytes, or `None` if not yet realized.
    ///
    /// We defer sizing until a `getattr`/`read` actually needs it so that
    /// `ls` of a deep tree doesn't force a `store.get` for every file just
    /// to learn its length.
    pub size: Option<u64>,
}

/// Inode allocator + bidirectional `u64 ↔ (O256, mode)` map.
///
/// Inodes are sequentially allocated `u64`s starting at 2 (1 is the root,
/// reserved by FUSE). Identical subtrees share an inode via the reverse map.
/// We intentionally do **not** derive inode numbers from `O256` bits —
/// collisions are avoidable when we're the only allocator, and a stable
/// 64-bit space is easier to reason about for tooling like `find -inum`.
pub struct InodeTable {
    next: AtomicU64,
    forward: Mutex<HashMap<u64, InodeEntry>>,
    reverse: Mutex<HashMap<O256, u64>>,
}

pub const ROOT_INO: u64 = 1;

impl InodeTable {
    pub fn new(root_hash: O256, root_mode: DirMode) -> Self {
        let mut forward = HashMap::new();
        forward.insert(
            ROOT_INO,
            InodeEntry {
                hash: root_hash,
                mode: root_mode,
                size: None,
            },
        );
        let mut reverse = HashMap::new();
        reverse.insert(root_hash, ROOT_INO);

        Self {
            next: AtomicU64::new(2),
            forward: Mutex::new(forward),
            reverse: Mutex::new(reverse),
        }
    }

    /// Intern an `(O256, mode)` pair, returning an existing inode if the hash
    /// has been seen before. Sizes are tracked per-inode (not per-hash) so
    /// that two inodes for the same blob share the size cache as a happy
    /// accident on next-realize.
    pub fn intern(&self, hash: O256, mode: DirMode) -> u64 {
        if let Some(&ino) = self.reverse.lock().unwrap().get(&hash) {
            return ino;
        }
        let ino = self.next.fetch_add(1, Ordering::Relaxed);
        self.forward.lock().unwrap().insert(
            ino,
            InodeEntry {
                hash,
                mode,
                size: None,
            },
        );
        self.reverse.lock().unwrap().insert(hash, ino);
        ino
    }

    pub fn get(&self, ino: u64) -> Option<InodeEntry> {
        self.forward.lock().unwrap().get(&ino).copied()
    }

    /// Record a realized file size. Called the first time we touch the blob.
    pub fn set_size(&self, ino: u64, size: u64) {
        if let Some(entry) = self.forward.lock().unwrap().get_mut(&ino) {
            entry.size = Some(size);
        }
    }
}
