use std::{
    fmt::{self, Debug},
    num::NonZeroU64,
    sync::atomic::{self, AtomicU64},
};

static NEXT_KERNEL_ID: AtomicU64 = AtomicU64::new(0);

#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct KernelId(NonZeroU64);

impl Debug for KernelId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#k{}", self.0)
    }
}

impl Default for KernelId {
    fn default() -> Self {
        let id = NEXT_KERNEL_ID
            .fetch_add(1, atomic::Ordering::SeqCst)
            .checked_add(1)
            .expect("exhausted kernel IDs");
        KernelId(NonZeroU64::new(id).unwrap())
    }
}
