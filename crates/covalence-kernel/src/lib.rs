mod traits;
pub use traits::{AsyncBackend, BackendInfo, Decision, KernelError, SyncBackend};

#[cfg(feature = "engine")]
mod kernel;
#[cfg(feature = "engine")]
pub use kernel::Kernel;

#[cfg(feature = "engine")]
pub use covalence_wasm::{PropError, WasmEngine};
