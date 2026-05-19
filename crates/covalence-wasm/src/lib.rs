mod validate;
pub use validate::{compile_wat, wasm_to_wat};

pub mod parse;
pub use parse::{ComponentInfo, ModuleInfo, parse_component, parse_module};

/// Errors from WAT compilation, WASM decompilation, and binary parsing.
#[derive(Debug, thiserror::Error)]
pub enum WasmError {
    #[error("WAT compile error: {0}")]
    Wat(String),
    #[error("WASM decompile error: {0}")]
    Decompile(String),
    #[error("invalid module: {0}")]
    InvalidModule(String),
    #[error("invalid component: {0}")]
    InvalidComponent(String),
}

#[cfg(feature = "runtime")]
pub mod engine;
#[cfg(feature = "runtime")]
pub use engine::{PropError, PropResult, WasmEngine};
// Note: PropResult is the engine-internal type. The public API type is
// `Decision` from `covalence-kernel`. PropResult is kept public for
// direct WasmEngine consumers (e.g. integration tests).

#[cfg(feature = "runtime")]
pub use wasmtime;
